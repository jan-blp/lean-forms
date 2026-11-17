module

public import Forms.Model.Basic
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.Meta
public meta import Lean.PrettyPrinter.Delaborator

public meta section
namespace Forms.Model.Deriving
open Lean Meta Elab Command

private abbrev TermSyntax := TSyntax `term
private abbrev Alternative := TSyntax ``Parser.Term.matchAltExpr

private structure FieldInfo where
  name : Name
  binder : Name
  type : Expr
  proof : Bool

private structure Constructor where
  name : Name
  fields : Array FieldInfo
  context : LocalContext
  instances : LocalInstances

private def Constructor.data (ctor : Constructor) := ctor.fields.filter (! ·.proof)
private def Constructor.proofs (ctor : Constructor) := ctor.fields.filter (·.proof)
private def ident (name : Name) : Ident := mkIdent name
private def global (name : Name) : Ident := mkIdent (`_root_ ++ name)
private def fresh (name : Name) : CommandElabM Ident := return ident (← liftCoreM <| mkFreshUserName name)

private def emit (command : TSyntax `command) : CommandElabM Unit := do
  let previous := (← get).messages.reportedPlusUnreported.size
  elabCommand command
  let messages := (← get).messages.reportedPlusUnreported.toList.drop previous
  if let some error := messages.find? (·.severity matches .error) then
    throwError "{error.data}"

private def emitting
  (context : MessageData)
  (action : CommandElabM Unit)
  : CommandElabM Unit := do
  try action
  catch error => throwError "{context}: {error.toMessageData}"

/-- Emits `command` in `name`'s namespace, so its auto-named instances stay unique across modules. -/
private def emitIn
  (name : Name)
  (command : TSyntax `command)
  : CommandElabM Unit :=
  withScope (fun scope => { scope with currNamespace := name }) (emit command)

private partial def checkOptionalJson (type : Expr) : MetaM Unit := do
  let type ← whnf type
  if type.isAppOf ``Option then
    let payload ← whnf type.getAppArgs[0]!
    if payload.isAppOf ``Option then
      throwError "nested Option fields lose presence in JSON; wrap the inner option in a structure"
    checkOptionalJson payload
  else if type.isAppOf ``List then
    checkOptionalJson type.getAppArgs[0]!

private def inspect (name : Name) : MetaM (Bool × Array Constructor) := do
  if isPrivateName name then
    throwError "the model must be public"
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do
    throwError "the type must be monomorphic, without parameters or indices"
  unless info.all.length == 1 && !info.isRec do
    throwError "recursive or mutually recursive types are not supported"
  if info.ctors.isEmpty then throwError "the type needs at least one constructor"
  let record := isStructure (← getEnv) name
  if record && !(getStructureParentInfo (← getEnv) name).isEmpty then
    throwError "structure inheritance is not supported yet"
  let ctors ← info.ctors.toArray.mapM fun ctorName => do
    let ctor ← getConstInfoCtor ctorName
    forallTelescopeReducing ctor.type fun args _ => do
      let mut fields := #[]
      let mut context := ← getLCtx
      let mut proofIds := #[]
      for arg in args do
        let decl ← arg.fvarId!.getDecl
        if decl.userName.hasMacroScopes || !decl.binderInfo.isExplicit then
          throwError "constructor arguments must be named and explicit"
        let proof ← isProp decl.type
        if proof then
          if proofIds.any (fun id => decl.type.containsFVar id) then
            throwError "proof fields cannot depend on earlier proofs"
          proofIds := proofIds.push arg.fvarId!
        else
          if decl.type.hasFVar then throwError "data fields cannot be dependent"
          let some fn := decl.type.getAppFn.constName?
            | throwError "unsupported field type: {decl.type}"
          unless [``String, ``Bool, ``Nat].contains fn do
            unless decl.type.getAppArgs.isEmpty || [``List, ``Subtype, ``Option].contains fn do
              throwError "unsupported field type: {decl.type}"
            unless (← synthInstance? (mkApp (mkConst ``FormModel) decl.type)).isSome do
              throwError "field type must derive FormModel first: {decl.type}"
          checkOptionalJson (← mkAppOptM ``FormModel.Raw #[some decl.type, none])
        let binder ← mkFreshUserName `field
        context := context.setUserName arg.fvarId! binder
        fields := fields.push ⟨decl.userName, binder, decl.type, proof⟩
      return ⟨ctorName, fields, context, ← getLocalInstances⟩
  return (record, ctors)

/-- Prints `type` so that it re-elaborates to the same term inside generated namespaces. -/
private def delabRooted
  (context : LocalContext)
  (instances : LocalInstances)
  (type : Expr)
  : CommandElabM TermSyntax := do
  -- Preserve names and coercion targets when re-elaborating generated code.
  let delabbed ← liftTermElabM <| withLCtx context instances <|
    withOptions (fun opts => opts.setBool `pp.fullNames true |>.setBool `pp.coercions.types true
        |>.setBool `pp.funBinderTypes true) <|
      PrettyPrinter.delab type
  -- Generated code is elaborated inside the model's namespace, where these names could be shadowed.
  let env ← getEnv
  let rooted ← delabbed.raw.replaceM fun node => do
    let .ident _ _ name _ := node | return none
    if (context.findFromUserName? name).isSome || !env.contains name then return none
    return some (mkIdent (`_root_ ++ name)).raw
  return ⟨rooted⟩

private def fieldType (ctor : Constructor) (field : FieldInfo) : CommandElabM TermSyntax :=
  delabRooted ctor.context ctor.instances field.type

private def app (fn : TermSyntax) (args : Array TermSyntax) : CommandElabM TermSyntax :=
  `($fn $args*)

private def matchOn
  (values : Array TermSyntax)
  (alts : Array Alternative)
  : CommandElabM TermSyntax := do
  let discrs ← values.mapM fun value => `(Parser.Term.matchDiscr| $value:term)
  `(match $[$discrs],* with $alts:matchAlt*)

private def alternative
  (patterns : Array TermSyntax)
  (body : TermSyntax)
  : CommandElabM Alternative :=
  `(Parser.Term.matchAltExpr| | $[$patterns],* => $body)

private def emitRecord
  (name : Name)
  (fields : Array (Name × TermSyntax))
  (json : Bool)
  : CommandElabM Unit := do
  let fields ← fields.mapM fun (name, type) =>
    `(Parser.Command.structExplicitBinder| ($(ident name) : $type))
  if json then
    emitIn name (← `(command| structure $(global name):ident where
      $fields:structExplicitBinder*
      deriving Lean.ToJson, Lean.FromJson))
  else
    emit (← `(command| structure $(global name):ident where
      $fields:structExplicitBinder*))

private def emitFieldLawful
  (ns raw field : Name)
  : CommandElabM TermSyntax := do
  let name := ns ++ `Field.lawful ++ field
  let (type, value) ← liftTermElabM do
    let raw := mkConst raw
    let selected := mkConst (ns ++ `Field ++ field)
    let type := (← inferType selected).appArg!
    let get := mkConst (ns ++ `Raw ++ field)
    let put := mkConst (ns ++ `Field ++ `set ++ field)
    -- Record eta reduces all three laws to reflexivity.
    let viewSet ← withLocalDeclD `value type fun value =>
      withLocalDeclD `source raw fun source => do
        mkLambdaFVars #[value, source] (← mkEqRefl value)
    let setView ← withLocalDeclD `source raw fun source => do
      mkLambdaFVars #[source] (← mkEqRefl source)
    let setSet ← withLocalDeclD `first type fun first =>
      withLocalDeclD `last type fun last =>
        withLocalDeclD `source raw fun source => do
          mkLambdaFVars #[first, last, source] (← mkEqRefl (mkApp2 put last source))
    let value := mkAppN (mkConst ``Forms.Model.lawfulMkLens)
      #[raw, type, get, put, viewSet, setView, setSet]
    let lens := mkApp2 (mkConst (ns ++ `Field.lens)) type selected
    return (mkAppN (mkConst ``LeanLens.LawfulLens) #[raw, type, lens], value)
  liftCoreM <| addDecl (.thmDecl { name, levelParams := [], type, value })
  return global name

private def emitFields
  (ns raw : Name)
  (fields : Array (FieldInfo × TermSyntax))
  : CommandElabM Unit := do
  let rawName := raw
  let field := global (ns ++ `Field)
  let raw := global raw
  let ctors ← fields.mapM fun (f, type) =>
    `(Parser.Command.ctor| | $(ident f.name):ident : $(ident `Field) (FormModel.Raw $type))
  emit (← `(command| inductive $field:ident : Type → Type where $ctors:ctor*))
  let selected ← fresh `selected
  let old ← fresh `old
  let new ← fresh `new
  let mut getters := #[]
  let mut setters := #[]
  let mut keys := #[]
  for (f, type) in fields do
    let pattern : TermSyntax := global (ns ++ `Field ++ f.name)
    let projection := global (ns ++ `Raw ++ f.name)
    getters := getters.push (← alternative #[pattern] (← `($projection $old)))
    let binders ← fields.mapM fun _ => fresh `value
    let values := (fields.zip binders).map fun ((g, _), binder) =>
      if f.name == g.name then (new : TermSyntax) else binder
    let fieldSetter := global (ns ++ `Field ++ `set ++ f.name)
    let rawMk := global (ns ++ `Raw ++ `mk)
    -- `casesOn` instead of `match` avoids compiling an n-field matcher per setter.
    emit (← `(command| @[expose] def $fieldSetter:ident ($new:ident : FormModel.Raw $type) ($old:ident : $raw) : $raw :=
      $(global (ns ++ `Raw ++ `casesOn)) (motive := fun _ => $raw) $old fun $binders* => $(← app rawMk values)))
    setters := setters.push (← alternative #[pattern] (← `($fieldSetter $new $old)))
    keys := keys.push (← alternative #[pattern] (Syntax.mkStrLit f.name.getString!))
  let getter ← if fields.isEmpty then `(nomatch $selected) else matchOn #[selected] getters
  let setter ← if fields.isEmpty then `(nomatch $selected) else matchOn #[selected] setters
  let key ← if fields.isEmpty then `(nomatch $selected) else matchOn #[selected] keys
  let get := global (ns ++ `Field.get)
  let set := global (ns ++ `Field.set)
  let keyName := global (ns ++ `Field.key)
  let lens := global (ns ++ `Field.lens)
  let lawful := global (ns ++ `Field.lawful)
  emit (← `(command| @[expose] def $get:ident {α : Type} ($selected:ident : $field α) ($old:ident : $raw) : α := $getter))
  emit (← `(command| @[expose] def $set:ident {α : Type} ($selected:ident : $field α) ($new:ident : α) ($old:ident : $raw) : $raw := $setter))
  emit (← `(command| @[expose] def $keyName:ident {α : Type} ($selected:ident : $field α) : String := $key))
  emit (← `(command| @[expose] def $lens:ident {α : Type} ($selected:ident : $field α) : LeanLens.Lens' $raw α :=
    LeanLens.mkLens ($get $selected) ($set $selected)))
  let lawfulCases ← fields.mapM fun (f, _) => do
    let proof ← emitFieldLawful ns rawName f.name
    alternative #[global (ns ++ `Field ++ f.name)] proof
  let lawfulBody ← if fields.isEmpty then `(nomatch $selected) else matchOn #[selected] lawfulCases
  emit (← `(command| instance $lawful:ident {α : Type} ($selected:ident : $field α) : LeanLens.LawfulLens ($lens $selected) :=
    $lawfulBody))
  emit (← `(command| @[expose, reducible] instance $(global (ns ++ `rawFields)):ident : Forms.Model.Fields $raw where
    Field := $field
    lens := $lens
    lawful := $lawful
    key := $keyName))

private structure ModelInfo where
  name : Name
  record : Bool
  constructors : Array Constructor

private def ModelInfo.raw (model : ModelInfo) := model.name ++ `Raw
private def ModelInfo.localNS (model : ModelInfo) (ctor : Constructor) :=
  if model.record then model.name else ctor.name
private def ModelInfo.payload (model : ModelInfo) (ctor : Constructor) := model.localNS ctor ++ `Raw
private def ModelInfo.parts (model : ModelInfo) (ctor : Constructor) := model.localNS ctor ++ `Parts
private def ModelInfo.constraint (model : ModelInfo) (ctor : Constructor) (field : FieldInfo) :=
  model.name ++ `Constraint ++ if model.record then field.name else
    Name.mkSimple (ctor.name.getString! ++ "_" ++ field.name.getString!)
private def ModelInfo.enum (model : ModelInfo) :=
  !model.record && model.constructors.all (·.fields.isEmpty)
private def ModelInfo.rules (model : ModelInfo) :=
  model.constructors.flatMap fun ctor => ctor.proofs.map (ctor, ·)

private def ModelInfo.wrap
  (model : ModelInfo)
  (ctor : Constructor)
  (value : TermSyntax)
  : CommandElabM TermSyntax := do
  if model.record then return value
  let name := global (model.raw ++ Name.mkSimple ctor.name.getString!)
  if ctor.data.isEmpty then return name
  app name #[value]

private def ModelInfo.liftError
  (model : ModelInfo)
  (ctor : Constructor)
  (error : TermSyntax)
  : CommandElabM TermSyntax := do
  if model.record then return error
  let constructor := global (model.name ++ `Constructor ++ Name.mkSimple ctor.name.getString!)
  `(Forms.Model.Error.inConstructor (α := $(global model.raw)) $constructor $error)

private def emitShapes (model : ModelInfo) : CommandElabM Unit := do
  for ctor in model.constructors do emitting m!"constructor `{ctor.name}`" do
    let fields ← ctor.data.mapM fun f => return (f, ← fieldType ctor f)
    let rawFields ← fields.mapM fun (f, type) => return (f.name, ← `(FormModel.Raw $type))
    emitRecord (model.payload ctor) rawFields true
    emitFields (model.localNS ctor) (model.payload ctor) fields
    emitRecord (model.parts ctor) (fields.map fun (f, type) => (f.name, type)) false
    let parts ← fresh `parts
    let values ← ctor.data.mapM fun f =>
      `(FormModel.erase ($(global (model.parts ctor ++ f.name)) $parts))
    let body ← app (global (model.payload ctor ++ `mk)) values
    emit (← `(command| @[expose] def $(global (model.parts ctor ++ `toRaw)):ident
      ($parts:ident : $(global (model.parts ctor))) : $(global (model.payload ctor)) := $body))

private def emitConstructors (model : ModelInfo) : CommandElabM Unit := do
  if model.record then return
  let raw := global model.raw
  let ctors ← model.constructors.mapM fun ctor => do
    let name := ident (Name.mkSimple ctor.name.getString!)
    if ctor.data.isEmpty then `(Parser.Command.ctor| | $name:ident)
    else `(Parser.Command.ctor| | $name:ident (payload : $(global (model.payload ctor))))
  emitIn model.raw <| ← if model.enum
    then `(command| inductive $raw:ident where $ctors:ctor*
      deriving DecidableEq, Lean.ToJson, Lean.FromJson)
    else `(command| inductive $raw:ident where $ctors:ctor* deriving Lean.ToJson, Lean.FromJson)
  let constructor := global (model.name ++ `Constructor)
  let ctors ← model.constructors.mapM fun ctor =>
    `(Parser.Command.ctor| | $(ident (Name.mkSimple ctor.name.getString!)):ident :
      $(ident `Constructor) $(global (model.payload ctor)))
  emit (← `(command| inductive $constructor:ident : Type → Type where $ctors:ctor*))
  let tagType := global (model.name ++ `Tag)
  let tags ← model.constructors.mapM fun ctor =>
    `(Parser.Command.ctor| | $(ident (Name.mkSimple ctor.name.getString!)):ident)
  emitIn (model.name ++ `Tag)
    (← `(command| inductive $tagType:ident where $tags:ctor* deriving DecidableEq, Repr))
  let selected ← fresh `selected
  let value ← fresh `value
  let payload ← fresh `payload
  let mut injections := #[]
  let mut projections := #[]
  let mut keys := #[]
  let mut decodings := #[]
  let mut tagsOf := #[]
  let mut valueTags := #[]
  for ctor in model.constructors do
    let pattern : TermSyntax := global (model.name ++ `Constructor ++ Name.mkSimple ctor.name.getString!)
    let tag : TermSyntax := global (model.name ++ `Tag ++ Name.mkSimple ctor.name.getString!)
    injections := injections.push (← alternative #[pattern] (← model.wrap ctor value))
    let found ← if ctor.data.isEmpty then `(some $(global (model.payload ctor ++ `mk))) else `(some $payload)
    let mut cases := #[← alternative #[← model.wrap ctor payload] found]
    if model.constructors.size > 1 then cases := cases.push (← alternative #[← `(_)] (← `(none)))
    projections := projections.push (← alternative #[pattern] (← matchOn #[value] cases))
    keys := keys.push (← alternative #[tag] (Syntax.mkStrLit ctor.name.getString!))
    decodings := decodings.push
      (← alternative #[Syntax.mkStrLit ctor.name.getString!] (← `(some $tag)))
    tagsOf := tagsOf.push (← alternative #[pattern] tag)
    valueTags := valueTags.push (← alternative #[← model.wrap ctor (← `(_))] tag)
  let injection ← matchOn #[selected] injections
  let projection ← matchOn #[selected] projections
  let key ← matchOn #[selected] keys
  let encoded ← fresh `encoded
  let decoding ← matchOn #[encoded] (decodings.push (← alternative #[← `(_)] (← `(none))))
  let tagOf ← matchOn #[selected] tagsOf
  let valueTag ← matchOn #[value] valueTags
  -- Fresh names, so constructors such as `inject` or `tag` cannot collide with the helpers.
  let inject ← fresh `inject
  let project ← fresh `project
  let tagOfName ← fresh `tagOf
  let tagName ← fresh `tag
  emitIn (model.name ++ `Tag) (← `(command| instance : Forms.Model.Key $tagType where
    encode $selected:ident := $key
    decode $encoded:ident := $decoding
    decode_encode := by
      intro $selected:ident
      cases $selected:ident <;> rfl
    encode_ne_empty := by
      intro $selected:ident
      cases $selected:ident <;> decide))
  emit (← `(command| @[expose] def $inject:ident {α : Type}
    ($selected:ident : $constructor α) ($value:ident : α) : $raw := $injection))
  emit (← `(command| @[expose] def $project:ident {α : Type}
    ($selected:ident : $constructor α) ($value:ident : $raw) : Option α := $projection))
  emit (← `(command| @[expose] def $tagOfName:ident {α : Type}
    ($selected:ident : $constructor α) : $tagType := $tagOf))
  emit (← `(command| @[expose] def $tagName:ident ($value:ident : $raw) : $tagType := $valueTag))
  emit (← `(command| @[expose, reducible] instance $(global (model.name ++ `constructors)):ident :
      Forms.Model.Constructors $raw where
    Constructor := $constructor
    Tag := $tagType
    inject := $inject
    project := $project
    tagOf := $tagOfName
    tag := $tagName))
  -- `split` stays linear in constructors; a single-constructor match reduces, so case on `source`.
  emit (← `(command| instance $(global (model.name ++ `lawfulConstructors)):ident :
      Forms.Model.LawfulConstructors $raw where
    project_inject := by
      intro payload selected value
      cases selected <;> rfl
    inject_project := by
      intro payload selected source value h
      change $inject selected value = source
      change $project selected source = some value at h
      cases selected <;> simp only [$project:ident] at h <;> (first | split at h | cases source) <;>
        simp_all [$inject:ident]
    tag_inject := by
      intro payload selected value
      cases selected <;> rfl))

private def emitErasure (model : ModelInfo) : CommandElabM Unit := do
  let value ← fresh `value
  let alts ← model.constructors.mapM fun ctor => do
    let pattern ← app (global ctor.name) (ctor.fields.map fun f => ident f.binder)
    let args ← ctor.data.mapM fun f => `(FormModel.erase $(ident f.binder))
    let payload ← app (global (model.payload ctor ++ `mk)) args
    alternative #[pattern] (← model.wrap ctor payload)
  let body ← matchOn #[value] alts
  let erase := global (model.name ++ `erase)
  let raw := global model.raw
  let name := global model.name
  emit (← `(command| @[expose] def $erase:ident ($value:ident : $name) : $raw := $body))
  emit (← `(command| @[expose, reducible] instance $(global (model.name ++ `formModel)):ident :
    FormModel $name := ⟨$raw, $erase⟩))

private def emitAlwaysValid (model : ModelInfo) : CommandElabM Unit := do
  unless model.enum do return
  let value ← fresh `value
  let alts ← model.constructors.mapM fun ctor => do
    alternative #[← model.wrap ctor (← `(_))] (global ctor.name)
  emit (← `(command| instance $(global (model.name ++ `alwaysValid)):ident :
      Forms.Model.AlwaysValid $(global model.name) where
    restore $value:ident := $(← matchOn #[value] alts)
    erase_restore $value:ident := by cases $value:ident <;> rfl
    restore_erase $value:ident := by cases $value:ident <;> rfl))

private def emitConstraints (model : ModelInfo) : CommandElabM Unit := do
  let constraint := global (model.name ++ `Constraint)
  let ctors ← model.rules.mapM fun (ctor, f) =>
    `(Parser.Command.ctor| | $(ident (Name.mkSimple (model.constraint ctor f).getString!)):ident)
  emit (← `(command| inductive $constraint:ident where $ctors:ctor*))
  if model.rules.isEmpty then return
  let selected ← fresh `selected
  let parts ← fresh `parts
  let mut partTypes := #[]
  let mut rawTypes := #[]
  let mut properties := #[]
  let mut erasures := #[]
  for (ctor, f) in model.rules do
    let pattern : TermSyntax := global (model.constraint ctor f)
    partTypes := partTypes.push (← alternative #[pattern] (global (model.parts ctor)))
    rawTypes := rawTypes.push (← alternative #[pattern] (global (model.payload ctor)))
    let mut property ← fieldType ctor f
    for field in ctor.data.reverse do
      let projection := global (model.parts ctor ++ field.name)
      property ← `(let $(ident field.binder):ident := $projection $parts; $property)
    properties := properties.push (← alternative #[pattern, parts] property)
    erasures := erasures.push (← alternative #[pattern, parts]
      (← `($(global (model.parts ctor ++ `toRaw)) $parts)))
  let partsType := global (model.name ++ `Constraint.Parts)
  let rawType := global (model.name ++ `Constraint.Raw)
  let holds := global (model.name ++ `Constraint.holds)
  let toRaw := global (model.name ++ `Constraint.toRaw)
  let partBody ← matchOn #[selected] partTypes
  let rawBody ← matchOn #[selected] rawTypes
  emit (← `(command| @[expose] abbrev $partsType:ident ($selected:ident : $constraint) : Type := $partBody))
  emit (← `(command| @[expose] abbrev $rawType:ident ($selected:ident : $constraint) : Type := $rawBody))
  let property ← matchOn #[selected, parts] properties
  let erasure ← matchOn #[selected, parts] erasures
  emit (← `(command| @[expose] def $holds:ident ($selected:ident : $constraint)
    ($parts:ident : $partsType $selected) : Prop := $property))
  emit (← `(command| @[expose] abbrev $toRaw:ident ($selected:ident : $constraint)
    ($parts:ident : $partsType $selected) : $rawType $selected := $erasure))
  emit (← `(command| @[expose, reducible] instance $(global (model.name ++ `constraints)):ident :
      Forms.Model.Constraints $constraint where
    Parts := $partsType
    Raw := $rawType
    holds := $holds
    toRaw := $toRaw))

/-- Folds `results` into `fn` with `accumulate`, so each result adds no binder around the rest. -/
private def accumulateAll
  (fn : TermSyntax)
  (results : Array TermSyntax)
  : CommandElabM TermSyntax := do
  results.foldlM (init := ← `(Except.ok $fn)) fun acc result =>
    `(Forms.Model.accumulate $acc $result)

private def validationBranch
  (model : ModelInfo)
  (ctor : Constructor)
  (payload : TermSyntax)
  : CommandElabM TermSyntax := do
  let raw ← model.wrap ctor payload
  let errors ← `(List (Forms.Model.Error $raw))
  let partsType := global (model.parts ctor)
  let toRaw := global (model.parts ctor ++ `toRaw)
  let parts ← fresh `parts
  let preserved ← fresh `preserved
  let values ← ctor.data.mapM fun _ => fresh `value
  let mut preservation ← `(rfl)
  for value in values, i in [:values.size] do
    preservation ← if i == 0
      then `(congrArg $(global (model.payload ctor ++ `mk)) (Subtype.property $value))
      else `(congr $preservation (Subtype.property $value))
  let partValue ← app (global (model.parts ctor ++ `mk)) (← values.mapM fun v => `(Subtype.val $v))
  let mut fn ← `((⟨$partValue, ($preservation :)⟩ : { $parts : $partsType // $toRaw $parts = $payload }))
  for (field, value) in (ctor.data.zip values).reverse do
    let projection ← `($(global (model.payload ctor ++ field.name)) $payload)
    fn ← `(fun ($value : Forms.Model.Validated $(← fieldType ctor field) $projection) => $fn)
  let fieldResults ← ctor.data.mapM fun field => do
    let error ← fresh `error
    let lifted ← model.liftError ctor
      (← `(Forms.Model.Error.lift (value := $payload) $(global (model.localNS ctor ++ `Field ++ field.name)) $error))
    `((Forms.Model.Validation.validate (model := $(← fieldType ctor field))
        ($(global (model.payload ctor ++ field.name)) $payload)).mapError (List.map fun $error:ident => $lifted))
  let validatedParts ← accumulateAll fn fieldResults
  let proofs ← ctor.proofs.mapM fun _ => fresh `proof
  let mut arguments := #[]
  let mut proofIndex := 0
  for field in ctor.fields do
    if field.proof then
      arguments := arguments.push (← `(PLift.down $(proofs[proofIndex]!)))
      proofIndex := proofIndex + 1
    else
      arguments := arguments.push (← `($(global (model.parts ctor ++ field.name)) $parts))
  let original ← app (global ctor.name) arguments
  let equality ← if model.record then pure (preserved : TermSyntax) else do
    let value ← fresh `value
    `(congrArg (fun ($value:ident : $(global (model.payload ctor))) => $(← model.wrap ctor value)) $preserved)
  fn ← `((⟨$original, $equality⟩ : Forms.Model.Validated $(global model.name) $raw))
  for (field, proof) in (ctor.proofs.zip proofs).reverse do
    let constraint := global (model.constraint ctor field)
    fn ← `(fun ($proof : PLift (Forms.Model.Constraints.holds $constraint $parts)) => $fn)
  let checks ← ctor.proofs.mapM fun field => do
    let check ← `(Forms.Model.Decision.toExcept
      (Forms.Model.ConstraintRule.check (c := $(global (model.constraint ctor field))) $parts) $preserved)
    if model.record then return check
    let error ← fresh `error
    `(($check).mapError (List.map fun $error:ident => $(← model.liftError ctor error)))
  let checked ← accumulateAll fn checks
  `(match ($validatedParts : Except $errors { $parts : $partsType // $toRaw $parts = $payload }) with
    | .error errors => .error errors
    | .ok ⟨$parts, $preserved⟩ => $checked)

private def emitValidation (model : ModelInfo) : CommandElabM Unit := do
  -- Children are resolved now, so an instance's term holds only its own rules, not its subtree.
  for ctor in model.constructors do
    for field in ctor.data do
      let missing ← liftTermElabM do
        return (← synthInstance? (← mkAppOptM ``Forms.Model.Validation #[some field.type, none])).isNone
      if missing then
        throwError "Validation {field.type} is missing: declare its constraint rules before deriving \
          {model.name}"
  let mut params : Array (TSyntax ``Parser.Term.instBinder) := #[]
  for (ctor, field) in model.rules do
    params := params.push (← `(Parser.Term.instBinder|
      [Forms.Model.ConstraintRule $(global (model.constraint ctor field))]))
  let value ← fresh `raw
  let body ← match model.record, model.constructors with
    | true, #[ctor] => validationBranch model ctor value
    | _, constructors => do
      let alternatives ← constructors.mapM fun ctor => do
        let payload : TermSyntax ← if ctor.data.isEmpty
          then pure (global (model.payload ctor ++ `mk))
          else fresh `payload
        alternative #[← model.wrap ctor payload] (← validationBranch model ctor payload)
      matchOn #[value] alternatives
  let validate := global (model.name ++ `validate)
  let raw := global model.raw
  let name := global model.name
  let fields := model.constructors.foldl (fun size ctor => max size ctor.fields.size) 0
  let depth := Syntax.mkNumLit (toString (512 + 8 * fields))
  emit (← `(command| set_option maxRecDepth $depth in
    @[expose] def $validate:ident $params:instBinder*
    ($value:ident : $raw) : Except (List (Forms.Model.Error $value)) (Forms.Model.Validated $name $value) := $body))
  emit (← `(command| @[expose] instance $(global (model.name ++ `validation)):ident $params:instBinder* :
    Forms.Model.Validation $name := ⟨$validate⟩))

private def deriveOne (name : Name) : CommandElabM Unit := do
  let saved ← get
  let generate : CommandElabM Unit :=
    -- Keep diagnostics synchronous so failures can roll back the entire derivation.
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      try
        let (record, constructors) ← liftTermElabM <| inspect name
        let model := { name, record, constructors : ModelInfo }
        emitShapes model
        emitting "constructors" (emitConstructors model)
        emitting "erasure" (emitErasure model)
        emitting "always valid" (emitAlwaysValid model)
        emitting "constraints" (emitConstraints model)
        emitting "validation" (emitValidation model)
      catch error =>
        let message ← addMessageContext error.toMessageData
        throwError "deriving FormModel for `{privateToUserName name}`: {message}"
  let _ ← MonadFinally.tryFinally' generate fun result => do
    unless result.isSome do
      -- Roll back declarations but keep traces and non-error messages for debugging.
      let failed ← get
      let previous := saved.messages.reportedPlusUnreported.size
      let kept := (failed.messages.reportedPlusUnreported.toList.drop previous).filter
        (!·.severity matches .error)
      set { saved with
        messages := kept.foldl (·.add ·) saved.messages
        traceState := failed.traceState }

initialize registerDerivingHandler ``FormModel fun names => do
  for name in names do deriveOne name
  return true

/-- `deriving HasUuid` for a structure with an `id : Uuid` field. Also generates `mkWithoutUuid`,
which takes the other fields. -/
private def deriveHasUuid (name : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env name do throwError "`{name}` is not a structure"
  let ctor := getStructureCtor env name
  unless ctor.numParams == 0 do throwError "the structure must not have parameters"
  let fields ← liftTermElabM <| forallTelescope ctor.type fun args _ => args.mapM fun arg => do
    let decl ← arg.fvarId!.getDecl
    if decl.type.hasFVar then throwError "fields cannot be dependent"
    return (decl.userName, decl.type)
  let some (_, idType) := fields.find? (·.1 == `id)
    | throwError "the structure needs an `id : Uuid` field"
  unless ← liftTermElabM (isDefEq idType (mkConst ``Uuid)) do
    throwError "the `id` field must have type `Uuid`"
  let item ← fresh `item
  let uuid ← fresh `uuid
  let withUuid ← app (global ctor.name) <| ← fields.mapM fun (field, _) =>
    if field == `id then pure uuid else app (global (name ++ field)) #[item]
  emit (← `(command| @[expose] instance $(global (name ++ `hasUuid)):ident :
      Forms.Model.HasUuid $(global name) where
    lens := LeanLens.mkLens $(global (name ++ `id)) fun $uuid:ident $item:ident => $withUuid))
  let rest := fields.filter (·.1 != `id)
  let binders ← rest.mapM fun (field, type) => do
    `(Parser.Term.bracketedBinderF| ($(ident field) : $(← delabRooted {} {} type)))
  let representative ← app (global ctor.name) <| ← fields.mapM fun (field, _) =>
    if field == `id then `(Forms.Model.Uuid.nil) else pure (ident field)
  let constructor := global (name ++ `mkWithoutUuid)
  emit (← `(command| @[expose] def $constructor:ident $binders:bracketedBinder* :
      Forms.Model.HasUuid.WithoutUuid $(global name) :=
    Forms.Model.HasUuid.withoutUuid $representative))

initialize registerDerivingHandler ``HasUuid fun names => do
  for name in names do
    emitting m!"deriving HasUuid for `{privateToUserName name}`" (deriveHasUuid name)
  return true

elab "#fields " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  unless isStructure env name do throwErrorAt id "{name} is not a structure"
  let ctor := getStructureCtor env name
  liftTermElabM <| forallTelescope ctor.type fun args _ => do
    let fields ← args[ctor.numParams:].toArray.mapM fun arg => do
      let decl ← arg.fvarId!.getDecl
      return m!"- {decl.userName} : {decl.type}"
    let body := if fields.isEmpty then m!"(no fields)" else .joinSep fields.toList "\n"
    logInfoAt id m!"Fields of {id.getId}:\n{body}"

end Forms.Model.Deriving
