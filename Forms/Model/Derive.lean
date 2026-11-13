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

private def emit (command : TSyntax `command) : CommandElabM Unit := elabCommand command

/-- Emits `command` in `name`'s namespace, so its auto-named instances stay unique across modules. -/
private def emitIn (name : Name) (command : TSyntax `command) : CommandElabM Unit := do
  let current ← getCurrNamespace
  unless current.isPrefixOf name && name != current do return ← emit command
  let relative := mkIdent (name.replacePrefix current .anonymous)
  emit (← `(command| namespace $relative))
  emit command
  emit (← `(command| end $relative))

private def inspect (name : Name) : MetaM (Bool × Array Constructor) := do
  if isPrivateName name then
    throwError "FormModel requires public model declarations"
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do
    throwError "FormModel requires a monomorphic type without parameters or indices"
  unless info.all.length == 1 && !info.isRec do
    throwError "FormModel does not support recursive or mutually recursive types"
  if info.ctors.isEmpty then throwError "FormModel requires at least one constructor"
  let record := isStructure (← getEnv) name
  if record && !(getStructureParentInfo (← getEnv) name).isEmpty then
    throwError "FormModel does not support structure inheritance yet"
  let ctors ← info.ctors.toArray.mapM fun ctorName => do
    let ctor ← getConstInfoCtor ctorName
    forallTelescopeReducing ctor.type fun args _ => do
      let mut fields := #[]
      let mut context := ← getLCtx
      let mut proofIds := #[]
      for arg in args do
        let decl ← arg.fvarId!.getDecl
        if decl.userName.hasMacroScopes || !decl.binderInfo.isExplicit then
          throwError "FormModel constructor arguments must be named and explicit"
        let proof ← isProp decl.type
        if proof then
          if proofIds.any (fun id => decl.type.containsFVar id) then
            throwError "FormModel proof fields cannot depend on earlier proofs"
          proofIds := proofIds.push arg.fvarId!
        else
          if decl.type.hasFVar then throwError "FormModel data fields cannot be dependent"
          let some fn := decl.type.getAppFn.constName?
            | throwError "Unsupported FormModel field type: {decl.type}"
          unless [``String, ``Bool, ``Nat].contains fn do
            unless decl.type.getAppArgs.isEmpty || fn == ``List do
              throwError "Unsupported FormModel field type: {decl.type}"
            unless (← synthInstance? (mkApp (mkConst ``FormModel) decl.type)).isSome do
              throwError "Field type must derive FormModel first: {decl.type}"
        let binder ← mkFreshUserName `field
        context := context.setUserName arg.fvarId! binder
        fields := fields.push ⟨decl.userName, binder, decl.type, proof⟩
      return ⟨ctorName, fields, context, ← getLocalInstances⟩
  return (record, ctors)

private def fieldType (ctor : Constructor) (field : FieldInfo) : CommandElabM TermSyntax :=
  -- Preserve names and coercion targets when re-elaborating generated code.
  liftTermElabM <| withLCtx ctor.context ctor.instances <|
    withOptions (fun opts => opts.setBool `pp.fullNames true |>.setBool `pp.coercions.types true) <|
      PrettyPrinter.delab field.type

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

private def emitFields
  (ns raw : Name)
  (fields : Array (FieldInfo × TermSyntax))
  : CommandElabM Unit := do
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
  let mut lawfulCases := #[]
  for (f, _) in fields do
    let pattern : TermSyntax := global (ns ++ `Field ++ f.name)
    let proof := global (ns ++ `Field ++ (f.name.appendAfter "_lawful"))
    emit (← `(command| theorem $proof:ident : LeanLens.LawfulLens ($lens $pattern) :=
      Forms.Model.lawfulMkLens (get := $get $pattern) (put := $set $pattern)
        (fun _ src => by cases src; rfl) (fun src => by cases src; rfl) (fun _ _ src => by cases src; rfl)))
    lawfulCases := lawfulCases.push (← alternative #[pattern] proof)
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
  for ctor in model.constructors do
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
  emitIn model.raw (← `(command| inductive $raw:ident where $ctors:ctor* deriving Lean.ToJson, Lean.FromJson))
  let constructor := global (model.name ++ `Constructor)
  let ctors ← model.constructors.mapM fun ctor =>
    `(Parser.Command.ctor| | $(ident (Name.mkSimple ctor.name.getString!)):ident :
      $(ident `Constructor) $(global (model.payload ctor)))
  emit (← `(command| inductive $constructor:ident : Type → Type where $ctors:ctor*))
  let selected ← fresh `selected
  let value ← fresh `value
  let payload ← fresh `payload
  let mut injections := #[]
  let mut projections := #[]
  let mut keys := #[]
  for ctor in model.constructors do
    let pattern : TermSyntax := global (model.name ++ `Constructor ++ Name.mkSimple ctor.name.getString!)
    injections := injections.push (← alternative #[pattern] (← model.wrap ctor value))
    let found ← if ctor.data.isEmpty then `(some $(global (model.payload ctor ++ `mk))) else `(some $payload)
    let mut cases := #[← alternative #[← model.wrap ctor payload] found]
    if model.constructors.size > 1 then cases := cases.push (← alternative #[← `(_)] (← `(none)))
    projections := projections.push (← alternative #[pattern] (← matchOn #[value] cases))
    keys := keys.push (← alternative #[pattern] (Syntax.mkStrLit ctor.name.getString!))
  let injection ← matchOn #[selected] injections
  let projection ← matchOn #[selected] projections
  let key ← matchOn #[selected] keys
  let inject := global (model.name ++ `Constructor.inject)
  let project := global (model.name ++ `Constructor.project)
  let keyName := global (model.name ++ `Constructor.key)
  emit (← `(command| @[expose] def $inject:ident {α : Type}
    ($selected:ident : $constructor α) ($value:ident : α) : $raw := $injection))
  emit (← `(command| @[expose] def $project:ident {α : Type}
    ($selected:ident : $constructor α) ($value:ident : $raw) : Option α := $projection))
  emit (← `(command| @[expose] def $keyName:ident {α : Type}
    ($selected:ident : $constructor α) : String := $key))
  emit (← `(command| @[expose, reducible] instance $(global (model.name ++ `constructors)):ident :
      Forms.Model.Constructors $raw where
    Constructor := $constructor
    inject := $inject
    project := $project
    key := $keyName))
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
        simp_all [$inject:ident]))

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

/-- Validates the fields of `payload` collecting all errors, then checks the constraints. -/
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
  let mut params : Array (TSyntax ``Parser.Term.instBinder) := #[]
  let mut childTypes : Array Expr := #[]
  for ctor in model.constructors do
    for field in ctor.data do
      unless childTypes.contains field.type do
        childTypes := childTypes.push field.type
        params := params.push (← `(Parser.Term.instBinder|
          [Forms.Model.Validation $(← fieldType ctor field)]))
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
  let (record, constructors) ← liftTermElabM <| inspect name
  let model := { name, record, constructors : ModelInfo }
  emitShapes model
  emitConstructors model
  emitErasure model
  emitConstraints model
  emitValidation model

initialize registerDerivingHandler ``FormModel fun names => do
  for name in names do deriveOne name
  return true

/-- Lists a structure's fields as `name : type`, one per line. -/
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
