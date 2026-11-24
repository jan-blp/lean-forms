module

public import Forms.Model.Component.LocalState
public import Forms.Model.Invocation
public import Forms.Runtime.Input
public import Forms.Runtime.Display

@[expose] public section
namespace Forms.Runtime.ModelView
open Forms.Model

def editorValue {α : Type} : Model.Editor α → α → Display.Value
  | .formatted format, value => .text format.kind (format.print value)
  | .checkbox, value => .checkbox value
  | .choices (key := _) { options, .. } selected, value =>
    .choices (value.map (Key.encode ∘ selected))
      (options.map fun option => { value := Key.encode option.key, label := option.label })
  | .refine editor print .., value => editorValue editor (print value)

def stale
  {α : Type}
  (widget : Model.Editor α)
  (read : String → Except String α)
  (value : α)
  (evidence : Model.Evidence)
  : Bool :=
  match read evidence.text with
  | .ok read => editorValue widget read != editorValue widget value
  | .error _ => true

theorem stale_of_read
  {α : Type}
  {widget : Model.Editor α}
  {read : String → Except String α}
  {value : α}
  {evidence : Model.Evidence}
  (reads : read evidence.text = .ok value)
  : stale widget read value evidence = false := by
  simp [stale, reads]

def readPick
  {α : Type}
  (read : String → Except String α)
  (picked : Model.Evidence)
  : Except DecodeError α :=
  (read picked.text).mapError fun message => .input s!"Could not read \"{picked.text}\": {message}"

def evidenceOf
  {α β : Type}
  (widget : Model.Editor β)
  (value : α)
  (current : β)
  : EvidenceSupport α β → Display.Evidence
  | .unsupported => .unsupported
  | .supported slot => match slot.path.get value with
    | none => .missing
    | some evidence => .linked evidence (stale widget slot.read current evidence)

def editor
  {α : Type}
  (widget : Model.Editor α)
  (value : α)
  (evidence : Display.Evidence)
  (target : Display.Target)
  (location : ErasedLocation)
  (label : String)
  (disabled : Bool)
  (messages : List Message)
  : Display.Control :=
  { key := .edit location, target, label, disabled, location, messages
    input := .field (editorValue widget value) evidence }

def _root_.Forms.Model.Targets.erase
  {α : Type}
  {value : α}
  : Model.Targets α value → Diagnostic.Targets
  | .global => .global
  | .locations first rest => .locations first.erase (rest.map (·.erase))

def error {α : Type} {value : α} (error : Model.Error value) : Diagnostic where
  kind := .error
  message := error.message
  targets := error.targets.erase

def report {α : Type} {value : α} (checked : Bool) (report : Model.Report value) : Diagnostic where
  kind := .report
    { state := report.status
      severity := report.severity
      outdated := !checked }
  message := report.message
  targets := report.targets.erase

def button
  (key : ControlKey)
  (target : Display.Target)
  (location : ErasedLocation)
  (label : String)
  (disabled : Bool)
  : Display.Control :=
  { key, target, label, disabled, location
    input := .action
    messages := [] }

def option {κ : Type} [Lean.ToJson κ] (reference : Reference κ) : Display.ChoiceOption :=
  { value := reference.key, label := reference.label }

def searchResults {κ : Type} [Lean.ToJson κ] : Status (LookupResults κ) → Display.SearchResults
  | .loading => .loading
  | .failed message => .failed message
  | .ready results => .found (results.found.map option) results.more

inductive ActionError where
  | decode (error : DecodeError)
  | invalid (error : Model.InvocationError)
  | idCollision (id : Uuid)

def noArgument
  {m : Type → Type}
  {α : Type}
  [Monad m]
  [MonadExcept ActionError m]
  (argument : Option Input)
  (invocation : α)
  : m α :=
  match argument with
  | none => pure invocation
  | some _ => throw (.decode (.clientBug .unexpectedArgument))

structure NodeEvaluation
  (Γ : Context)
  (α state β : Type)
  (viewType : Type := Display.View) where
  output : β
  locals : state
  view : viewType
  requests : List HttpRequest
  /-- Draws new item ids from the `Supply` state. -/
  apply :
    List Nat → Option Input →
      StateT Supply (Except ModelView.ActionError) (ComponentUpdate Γ α state)

/-- Runtime facts shared by one evaluation; unlike `Env`, components cannot bind or set them.
Build with `Ambient.of`, which derives `messages` from `diagnostics`. -/
structure Ambient where
  cache : HttpRequest.Cache
  diagnostics : List Diagnostic
  messages : Std.HashMap ErasedLocation (List Message)

def Ambient.of
  (cache : HttpRequest.Cache)
  (diagnostics : List Diagnostic)
  : Ambient :=
  { cache, diagnostics, messages := Diagnostic.messageIndex diagnostics }

def Ambient.messagesAt (ambient : Ambient) (location : ErasedLocation) : List Message :=
  ambient.messages.getD location []

structure Evaluated (Γ : Context) (α state β : Type)
  extends NodeEvaluation Γ α state β, Ambient where
  value : α
  env : Env Γ

def absent {m : Type → Type} {α : Type} [MonadExcept ActionError m] : m α :=
  throw (.invalid .absent)

/-- A `bind` around an evaluated `body`, which stores the bound value at its head. -/
def bound
  {Γ : Context}
  {α β γ state viewType : Type}
  (stored : β)
  (body : NodeEvaluation (⟨.writable, β⟩ :: Γ) α state γ viewType)
  : NodeEvaluation Γ α (Binding β state) γ viewType where
  output := body.output
  locals := { value := stored, tail := body.locals }
  view := body.view
  requests := body.requests
  apply := fun route argument => match route with
    | 0 :: rest => do
      let updated ← body.apply rest argument
      return { updated with
        state := updated.state.tail
        locals := { value := updated.state.value, tail := updated.locals } }
    | _ => absent

/-- An evaluated `body` that reads `producer`'s output; routes `0` and `1` reach each. -/
def observed
  {Γ : Context}
  {α β γ producerState consumerState producerView bodyView viewType : Type}
  (producer : NodeEvaluation Γ α producerState β producerView)
  (body : NodeEvaluation (⟨.readOnly, β⟩ :: Γ) α consumerState γ bodyView)
  (view : viewType)
  : NodeEvaluation Γ α (ObservationState producerState consumerState) γ viewType where
  output := body.output
  locals := { producer := producer.locals, consumers := body.locals }
  view := view
  requests := producer.requests ++ body.requests
  apply := fun route argument => match route with
    | 0 :: rest => do
      let updated ← producer.apply rest argument
      return updated.mapLocals (fun locals => { producer := locals, consumers := body.locals })
    | 1 :: rest => do
      let updated ← body.apply rest argument
      return { updated with
        state := updated.state.tail
        locals := { producer := producer.locals, consumers := updated.locals } }
    | _ => absent

/-- A view given the content of each of its `holes`. -/
abbrev Hollow (holes : Nat) := Vector (List Display.View) holes → Display.View

/-- An owned component's view, kept until a layout places it. -/
structure Prepared (holes : Nat) where
  view : Hollow holes

abbrev Presentations (Δ : ViewContext) := {holes : Nat} → ViewRef Δ holes → Prepared holes

mutual
def renderLayout
  {Δ : ViewContext}
  (views : {holes : Nat} → ViewRef Δ holes → Hollow holes)
  : Layout Δ → Display.View
  | .fill view contents => views view (renderFills views contents)
  | .group label children => .stack label (renderAll views children)

def renderAll
  {Δ : ViewContext}
  (views : {holes : Nat} → ViewRef Δ holes → Hollow holes)
  : List (Layout Δ) → List Display.View
  | [] => []
  | child :: rest => renderLayout views child :: renderAll views rest

def renderFills
  {Δ : ViewContext}
  {holes : Nat}
  (views : {holes : Nat} → ViewRef Δ holes → Hollow holes)
  : Fills Δ holes → Vector (List Display.View) holes
  | .nil => #v[]
  | .cons content rest => (#v[renderAll views content] ++ renderFills views rest).cast (by omega)
end

def NodeEvaluation.mapView
  {Γ : Context}
  {α state β viewType other : Type}
  (evaluation : NodeEvaluation Γ α state β viewType)
  (f : viewType → other)
  : NodeEvaluation Γ α state β other :=
  { evaluation with view := f evaluation.view }

def NodeEvaluation.closed
  {Γ : Context}
  {α state β : Type}
  (evaluation : NodeEvaluation Γ α state β (Hollow 0))
  : NodeEvaluation Γ α state β :=
  evaluation.mapView (· #v[])

def renderCollection
  {Γ : Context}
  {α β : Type}
  {views : Nat}
  (display : CollectionDisplay Γ α β views)
  (value : α)
  (env : Env Γ)
  (items : List (Item β))
  (label : String)
  (rowViews : List (Vector Display.View views))
  (content : List Display.View)
  (messages : List Message)
  : Display.View :=
  match display with
  | .list =>
    let rows := items.zipWith (fun item row => .keyed item.id row[0]) rowViews
    .list label (rows ++ content) messages
  | .table headers rowLabel selected =>
    let rows := items.mapFinIdx fun index item bound (cells : Vector Display.View views) =>
      let rowEnv := Env.row items ⟨index, bound⟩ env
      ({ key := item.id
         label := rowLabel.eval item.value rowEnv
         selected := selected.map (·.eval item.value rowEnv)
         cells := cells.toList } : Display.TableRow)
    .table label (headers.eval value env).toList (rows.zipWith (· ·) rowViews) (.ofList content)
      messages

mutual
def evaluateNode
  {Γ : Context}
  {α state β : Type}
  {holes : Nat}
  (component : ComponentNode Γ α state β holes)
  (value : α)
  (env : Env Γ)
  (ambient : Ambient)
  (locals : state)
  (target : Display.Target)
  (location : ErasedLocation)
  (disabled : Bool := false)
  : NodeEvaluation Γ α state β (Hollow holes) :=
  match component with
  | .field path label widget evidence =>
    let location := location ++ path.erase
    let current := path.get value
    let control := editor widget current (evidenceOf widget value current evidence) target location
      (label.eval value env) disabled (ambient.messagesAt location)
    { output := ()
      locals := ()
      view := fun _ => .control control
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some input := argument | throw (.decode (.clientBug .missingArgument))
          match input with
          | .pick picked => match evidence with
            | .supported slot =>
              let updated ← MonadExcept.ofExcept ((readPick slot.read picked).mapError .decode)
              return {
                value := slot.path.set (some picked) (path.set updated value)
                state := env
                locals := () }
            | .unsupported => throw (.decode (.clientBug .noEvidence))
          | .text _
          | .boolean _
          | .texts _
          | .search _
          | .choose _ =>
            let updated ← MonadExcept.ofExcept ((Input.decode widget input).mapError .decode)
            return {
              value := path.set updated value
              state := env
              locals := () }
        | _ => absent }
  | .computed label computation =>
    { output := ()
      locals := ()
      view := fun _ => .computed (label.eval value env) (computation.eval value env)
      requests := []
      apply := fun _ _ => absent }
  | .button caption action =>
    { output := ()
      locals := ()
      view := fun _ => .control {
        key := .press target.indices location
        target, location, disabled
        label := caption.eval value env
        input := .action
        messages := [] }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          noArgument argument ()
          match ← (action.run value env).run with
          | .ok updated => pure updated
          | .error collision => throw (.idCollision collision.id)
        | _ => absent }
  | .tabBar (n := n) label active tabs =>
    { output := ()
      locals := ()
      view := fun _ => .control {
        key := .tab target.indices location
        target, location, disabled
        label := label.eval value env
        input := .tabs (active.get env).val (tabs.eval value env).toList
        messages := [] }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some (.text chosen) := argument | throw (.decode (.clientBug (.wrongArgument "text")))
          let some index := chosen.toNat? | throw (.decode (.clientBug .unknownOption))
          if h : index < n then
            return { value, state := active.set ⟨index, h⟩ env, locals := () }
          throw (.decode (.clientBug .unknownOption))
        | _ => absent }
  | .withAvailability availability body =>
    let availability := availability.eval value env
    let body := evaluateNode body value env ambient locals target location
      (disabled || availability != .enabled)
    { output := body.output
      locals := body.locals
      view := fun content => if availability == .hidden then .hidden else body.view content
      requests := if availability == .hidden then [] else body.requests
      apply := fun route argument => match availability with
        | .hidden => throw (.invalid .hidden)
        | .disabled => throw (.invalid .disabled)
        | .enabled => body.apply route argument }
  | .select (decidableEq := _) (key := _) path label options selected =>
    let options := (options.eval value env).options
    let selected := selected (path.get value)
    let location := location ++ path.erase
    let shown := if options.any (·.key == selected) then Key.encode selected else ""
    let control : Display.Control := {
      key := .select location
      target, location, disabled
      label := label.eval value env
      messages := ambient.messagesAt location
      input := .choice shown
        (options.map fun option => { value := Key.encode option.key, label := option.label }) }
    { output := ()
      locals := ()
      view := fun _ => .control control
      requests := []
      apply := fun route argument => do
        if disabled then throw (.invalid .disabled)
        match route, argument with
        | [], some (.text key) =>
          let some option := (Key.decode key).bind fun key => options.find? (·.key == key)
            | throw (.invalid (.unavailableBranch key))
          if option.key == selected then return { value, state := env, locals := () }
          return {
            value := path.set option.start value
            state := env
            locals := () }
        | [], some _ => throw (.decode (.clientBug (.wrongArgument "an option")))
        | [], none => throw (.decode (.clientBug .missingArgument))
        | _, _ => absent }
  | .lookup (toJson := _) path label search =>
    let location := location ++ path.erase
    let search := search.eval value env
    let status (text : String) := (search text).resolve ambient.cache
    let control : Display.Control := {
      key := .edit location
      target, location, disabled
      label := label.eval value env
      messages := ambient.messagesAt location
      input := .lookup ((path.get value).map option)
        (locals.map fun text => { text, results := searchResults (status text) }) }
    { output := ()
      locals
      view := fun _ => .control control
      requests := (locals.bind (search · |>.request?)).toList
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          match argument with
          | some (.search text) => return { value, state := env, locals := text }
          | some (.choose none) => return { value := path.set none value, state := env, locals := none }
          | some (.choose (some key)) =>
            let found := match locals.map status with
              | some (.ready results) => results.found.find? (Reference.key · == key)
              | some .loading
              | some (.failed _)
              | none => none
            let some reference := found | throw (.invalid (.unlistedMatch key))
            return { value := path.set (some reference) value, state := env, locals := none }
          | some (.text _)
          | some (.boolean _)
          | some (.texts _)
          | some (.pick _) => throw (.decode (.clientBug (.wrongArgument "a search or a choice")))
          | none => throw (.decode (.clientBug .missingArgument))
        | _ => absent }
  | .output computation =>
    { output := computation.eval value env
      locals := ()
      view := fun _ => .hidden
      requests := []
      apply := fun _ _ => absent }
  | .issues =>
    { output := Diagnostic.issues ambient.diagnostics location
      locals := ()
      view := fun _ => .hidden
      requests := []
      apply := fun _ _ => absent }
  | .reports path =>
    { output := Message.reports (ambient.messagesAt (location ++ path.erase))
      locals := ()
      view := fun _ => .hidden
      requests := []
      apply := fun _ _ => absent }
  | .statusMarker reports =>
    { output := ()
      locals := ()
      view := fun _ => .marker (reports.eval value env)
      requests := []
      apply := fun _ _ => absent }
  | .zoom? computation body =>
    let path? := computation.eval value env
    match path?, path?.bind (·.get? value) with
    | none, _
    | _, none =>
      { output := none
        locals
        view := fun _ => .hidden
        requests := []
        apply := fun _ _ => absent }
    | some path, some focused =>
      let body := evaluateNode body focused env ambient locals target (location ++ path.erase)
        disabled
      { output := some body.output
        locals := body.locals
        view := body.view
        requests := body.requests
        apply := fun route argument => do
          let updated ← body.apply route argument
          return updated.mapValue (fun focused => path.set focused value) }
  | .zoom path body =>
    let body := evaluateNode body (path.get value) env ambient locals target
      (location ++ path.erase) disabled
    { body with
      apply := fun route argument => do
        let updated ← body.apply route argument
        return updated.mapValue (fun focused => path.set focused value) }
  | .load (inst := _inst) (source := source) (body := body) .. =>
    let source := source.eval value env
    let status := source.resolve ambient.cache
    let body := evaluateNode (body status) value env ambient
      (locals.at status (body status).initialState) target location disabled
    { output := body.output
      locals := ⟨status, body.locals⟩
      view := body.view
      requests := source.request?.toList ++ body.requests
      apply := fun route argument => do
        let updated ← body.apply route argument
        return updated.mapLocals (fun state => ⟨status, state⟩) }
  | .present body =>
    (evaluatePresentation body value env ambient locals target location disabled
      (nomatch ·)).mapView
      fun views _ => views[0]
  | .collection path label row display =>
    let collection := path.get value
    let items := collection.entries
    let location := location ++ path.erase
    let rows := items.mapFinIdx fun index item bound =>
      evaluatePresentation row item.value (Env.row items ⟨index, bound⟩ env) ambient
        (locals.getD item.id row.initialState) (target.child index)
        (location ++ [.item item.id])
        disabled (nomatch ·)
    let states := Std.HashMap.ofList <|
      items.zipWith (fun item row => (item.id, row.locals)) rows
    let render views (content : Vector (List Display.View) 1) :=
      renderCollection display value env items (label.eval value env) views content[0]
        (ambient.messagesAt location)
    { output := rows.map (·.output)
      locals := states
      view := render (rows.map (·.view))
      requests := rows.flatMap (·.requests)
      apply := fun route argument => match route with
        | index :: rest => do
          let some row := rows[index]? | absent
          let some item := items[index]? | absent
          let updated ← row.apply rest argument
          let env := updated.state.tail.tail
          if updated.state.tail.value then
            return {
              value := path.set (collection.eraseAt index) value
              state := env
              locals := states.erase item.id }
          return { updated with
            value := path.set (collection.modifyAt index fun _ => updated.value) value
            state := env
            locals := states.insert item.id updated.locals }
        | _ => absent }

def evaluatePresentation
  {Δ : ViewContext}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode Δ Γ α state β views)
  (value : α)
  (env : Env Γ)
  (ambient : Ambient)
  (locals : state)
  (target : Display.Target)
  (location : ErasedLocation)
  (disabled : Bool)
  (presentations : Presentations Δ)
  : NodeEvaluation Γ α state β (Vector Display.View views) :=
  match presentation with
  | .layout output arrangement =>
    let layouts := arrangement.eval value env
    { output := output.eval value env
      locals := ()
      view := layouts.map (renderLayout fun view => (presentations view).view)
      requests := []
      apply := fun _ _ => absent }
  | .own (holes := owns) component body =>
    let child := evaluateNode component value env ambient locals.producer (target.child 0)
      location disabled
    let presentations : Presentations (owns :: Δ) := fun {holes} view => match holes, view with
      | _, .here => ⟨child.view⟩
      | _, .there view => presentations view
    let body := evaluatePresentation body value (Env.cons child.output env) ambient
      locals.consumers (target.child 1) location disabled presentations
    observed child body body.view
  | .bind _ body =>
    bound locals.value <| evaluatePresentation body value (Env.cons locals.value env) ambient
      locals.tail (target.child 0) location disabled presentations

end

def evaluate
  {Γ : Context}
  {α β : Type}
  (component : Model.Component Γ α β)
  (value : α)
  (cache : HttpRequest.Cache)
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  (diagnostics : List Diagnostic := [])
  : Evaluated Γ α component.LocalState β :=
  let ambient := Ambient.of cache diagnostics
  let evaluated := (evaluateNode component.node value env ambient locals {} []).closed
  { toNodeEvaluation := { evaluated with view := evaluated.view.dedupe }
    toAmbient := ambient
    value, env }

def Evaluated.applyKey
  {Γ : Context}
  {α state β : Type}
  (evaluated : Evaluated Γ α state β)
  (key : ControlKey)
  (argument : Option Input)
  : StateT Supply (Except ActionError) (ComponentUpdate Γ α state) := do
  let some control := evaluated.view.controls.find? (·.key == key) | absent
  evaluated.apply control.target.indices argument

structure Rendered where
  view : Display.View
  controls : List Display.Control

def render
  {Γ : Context}
  {α β : Type}
  (component : Model.Component Γ α β)
  (value : α)
  (cache : HttpRequest.Cache)
  (errors : List Diagnostic := [])
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : Rendered :=
  let view := (evaluate component value cache env locals errors).view
  ⟨view, view.controls⟩

def decodeKey
  {Γ : Context}
  {α β : Type}
  (component : Model.Component Γ α β)
  (cache : HttpRequest.Cache)
  (value : α)
  (key : ControlKey)
  (argument : Option Input)
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : StateT Supply (Except ActionError) (ComponentUpdate Γ α component.LocalState) :=
  (evaluate component value cache env locals).applyKey key argument

end Forms.Runtime.ModelView

namespace Forms.Model

def Component.evaluate
  {Γ : Context}
  {α β : Type}
  (component : Component Γ α β)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache := {})
  (locals : component.LocalState := component.initialState)
  (diagnostics : List Diagnostic := [])
  : Runtime.ModelView.Evaluated Γ α component.LocalState β :=
  Runtime.ModelView.evaluate component value cache env locals diagnostics

end Forms.Model
