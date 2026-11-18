module

public import Forms.Model.Component.LocalState
public import Forms.Model.Invocation
public import Forms.Runtime.Input
public import Forms.Runtime.Display

@[expose] public section
namespace Forms.Runtime.ModelView
open Forms.Model

def editorInput {α : Type} : Model.Editor α → α → Display.Editor
  | .formatted format, value => .text format.kind (format.print value)
  | .checkbox, value => .checkbox value
  | .choices (key := _) { options, .. } selected, value =>
    .choices (value.map (Key.encode ∘ selected))
      (options.map fun option => { value := Key.encode option.key, label := option.label })
  | .refine editor print .., value => editorInput editor (print value)

def editor
  {α : Type}
  (widget : Model.Editor α)
  (value : α)
  (target : Display.Target)
  (location : ErasedLocation)
  (label : String)
  (disabled : Bool)
  (messages : List Message)
  : Display.Control :=
  { key := .edit location, target, label, disabled, location, messages
    input := editorInput widget value }

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
  kind :=
    let state : Diagnostic.ReportState := match report.status with
      | .unresolved => .unresolved
      | .resolved => .resolved
    .report state <| match report.origin with
      | .form => false
      | .server => !checked
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

inductive ActionError where
  | decode (error : DecodeError)
  | invalid (error : Model.InvocationError)

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

abbrev Presentations (slots : List Nat) := {holes : Nat} → Slot slots holes → Prepared holes

mutual
def renderLayout
  {slots : List Nat}
  (views : {holes : Nat} → Slot slots holes → Hollow holes)
  : Layout slots → Display.View
  | .place slot => views slot #v[]
  | .fill slot contents => views slot (renderFills views contents)
  | .group label children => .stack label (renderAll views children)

def renderAll
  {slots : List Nat}
  (views : {holes : Nat} → Slot slots holes → Hollow holes)
  : List (Layout slots) → List Display.View
  | [] => []
  | child :: rest => renderLayout views child :: renderAll views rest

def renderFills
  {slots : List Nat}
  {holes : Nat}
  (views : {holes : Nat} → Slot slots holes → Hollow holes)
  : Fills slots holes → Vector (List Display.View) holes
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
  [HasUuid β]
  (display : CollectionDisplay Γ α β views)
  (value : α)
  (env : Env Γ)
  (items : List β)
  (label : String)
  (rowViews : List (Vector Display.View views))
  (content : List Display.View)
  (messages : List Message)
  : Display.View :=
  match display with
  | .list =>
    let rows := items.zipWith (fun item row => .keyed (HasUuid.id item) row[0]) rowViews
    .list label (rows ++ content) messages
  | .table headers rowLabel selected =>
    let rows := items.mapFinIdx fun index item bound (cells : Vector Display.View views) =>
      let rowEnv := Env.row items ⟨index, bound⟩ env
      ({ key := HasUuid.id item
         label := rowLabel.eval item rowEnv
         selected := selected.map (·.eval item rowEnv)
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
  | .field path label widget =>
    let location := location ++ path.erase
    let control := editor widget (path.get value) target location
      (label.eval value env) disabled (ambient.messagesAt location)
    { output := ()
      locals := ()
      view := fun _ => .control control
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some input := argument | throw (.decode (.clientBug .missingArgument))
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
          action.run value env
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
  | .collection (hasUuid := _) path label row display =>
    let items := path.get value
    let location := location ++ path.erase
    let rows := items.mapFinIdx fun index item bound =>
      evaluatePresentation row item (Env.row items ⟨index, bound⟩ env) ambient
        (locals.getD (HasUuid.id item) row.initialState) (target.child index)
        (location ++ [.item (HasUuid.id item)])
        disabled (nomatch ·)
    let states := Std.HashMap.ofList <|
      items.zipWith (fun item row => (HasUuid.id item, row.locals)) rows
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
              value := path.set (items.eraseIdx index) value
              state := env
              locals := states.erase (HasUuid.id item) }
          return { updated with
            value := path.set (items.set index updated.value) value
            state := env
            locals := states.insert (HasUuid.id item) updated.locals }
        | _ => absent }

def evaluatePresentation
  {slots : List Nat}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode slots Γ α state β views)
  (value : α)
  (env : Env Γ)
  (ambient : Ambient)
  (locals : state)
  (target : Display.Target)
  (location : ErasedLocation)
  (disabled : Bool)
  (presentations : Presentations slots)
  : NodeEvaluation Γ α state β (Vector Display.View views) :=
  match presentation with
  | .layout output arrangement =>
    let layouts := arrangement.eval value env
    { output := output.eval value env
      locals := ()
      view := layouts.map (renderLayout fun slot => (presentations slot).view)
      requests := []
      apply := fun _ _ => absent }
  | .own (holes := owns) component body =>
    let owned := evaluateNode component value env ambient locals.producer (target.child 0)
      location disabled
    let presentations : Presentations (owns :: slots) := fun {holes} slot => match holes, slot with
      | _, .here => ⟨owned.view⟩
      | _, .there slot => presentations slot
    let body := evaluatePresentation body value (Env.cons owned.output env) ambient
      locals.consumers (target.child 1) location disabled presentations
    observed owned body body.view
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
