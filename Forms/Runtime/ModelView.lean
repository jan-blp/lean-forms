module

public import Forms.Model.Component.LocalState
public import Forms.Model.Invocation
public import Forms.Runtime.Input
public import Forms.Runtime.Display

@[expose] public section
namespace Forms.Runtime.ModelView
open Forms.Model

def editor
  {α : Type}
  (widget : Model.Editor α)
  (value : α)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  (errors : List Feedback.Error)
  : Display.Control :=
  let input : Display.Editor := match widget with
    | .formatted format => .text format.kind (format.print value)
    | .checkbox => .checkbox value
    | .choices (key := _) { options, .. } selected _ =>
      .choices (value.1.map (Key.encode ∘ selected))
        (options.map fun option => { value := Key.encode option.key, label := option.label })
  { key := .edit location, target, label, disabled, location, input
    messages := Feedback.messages errors location }

def location {α : Type} {value : α} : Model.Location value → Feedback.Location
  | .self => []
  | .field (fields := _) f rest => .field (Fields.key f) :: location rest
  | .constructor (constructors := _) c rest => .constructor (Constructors.key c) :: location rest
  | .index position rest => .index position.val :: location rest

def error {α : Type} {value : α} (error : Model.Error value) : Feedback.Error where
  message := error.message
  targets := match error.targets with
    | .global => .global
    | .locations first rest => .locations (location first) (rest.map location)

def pathLocation {α β : Type} : Model.Path α β → Feedback.Location
  | .self => []
  | .stepField (fields := _) f rest => .field (Fields.key f) :: pathLocation rest

def partialPathLocation {α β : Type} : Model.PartialPath α β → Feedback.Location
  | .self => []
  | .empty => []
  | .field (fields := _) f rest => .field (Fields.key f) :: partialPathLocation rest
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    .constructor (Constructors.key ctor) :: partialPathLocation rest
  | .index position rest => .index position :: partialPathLocation rest

def button
  (key : ControlKey)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  : Display.Control :=
  { key, target, label, disabled, location
    input := .action }

inductive ActionError where
  | decode (error : DecodeError)
  | invalid (error : Model.InvocationError)

def noArgument {α : Type} (argument : Option Input) (invocation : α) : Except ActionError α :=
  match argument with
  | none => .ok invocation
  | some _ => .error (.decode (.clientBug .unexpectedArgument))

structure NodeEvaluation
  (Γ : Context)
  (α state β : Type)
  (viewType : Type := Display.View) where
  output : β
  locals : state
  view : viewType
  /-- Adds validation messages to the prepared view without reevaluating components. -/
  feedback : List Feedback.Error → viewType := fun _ => view
  requests : List HttpRequest
  apply : List Nat → Option Input → Except ModelView.ActionError (ComponentUpdate Γ α state)

structure Evaluated (Γ : Context) (α state β : Type) extends NodeEvaluation Γ α state β where
  value : α
  env : Env Γ
  cache : HttpRequest.Cache

def absent {α : Type} : Except ActionError α :=
  .error (.invalid .absent)

/-- A `bind` around an evaluated `body`, which stores the bound value at its head. -/
def bound
  {Γ : Context}
  {α β γ state viewType : Type}
  (stored : β)
  (body : NodeEvaluation (⟨.writable, β⟩ :: Γ) α state γ viewType)
  : NodeEvaluation Γ α (Binding β state) γ viewType where
  output := body.output
  locals := ⟨stored, body.locals⟩
  view := body.view
  feedback := body.feedback
  requests := body.requests
  apply := fun route argument => match route with
    | 0 :: rest => do
      let updated ← body.apply rest argument
      return ⟨updated.value, updated.state.tail, ⟨updated.state.value, updated.locals⟩⟩
    | _ => absent

/-- An evaluated `body` that reads `producer`'s output; routes `0` and `1` reach each. -/
def observed
  {Γ : Context}
  {α β γ producerState consumerState producerView bodyView viewType : Type}
  (producer : NodeEvaluation Γ α producerState β producerView)
  (body : NodeEvaluation (⟨.readOnly, β⟩ :: Γ) α consumerState γ bodyView)
  (view : viewType)
  (feedback : List Feedback.Error → viewType)
  : NodeEvaluation Γ α (ObservationState producerState consumerState) γ viewType where
  output := body.output
  locals := ⟨producer.locals, body.locals⟩
  view := view
  feedback := feedback
  requests := producer.requests ++ body.requests
  apply := fun route argument => match route with
    | 0 :: rest => do
      let updated ← producer.apply rest argument
      return updated.mapLocals (⟨·, body.locals⟩)
    | 1 :: rest => do
      let updated ← body.apply rest argument
      return ⟨updated.value, updated.state.tail, ⟨producer.locals, updated.locals⟩⟩
    | _ => absent

/-- A view given the content of each of its `holes`. -/
abbrev Hollow (holes : Nat) := Vector (List Display.View) holes → Display.View

/-- An owned component's view, kept until a layout places it. -/
structure Prepared (holes : Nat) where
  view : Hollow holes
  feedback : List Feedback.Error → Hollow holes

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
  { evaluation with
    view := f evaluation.view
    feedback := fun errors => f (evaluation.feedback errors) }

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
  (items : List β)
  (label : String)
  (rows : List (Vector Display.View views))
  (content : List Display.View)
  (messages : Option String)
  : Display.View :=
  match display with
  | .list => .list label (rows.map (·[0]) ++ content) messages
  | .table headers rowLabel selected =>
    let rows := (items.mapFinIdx fun index item bound =>
      let rowEnv := Env.row items ⟨index, bound⟩ env
      (rowLabel.eval item rowEnv, selected.map (·.eval item rowEnv))).zipWith
      (fun (label, selected) cells => { label, selected, cells := cells.toList }) rows
    .table label (headers.eval value env).toList rows (.ofList content) messages

mutual
def evaluateNode
  {Γ : Context}
  {α state β : Type}
  {holes : Nat}
  (component : ComponentNode Γ α state β holes)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool := false)
  : NodeEvaluation Γ α state β (Hollow holes) :=
  match component with
  | .field path label widget =>
    let location := location ++ pathLocation path
    let control := editor widget (path.get value) target location (label.eval value env) disabled []
    { output := ()
      locals := ()
      view := fun _ => .control control
      feedback := fun errors _ =>
        .control { control with messages := Feedback.messages errors location }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some input := argument | throw (.decode (.clientBug .missingArgument))
          let updated ← (Input.decode widget input).mapError .decode
          return ⟨path.set updated value, env, ()⟩
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
        input := .action }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          noArgument argument ()
          return action.run value env
        | _ => absent }
  | .tabBar (n := n) label active tabs =>
    { output := ()
      locals := ()
      view := fun _ => .control {
        key := .tab target.indices location
        target, location, disabled
        label := label.eval value env
        input := .tabs (active.get env).val (tabs.eval value env).toList }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some (.text chosen) := argument | throw (.decode (.clientBug (.wrongArgument "text")))
          let some index := chosen.toNat? | throw (.decode (.clientBug .unknownOption))
          if h : index < n then return ⟨value, active.set ⟨index, h⟩ env, ()⟩
          throw (.decode (.clientBug .unknownOption))
        | _ => absent }
  | .withAvailability availability body =>
    let availability := availability.eval value env
    let body := evaluateNode body value env cache locals target location (disabled || availability != .enabled)
    { output := body.output
      locals := body.locals
      view := fun content => if availability == .hidden then .hidden else body.view content
      feedback := fun errors content =>
        if availability == .hidden then .hidden else body.feedback errors content
      requests := if availability == .hidden then [] else body.requests
      apply := fun route argument => match availability with
        | .hidden => .error (.invalid .hidden)
        | .disabled => .error (.invalid .disabled)
        | .enabled => body.apply route argument }
  | .select (decidableEq := _) (key := _) path label options selected =>
    let options := (options.eval value env).options
    let selected := selected (path.get value)
    let location := location ++ pathLocation path
    let shown := if options.any (·.key == selected) then Key.encode selected else ""
    let control : Display.Control := {
      key := .select location
      target, location, disabled
      label := label.eval value env
      input := .choice shown
        (options.map fun option => { value := Key.encode option.key, label := option.label }) }
    { output := ()
      locals := ()
      view := fun _ => .control control
      feedback := fun errors _ =>
        .control { control with messages := Feedback.messages errors location }
      requests := []
      apply := fun route argument => do
        if disabled then throw (.invalid .disabled)
        match route, argument with
        | [], some (.text key) =>
          let some option := (Key.decode key).bind fun key => options.find? (·.key == key)
            | throw (.invalid (.unavailableBranch key))
          if option.key == selected then return ⟨value, env, ()⟩
          return ⟨path.set option.start value, env, ()⟩
        | [], some _ => throw (.decode (.clientBug (.wrongArgument "an option")))
        | [], none => throw (.decode (.clientBug .missingArgument))
        | _, _ => absent }
  | .output computation =>
    { output := computation.eval value env
      locals := ()
      view := fun _ => .hidden
      requests := []
      apply := fun _ _ => absent }
  | .focus computation body =>
    let path := computation.eval value env
    match path.get? value with
    | none =>
      { output := none
        locals
        view := fun _ => .hidden
        requests := []
        apply := fun _ _ => absent }
    | some focused =>
      let body := evaluateNode body focused env cache locals target (location ++ partialPathLocation path) disabled
      { output := some body.output
        locals := body.locals
        view := body.view
        feedback := body.feedback
        requests := body.requests
        apply := fun route argument => do
          let updated ← body.apply route argument
          return updated.mapValue (fun focused => path.set focused value) }
  | .load (inst := _inst) (source := source) (body := body) .. =>
    let source := source.eval value env
    let status := source.resolve cache
    let body := evaluateNode (body status) value env cache (locals.at status (body status).initialState) target location disabled
    { output := body.output
      locals := ⟨status, body.locals⟩
      view := body.view
      feedback := body.feedback
      requests := source.request?.toList ++ body.requests
      apply := fun route argument => do
        let updated ← body.apply route argument
        return updated.mapLocals (fun state => ⟨status, state⟩) }
  | .present body =>
    (evaluatePresentation body value env cache locals target location disabled (nomatch ·)).mapView
      fun views _ => views[0]
  | .collection path label row display =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapFinIdx fun index item bound =>
      evaluatePresentation row item (Env.row items ⟨index, bound⟩ env) cache
        (locals[index]?.getD row.initialState) (target.child index) (location ++ [.index index])
        disabled (nomatch ·)
    let states := rows.map (·.locals)
    let render views errors (content : Vector (List Display.View) 1) :=
      renderCollection display value env items (label.eval value env) views content[0]
        (Feedback.messages errors location)
    { output := rows.map (·.output)
      locals := states
      view := render (rows.map (·.view)) []
      feedback := fun errors => render (rows.map fun row => row.feedback errors) errors
      requests := rows.flatMap (·.requests)
      apply := fun route argument => match route with
        | index :: rest => do
          let some row := rows[index]? | absent
          let updated ← row.apply rest argument
          let env := updated.state.tail.tail
          if updated.state.tail.value then
            return ⟨path.set (items.eraseIdx index) value, env, states.eraseIdx index⟩
          return ⟨path.set (items.set index updated.value) value, env,
            states.set index updated.locals⟩
        | _ => absent }

def evaluatePresentation
  {slots : List Nat}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode slots Γ α state β views)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool)
  (presentations : Presentations slots)
  : NodeEvaluation Γ α state β (Vector Display.View views) :=
  match presentation with
  | .layout output arrangement =>
    let layouts := arrangement.eval value env
    { output := output.eval value env
      locals := ()
      view := layouts.map (renderLayout fun slot => (presentations slot).view)
      feedback := fun errors =>
        layouts.map (renderLayout fun slot => (presentations slot).feedback errors)
      requests := []
      apply := fun _ _ => absent }
  | .own (holes := owns) component body =>
    let owned := evaluateNode component value env cache locals.producer (target.child 0) location
      disabled
    let presentations : Presentations (owns :: slots) := fun {holes} slot => match holes, slot with
      | _, .here => ⟨owned.view, owned.feedback⟩
      | _, .there slot => presentations slot
    let body := evaluatePresentation body value (Env.cons owned.output env) cache locals.consumers
      (target.child 1) location disabled presentations
    observed owned body body.view body.feedback
  | .bind _ body =>
    bound locals.value <| evaluatePresentation body value (Env.cons locals.value env) cache locals.tail
      (target.child 0) location disabled presentations

end

def evaluate
  {Γ : Context}
  {α β : Type}
  (component : Model.Component Γ α β)
  (value : α)
  (cache : HttpRequest.Cache)
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : Evaluated Γ α component.LocalState β :=
  let evaluated := (evaluateNode component.node value env cache locals {} []).closed
  { toNodeEvaluation := { evaluated with
      view := evaluated.view.dedupe
      feedback := fun errors => (evaluated.feedback errors).dedupe }
    value, env, cache }

def Evaluated.applyKey
  {Γ : Context}
  {α state β : Type}
  (evaluated : Evaluated Γ α state β)
  (key : ControlKey)
  (argument : Option Input := none)
  : Except ActionError (ComponentUpdate Γ α state) := do
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
  (errors : List Feedback.Error := [])
  (env : Env Γ)
  (locals : component.LocalState := component.initialState)
  : Rendered :=
  let evaluated := evaluate component value cache env locals
  let view := if errors.isEmpty then evaluated.view else evaluated.feedback errors
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
  : Except ActionError (ComponentUpdate Γ α component.LocalState) :=
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
  : Runtime.ModelView.Evaluated Γ α component.LocalState β :=
  Runtime.ModelView.evaluate component value cache env locals

end Forms.Model
