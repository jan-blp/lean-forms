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
    | .text => .text value
    | .natural => .natural value
    | .checkbox => .checkbox value
  { key := .edit location, target, label, disabled, location, input
    messages := Feedback.messages errors location }

def location {α : Type} {value : α} : Model.Location value → Feedback.Location
  | .self => []
  | @Model.Location.field _ _ inst _ f rest => .field (@Fields.key _ inst _ f) :: location rest
  | @Model.Location.constructor _ _ inst _ c rest => .constructor (@Constructors.key _ inst _ c) :: location rest
  | .index position rest => .index position.val :: location rest

def error {α : Type} {value : α} (error : Model.Error value) : Feedback.Error where
  message := error.message
  targets := match error.targets with
    | .global => .global
    | .locations first rest => .locations (location first) (rest.map location)

def pathLocation {α β : Type} : Model.Path α β → Feedback.Location
  | .self => []
  | @Model.Path.stepField _ _ _ inst f rest => .field (@Fields.key _ inst _ f) :: pathLocation rest

def partialPathLocation {α β : Type} : Model.PartialPath α β → Feedback.Location
  | .self => []
  | .empty => []
  | @Model.PartialPath.field _ _ _ inst f rest =>
    .field (@Fields.key _ inst _ f) :: partialPathLocation rest
  | @Model.PartialPath.constructor _ _ _ inst _ ctor rest =>
    .constructor (@Constructors.key _ inst _ ctor) :: partialPathLocation rest
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

/-- Lexical binder addresses used only for frontend control keys. -/
abbrev WireScopes := Nat → List Nat

/-- One view for each statically named column. -/
inductive CellViews : List String → Type where
  | nil : CellViews []
  | cons {header : String} {rest : List String}
      (view : Display.View)
      (tail : CellViews rest)
      : CellViews (header :: rest)

def CellViews.append
  {first second : List String}
  (left : CellViews first)
  (right : CellViews second)
  : CellViews (first ++ second) :=
  match left with
  | .nil => right
  | .cons view tail => .cons view (tail.append right)

def CellViews.toList {headers : List String} : CellViews headers → List Display.View
  | .nil => []
  | .cons view tail => view :: tail.toList

def CellViews.hidden : (headers : List String) → CellViews headers
  | [] => .nil
  | _ :: rest => .cons .hidden (hidden rest)

structure RowSelector where
  current : RowSelection
  scope : List Nat

@[reducible] def ViewFor : (layout : Layout) → layout.Headers → Type
  | .block, _ => Display.View
  | .cells, headers => CellViews headers

def combineViews
  {layout : Layout}
  {first second : layout.Headers}
  (left : ViewFor layout first)
  (right : ViewFor layout second)
  : ViewFor layout (layout.appendHeaders first second) :=
  match layout with
  | .block => .stack none [left, right]
  | .cells => left.append right

def hiddenView
  (layout : Layout)
  (headers : layout.Headers)
  : ViewFor layout headers :=
  match layout with
  | .block => .hidden
  | .cells => CellViews.hidden headers

def collectionView
  (layout : Layout)
  (headers : layout.Headers)
  (views : List (ViewFor layout headers))
  (label itemLabel : String)
  (target : Display.Target)
  (location : Feedback.Location)
  (selection : Option RowSelector)
  (errors : List Feedback.Error)
  (disabled : Bool)
  : Display.View :=
  let add := ModelView.button (.add location) target location s!"Add {itemLabel.toLower}" disabled
  match layout, headers, views with
  | .block, _, views =>
    let views := views.mapIdx fun index view =>
      let remove := ModelView.button (.remove (location ++ [.index index])) ((target.child index).child 1)
        (location ++ [.index index]) "Remove" disabled
      Display.View.stack (some s!"{itemLabel} {index + 1}") [view, .control remove]
    .list label (views ++ [.control add]) (Feedback.messages errors location)
  | .cells, headers, views =>
    let views := views.mapIdx fun index view =>
      let remove := ModelView.button (.remove (location ++ [.index index])) ((target.child index).child 1)
        (location ++ [.index index]) "Remove" disabled
      let selected := selection.map fun selection => selection.current == .row index
      let actions := match selection with
        | none => Display.View.control remove
        | some selection =>
          let select := button (.selectRow selection.scope index) ((target.child index).child 2)
            (location ++ [.index index]) (if selected.getD false then "Selected" else "Select") disabled
          .stack none [.control select, .control remove]
      ({ label := s!"{itemLabel} {index + 1}"
         selected
         cells := view.toList ++ [actions] } : Display.TableRow)
    .table label (headers ++ ["Actions"]) views (.control add) (Feedback.messages errors location)

inductive ActionError where
  | decode (error : DecodeError)
  | invalid (error : Model.InvocationError)

def noArgument {α : Type} (argument : Option Input) (invocation : α) : Except ActionError α :=
  match argument with
  | none => .ok invocation
  | some _ => .error (.decode (.clientBug .unexpectedArgument))

def checkedIndex (index length : Nat) : Except ActionError (Fin length) :=
  if h : index < length then .ok ⟨index, h⟩ else .error (.invalid (.indexOutOfBounds index length))

/-- A result for one fixed model, environment, cache, and set of private states. -/
structure NodeEvaluation
  (Γ : Context)
  (α state β : Type)
  (layout : Layout := .block)
  (headers : layout.Headers := layout.emptyHeaders) where
  output : β
  locals : state
  view : ViewFor layout headers
  /-- Adds validation messages to the prepared view without reevaluating components. -/
  feedback : List Feedback.Error → ViewFor layout headers := fun _ => view
  requests : List HttpRequest
  apply : List Nat → Option Input → Except ModelView.ActionError (ComponentUpdate Γ α state)

structure Evaluated (Γ : Context) (α state β : Type) extends NodeEvaluation Γ α state β where
  value : α
  env : Env Γ
  cache : HttpRequest.Cache

structure EvaluatedChildren (Γ : Context) (α state : Type) where
  locals : state
  views : List Display.View
  feedback : List Feedback.Error → List Display.View
  requests : List HttpRequest
  apply : Nat → List Nat → Option Input → Except ActionError (ComponentUpdate Γ α state)

structure EvaluatedBranches (Γ : Context) (α state : Type) where
  locals : state
  view : Option Display.View
  feedback : List Feedback.Error → Option Display.View
  selected : String
  options : List Display.ChoiceOption
  requests : List HttpRequest
  apply : Nat → List Nat → Option Input → Except ActionError (ComponentUpdate Γ α state)
  select : String → Except ActionError (ComponentUpdate Γ α state)

def absent {α : Type} : Except ActionError α :=
  .error (.invalid .absent)

mutual
/-- Evaluates outputs while building the view, requests, and action routes. -/
def evaluateNode
  {layout : Layout}
  {headers : layout.Headers}
  {Γ : Context}
  {α state β : Type}
  (component : ComponentNode layout headers Γ α state β)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool := false)
  : NodeEvaluation Γ α state β layout headers :=
  match component with
  | .field path label widget =>
    let location := location ++ pathLocation path
    let control := editor widget (path.get value) target location label disabled []
    { output := ()
      locals := ()
      view := .control control
      feedback := fun errors => .control { control with messages := Feedback.messages errors location }
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
      view := .computed label (computation.eval value env)
      requests := []
      apply := fun _ _ => absent }
  | .button label action =>
    { output := ()
      locals := ()
      view := .control { key := .press target.indices location, target, location, label, disabled, input := .action }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          noArgument argument ()
          return ⟨value, action.run value env, ()⟩
        | _ => absent }
  | .groupOf label children =>
    let children := evaluateChildren children value env cache locals scopes target location disabled 0
    { output := ()
      locals := children.locals
      view := .stack (some label) children.views
      feedback := fun errors => .stack (some label) (children.feedback errors)
      requests := children.requests
      apply := fun route argument => match route with
        | index :: rest => children.apply index rest argument
        | _ => absent }
  | .labeled label body =>
    let body := evaluateNode body value env cache locals scopes target location disabled
    { body with
      view := .stack (some label) [body.view]
      feedback := fun errors => .stack (some label) [body.feedback errors] }
  | .mapOutput f body =>
    let body := evaluateNode body value env cache locals scopes target location disabled
    { output := f body.output
      locals := body.locals
      view := body.view
      feedback := body.feedback
      requests := body.requests
      apply := body.apply }
  | .withAvailability availability body =>
    let availability := availability.eval value env
    let body := evaluateNode body value env cache locals scopes target location (disabled || availability != .enabled)
    { output := body.output
      locals := body.locals
      view := if availability == .hidden then hiddenView layout headers else body.view
      feedback := fun errors => if availability == .hidden then hiddenView layout headers else body.feedback errors
      requests := if availability == .hidden then [] else body.requests
      apply := fun route argument => match availability with
        | .hidden => .error (.invalid .hidden)
        | .disabled => .error (.invalid .disabled)
        | .enabled => body.apply route argument }
  | .choiceOf path label branches =>
    let current := path.get value
    let location := location ++ pathLocation path
    let branches := evaluateBranches branches current env cache locals scopes target location disabled 0
    let control : Display.Control := {
      key := .select location
      target, location, label, disabled
      input := .choice branches.selected branches.options }
    { output := ()
      locals := branches.locals
      view := match branches.view with
        | none => .control control
        | some body => .stack none [.control control, body]
      feedback := fun errors =>
        let control := { control with messages := Feedback.messages errors location }
        match branches.feedback errors with
        | none => .control control
        | some body => .stack none [.control control, body]
      requests := branches.requests
      apply := fun route argument => do
        if disabled then throw (.invalid .disabled)
        let updated ← match route with
          | [] => match argument with
            | some (.text key) => branches.select key
            | some _ => .error (.decode (.clientBug (.wrongArgument "an option")))
            | none => .error (.decode (.clientBug .missingArgument))
          | index :: rest => branches.apply index rest argument
        return updated.mapValue (fun updated => path.set updated value) }
  | .output computation =>
    { output := computation.eval value env
      locals := ()
      view := hiddenView layout layout.emptyHeaders
      requests := []
      apply := fun _ _ => absent }
  | .sequence first second =>
    let first := evaluateNode first value env cache locals.value scopes (target.child 0) location disabled
    let second := evaluateNode second value env cache locals.tail scopes (target.child 1) location disabled
    { output := second.output
      locals := ⟨first.locals, second.locals⟩
      view := combineViews first.view second.view
      feedback := fun errors => combineViews (first.feedback errors) (second.feedback errors)
      requests := first.requests ++ second.requests
      apply := fun route argument => match route with
        | 0 :: rest => do
          let updated ← first.apply rest argument
          return updated.mapLocals (⟨·, second.locals⟩)
        | 1 :: rest => do
          let updated ← second.apply rest argument
          return updated.mapLocals (⟨first.locals, ·⟩)
        | _ => absent }
  | .focus computation body =>
    let path := computation.eval value env
    match path.get? value with
    | none =>
      { output := none
        locals
        view := hiddenView layout headers
        requests := []
        apply := fun _ _ => absent }
    | some focused =>
      let body := evaluateNode body focused env cache locals scopes target (location ++ partialPathLocation path) disabled
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
    let body := evaluateNode (body status) value env cache (locals.at status (body status).initialState) scopes target location disabled
    { output := body.output
      locals := ⟨status, body.locals⟩
      view := body.view
      feedback := body.feedback
      requests := source.request?.toList ++ body.requests
      apply := fun route argument => do
        let updated ← body.apply route argument
        return updated.mapLocals (fun state => ⟨status, state⟩) }
  | .bind _ body =>
    let scopes := fun index => match index with
      | 0 => 1 :: target.indices
      | index + 1 => scopes index
    let body := evaluateNode body value (Env.cons locals.value env) cache locals.tail scopes (target.child 0) location disabled
    { output := body.output
      locals := ⟨locals.value, body.locals⟩
      view := body.view
      feedback := body.feedback
      requests := body.requests
      apply := fun route argument => match route with
        | 0 :: rest => do
          let updated ← body.apply rest argument
          return ⟨updated.value, updated.state.tail, ⟨updated.state.value, updated.locals⟩⟩
        | _ => absent }
  | .observe producer body =>
    let producer := evaluateNode producer value env cache locals.producer scopes (target.child 0) location disabled
    let scopes := fun index => match index with
      | 0 => 2 :: target.indices
      | index + 1 => scopes index
    let body := evaluateNode body value (Env.cons producer.output env) cache locals.consumers scopes (target.child 1) location disabled
    { output := body.output
      locals := ⟨producer.locals, body.locals⟩
      view := combineViews producer.view body.view
      feedback := fun errors => combineViews (producer.feedback errors) (body.feedback errors)
      requests := producer.requests ++ body.requests
      apply := fun route argument => match route with
        | 0 :: rest => do
          let updated ← producer.apply rest argument
          return updated.mapLocals (⟨·, body.locals⟩)
        | 1 :: rest => do
          let updated ← body.apply rest argument
          return ⟨updated.value, updated.state.tail, ⟨producer.locals, updated.locals⟩⟩
        | _ => absent }
  | .cell _ body =>
    let body := evaluateNode body value env cache locals scopes target location disabled
    { output := body.output
      locals := body.locals
      view := .cons body.view .nil
      feedback := fun errors => .cons (body.feedback errors) .nil
      requests := body.requests
      apply := body.apply }
  | .collection (layout := rowLayout) (headers := rowHeaders) path label itemLabel initial body selection =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      evaluateNode body item env cache (locals[index]?.getD body.initialState) scopes
        ((target.child index).child 0) (location ++ [.index index]) disabled
    let states := rows.map (·.locals)
    let selector := selection.map fun selected => ({ current := selected.get env, scope := scopes selected.index } : RowSelector)
    let view := collectionView rowLayout rowHeaders (rows.map (·.view)) label itemLabel target location selector [] disabled
    { output := rows.map (·.output)
      locals := states
      view
      feedback := fun errors => collectionView rowLayout rowHeaders (rows.map fun row => row.feedback errors)
        label itemLabel target location selector errors disabled
      requests := rows.flatMap (·.requests)
      apply := fun route argument => do
        if disabled then throw (.invalid .disabled)
        match route with
        | [] => do
          noArgument argument ()
          return ⟨path.set (items ++ [initial]) value, env, states ++ [body.initialState]⟩
        | [index, 1] => do
          let index ← checkedIndex index items.length
          noArgument argument ()
          let env := match selection with
            | none => env
            | some selected => selected.set ((selected.get env).remove index.val) env
          return ⟨path.set (items.eraseIdx index) value, env, states.eraseIdx index⟩
        | [index, 2] => do
          let index ← checkedIndex index items.length
          noArgument argument ()
          let some selected := selection | absent
          return ⟨value, selected.set (.row index.val) env, states⟩
        | index :: 0 :: rest => do
          let some row := rows[index]? | absent
          let updated ← row.apply rest argument
          return ⟨path.set (items.set index updated.value) value, updated.state, states.set index updated.locals⟩
        | _ => absent }

def evaluateChildren
  {Γ : Context}
  {α state : Type}
  (children : ComponentsNode Γ α state)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool)
  (index : Nat)
  : EvaluatedChildren Γ α state :=
  match children with
  | .columns columns =>
    let columns := evaluateNode columns value env cache locals scopes (target.child index) location disabled
    { locals := columns.locals
      views := columns.view.toList
      feedback := fun errors => (columns.feedback errors).toList
      requests := columns.requests
      apply := fun index route argument => match index with
        | 0 => columns.apply route argument
        | _ => absent }
  | .nil =>
    { locals := (), views := [], feedback := fun _ => [], requests := [], apply := fun _ _ _ => absent }
  | .cons head tail =>
    let head := evaluateNode head value env cache locals.value scopes (target.child index) location disabled
    let tail := evaluateChildren tail value env cache locals.tail scopes target location disabled (index + 1)
    { locals := ⟨head.locals, tail.locals⟩
      views := head.view :: tail.views
      feedback := fun errors => head.feedback errors :: tail.feedback errors
      requests := head.requests ++ tail.requests
      apply := fun index route argument => match index with
        | 0 => do
          let updated ← head.apply route argument
          return updated.mapLocals (⟨·, tail.locals⟩)
        | index + 1 => do
          let updated ← tail.apply index route argument
          return updated.mapLocals (⟨head.locals, ·⟩) }

def evaluateBranches
  {Γ : Context}
  {α state : Type}
  (branches : BranchesNode Γ α state)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool)
  (index : Nat)
  : EvaluatedBranches Γ α state :=
  match branches with
  | .nil =>
    { locals := (), view := none, feedback := fun _ => none, selected := "", options := [], requests := []
      apply := fun _ _ _ => absent
      select := fun key => .error (.invalid (.unavailableBranch key)) }
  | .cons (.mk key label inject project initial body) tail =>
    let tail := evaluateBranches tail value env cache locals.tail scopes target location disabled (index + 1)
    match project value with
    | none =>
      { locals := ⟨locals.value, tail.locals⟩
        view := tail.view
        feedback := tail.feedback
        selected := tail.selected
        options := { value := key, label } :: tail.options
        requests := tail.requests
        apply := fun index route argument => match index with
          | 0 => .error (.invalid .inactiveBranch)
          | index + 1 => do
            let updated ← tail.apply index route argument
            return updated.mapLocals (⟨locals.value, ·⟩)
        select := fun chosen =>
          if chosen == key then .ok ⟨inject initial, env, ⟨locals.value, tail.locals⟩⟩ else do
            let updated ← tail.select chosen
            return updated.mapLocals (⟨locals.value, ·⟩) }
    | some payload =>
      let head := evaluateNode body payload env cache locals.value scopes (target.child index) (location ++ [.constructor key]) disabled
      { locals := ⟨head.locals, tail.locals⟩
        view := some head.view
        feedback := fun errors => some (head.feedback errors)
        selected := key
        options := { value := key, label } :: tail.options
        requests := head.requests ++ tail.requests
        apply := fun index route argument => match index with
          | 0 => do
            let updated ← head.apply route argument
            return ⟨inject updated.value, updated.state, ⟨updated.locals, tail.locals⟩⟩
          | index + 1 => do
            let updated ← tail.apply index route argument
            return updated.mapLocals (⟨head.locals, ·⟩)
        select := fun chosen =>
          if chosen == key then .ok ⟨value, env, ⟨head.locals, tail.locals⟩⟩ else do
            let updated ← tail.select chosen
            return updated.mapLocals (⟨head.locals, ·⟩) }
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
  let evaluated := evaluateNode component.node value env cache locals (fun index => [0, index]) {} []
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
