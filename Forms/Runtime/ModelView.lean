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

def CellViews.toList {headers : List String} : CellViews headers → List Display.View
  | .nil => []
  | .cons view tail => view :: tail.toList

def CellViews.hidden : (headers : List String) → CellViews headers
  | [] => .nil
  | _ :: rest => .cons .hidden (hidden rest)

structure RowSelector where
  current : RowSelection
  scope : List Nat

def listView
  (views : List Display.View)
  (label itemLabel : String)
  (target : Display.Target)
  (location : Feedback.Location)
  (errors : List Feedback.Error)
  (disabled : Bool)
  : Display.View :=
  let add := ModelView.button (.add location) target location s!"Add {itemLabel.toLower}" disabled
  let views := views.mapIdx fun index view =>
    let remove := ModelView.button (.remove (location ++ [.index index])) ((target.child index).child 1)
      (location ++ [.index index]) "Remove" disabled
    Display.View.stack (some s!"{itemLabel} {index + 1}") [view, .control remove]
  .list label (views ++ [.control add]) (Feedback.messages errors location)

def tableView
  (headers : List String)
  (views : List (CellViews headers))
  (label itemLabel : String)
  (target : Display.Target)
  (location : Feedback.Location)
  (selection : Option RowSelector)
  (errors : List Feedback.Error)
  (disabled : Bool)
  : Display.View :=
  let add := ModelView.button (.add location) target location s!"Add {itemLabel.toLower}" disabled
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

/-- `scopes` under a binder at `target` whose body is its child `child`. -/
def WireScopes.bind (scopes : WireScopes) (target : Display.Target) (child : Nat) : WireScopes
  | 0 => child :: target.indices
  | index + 1 => scopes index

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

/-- An owned component's view, kept until a layout places it. -/
structure Prepared where
  view : Display.View
  feedback : List Feedback.Error → Display.View

abbrev Presentations (slots : Nat) := Slot slots → Prepared

mutual
def renderLayout
  {slots : Nat}
  (views : Slot slots → Display.View)
  : Layout slots → Display.View
  | .place slot => views slot
  | .group label children => .stack label (renderAll views children)

def renderAll
  {slots : Nat}
  (views : Slot slots → Display.View)
  : List (Layout slots) → List Display.View
  | [] => []
  | child :: rest => renderLayout views child :: renderAll views rest
end

/-- Shares list and table updates after their rows have been evaluated. -/
def evaluateCollection
  {Γ : Context}
  {α β γ state viewType : Type}
  (path : Path α (List β))
  (initial : β)
  (rowInitial : state)
  (rows : List (NodeEvaluation Γ β state γ viewType))
  (value : α)
  (env : Env Γ)
  (selection : Option (Var Γ RowSelection))
  (disabled : Bool)
  (render : List viewType → List Feedback.Error → Display.View)
  : NodeEvaluation Γ α (List state) (List γ) :=
  let items := path.get value
  let states := rows.map (·.locals)
  { output := rows.map (·.output)
    locals := states
    view := render (rows.map (·.view)) []
    feedback := fun errors => render (rows.map fun row => row.feedback errors) errors
    requests := rows.flatMap (·.requests)
    apply := fun route argument => do
      if disabled then throw (.invalid .disabled)
      match route with
      | [] => do
        noArgument argument ()
        return ⟨path.set (items ++ [initial]) value, env, states ++ [rowInitial]⟩
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

mutual
/-- Evaluates outputs while building the view, requests, and action routes. -/
def evaluateNode
  {Γ : Context}
  {α state β : Type}
  (component : ComponentNode Γ α state β)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool := false)
  : NodeEvaluation Γ α state β :=
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
  | .button caption action =>
    { output := ()
      locals := ()
      view := .control {
        key := .press target.indices location
        target, location, disabled
        label := caption.eval value env
        input := .action }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          noArgument argument ()
          return ⟨value, action.run value env, ()⟩
        | _ => absent }
  | .tabBar label active tabs =>
    { output := ()
      locals := ()
      view := .control {
        key := .tab target.indices location
        target, location, label, disabled
        input := .tabs (active.get env) tabs }
      requests := []
      apply := fun route argument => match route with
        | [] => do
          if disabled then throw (.invalid .disabled)
          let some (.text chosen) := argument | throw (.decode (.clientBug (.wrongArgument "text")))
          let some index := chosen.toNat? | throw (.decode (.clientBug .unknownOption))
          unless index < tabs.length do throw (.decode (.clientBug .unknownOption))
          return ⟨value, active.set index env, ()⟩
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
  | .void body =>
    let body := evaluateNode body value env cache locals scopes target location disabled
    { output := ()
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
      view := if availability == .hidden then .hidden else body.view
      feedback := fun errors => if availability == .hidden then .hidden else body.feedback errors
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
      view := .hidden
      requests := []
      apply := fun _ _ => absent }
  | .sequence first second =>
    let first := evaluateNode first value env cache locals.value scopes (target.child 0) location disabled
    let second := evaluateNode second value env cache locals.tail scopes (target.child 1) location disabled
    { output := second.output
      locals := ⟨first.locals, second.locals⟩
      view := .stack none [first.view, second.view]
      feedback := fun errors => .stack none [first.feedback errors, second.feedback errors]
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
        view := .hidden
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
  | .present body =>
    evaluatePresentation body value env cache locals scopes target location disabled nofun
  | .bind _ body =>
    bound locals.value <| evaluateNode body value (Env.cons locals.value env) cache locals.tail
      (scopes.bind target 1) (target.child 0) location disabled
  | .observe producer body =>
    let producer := evaluateNode producer value env cache locals.producer scopes (target.child 0) location disabled
    let body := evaluateNode body value (Env.cons producer.output env) cache locals.consumers
      (scopes.bind target 2) (target.child 1) location disabled
    observed producer body (.stack none [producer.view, body.view])
      fun errors => .stack none [producer.feedback errors, body.feedback errors]
  | .list path label itemLabel initial body =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      evaluateNode body item env cache (locals[index]?.getD body.initialState) scopes
        ((target.child index).child 0) (location ++ [.index index]) disabled
    evaluateCollection path initial body.initialState rows value env none disabled
      (fun views errors => listView views label itemLabel target location errors disabled)
  | .table (headers := headers) path label itemLabel initial columns selection =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      evaluateColumns columns item env cache (locals[index]?.getD columns.initialState) scopes
        ((target.child index).child 0) (location ++ [.index index]) disabled
    let selector := selection.map fun selected => ({ current := selected.get env, scope := scopes selected.index } : RowSelector)
    evaluateCollection path initial columns.initialState rows value env selection disabled
      (fun views errors => tableView headers views label itemLabel target location selector errors disabled)

def evaluateColumns
  {headers : List String}
  {Γ : Context}
  {α state β : Type}
  (columns : ColumnsNode headers Γ α state β)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool := false)
  : NodeEvaluation Γ α state β (CellViews headers) :=
  match columns with
  | .output computation =>
    { output := computation.eval value env
      locals := ()
      view := .nil
      requests := []
      apply := fun _ _ => absent }
  | .cons _ cell rest =>
    let cell := evaluateNode cell value env cache locals.value scopes (target.child 0) location disabled
    let rest := evaluateColumns rest value env cache locals.tail scopes (target.child 1) location disabled
    { output := rest.output
      locals := ⟨cell.locals, rest.locals⟩
      view := .cons cell.view rest.view
      feedback := fun errors => .cons (cell.feedback errors) (rest.feedback errors)
      requests := cell.requests ++ rest.requests
      apply := fun route argument => match route with
        | 0 :: route => do
          let updated ← cell.apply route argument
          return updated.mapLocals (⟨·, rest.locals⟩)
        | 1 :: route => do
          let updated ← rest.apply route argument
          return updated.mapLocals (⟨cell.locals, ·⟩)
        | _ => absent }
  | .observe _ cell rest =>
    let cell := evaluateNode cell value env cache locals.producer scopes (target.child 0) location disabled
    let rest := evaluateColumns rest value (Env.cons cell.output env) cache locals.consumers
      (scopes.bind target 2) (target.child 1) location disabled
    observed cell rest (.cons cell.view rest.view)
      fun errors => .cons (cell.feedback errors) (rest.feedback errors)
  | .bind _ body =>
    bound locals.value <| evaluateColumns body value (Env.cons locals.value env) cache locals.tail
      (scopes.bind target 1) (target.child 0) location disabled
  | .focus computation body =>
    let path := computation.eval value env
    match path.get? value with
    | none =>
      { output := none
        locals
        view := CellViews.hidden headers
        requests := []
        apply := fun _ _ => absent }
    | some focused =>
      let body := evaluateColumns body focused env cache locals scopes target (location ++ partialPathLocation path) disabled
      { output := some body.output
        locals := body.locals
        view := body.view
        feedback := body.feedback
        requests := body.requests
        apply := fun route argument => do
          let updated ← body.apply route argument
          return updated.mapValue (fun focused => path.set focused value) }

def evaluatePresentation
  {slots : Nat}
  {Γ : Context}
  {α state β : Type}
  (presentation : PresentationNode slots Γ α state β)
  (value : α)
  (env : Env Γ)
  (cache : HttpRequest.Cache)
  (locals : state)
  (scopes : WireScopes)
  (target : Display.Target)
  (location : Feedback.Location)
  (disabled : Bool)
  (presentations : Presentations slots)
  : NodeEvaluation Γ α state β :=
  match presentation with
  | .layout output arrangement =>
    let layout := arrangement.eval value env
    { output := output.eval value env
      locals := ()
      view := renderLayout (fun slot => (presentations slot).view) layout
      feedback := fun errors => renderLayout (fun slot => (presentations slot).feedback errors) layout
      requests := []
      apply := fun _ _ => absent }
  | .own component body =>
    let owned := evaluateNode component value env cache locals.producer scopes (target.child 0) location
      disabled
    let presentations : Presentations (slots + 1) := fun
      | .here => ⟨owned.view, owned.feedback⟩
      | .there slot => presentations slot
    let body := evaluatePresentation body value (Env.cons owned.output env) cache locals.consumers
      (scopes.bind target 2) (target.child 1) location disabled presentations
    observed owned body body.view body.feedback
  | .bind _ body =>
    bound locals.value <| evaluatePresentation body value (Env.cons locals.value env) cache locals.tail
      (scopes.bind target 1) (target.child 0) location disabled presentations

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
    let columns := evaluateColumns columns value env cache locals scopes (target.child index) location disabled
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
