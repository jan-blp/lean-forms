module

public import Forms.Model.Component
public import Forms.Model.Sugar.Computation
public meta import Lean.Elab.Term
meta import all Init.Prelude

/-!
# Form sugar

Use `_` for an ignored binding. Named bindings warn when neither their reference nor slot is used.

Enable the syntax with:

```lean
import Forms
open Forms.Model.Sugar
```
-/

public section
namespace Forms.Model.Sugar.Internal

abbrev bindComponent
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Var (⟨.writable, β⟩ :: Γ) β → Component (⟨.writable, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  .bind initial (body .here)

abbrev bindPresentation
  {slots : List Nat}
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  (initial : β)
  (body : Var (⟨.writable, β⟩ :: Γ) β →
    Presentation slots (⟨.writable, β⟩ :: Γ) α γ views)
  : Presentation slots Γ α γ views :=
  .bind initial (body .here)

abbrev observeComponent
  {Γ : Context}
  {α β γ : Type}
  (producer : Component Γ α β)
  (body : InputRef (⟨.readOnly, β⟩ :: Γ) β → Component (⟨.readOnly, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  .observe producer (body .here)

abbrev ownComponent
  {slots : List Nat}
  {Γ : Context}
  {α β γ : Type}
  {holes views : Nat}
  (component : Component Γ α β holes)
  (body : InputRef (⟨.readOnly, β⟩ :: Γ) β → Slot (holes :: slots) holes →
    Presentation (holes :: slots) (⟨.readOnly, β⟩ :: Γ) α γ views)
  : Presentation slots Γ α γ views :=
  .own component (body .here .here)

abbrev rowComputation
  {Γ : Context}
  {α β : Type}
  (body : InputRef (Context.row α Γ) (PointedList α) → Var (Context.row α Γ) Bool →
    Computation (Context.row α Γ) α β)
  : Computation (Context.row α Γ) α β :=
  body Ref.row Ref.rowRemoved

abbrev rowPresentation
  {Γ : Context}
  {α β : Type}
  {views : Nat}
  (body : InputRef (Context.row α Γ) (PointedList α) → Var (Context.row α Γ) Bool →
    Presentation [] (Context.row α Γ) α β views)
  : Presentation [] (Context.row α Γ) α β views :=
  body Ref.row Ref.rowRemoved

abbrev tabsPresentation
  {slots : List Nat}
  {Γ : Context}
  {α β : Type}
  {n : Nat}
  (label : Var (⟨.writable, Fin (n + 1)⟩ :: Γ) (Fin (n + 1)) →
    Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α String)
  (labels : Var (⟨.writable, Fin (n + 1)⟩ :: Γ) (Fin (n + 1)) →
    Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α (Vector String (n + 1)))
  (body :
    Var (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) (Fin (n + 1)) →
    InputRef (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) Unit →
    Slot (0 :: slots) 0 →
    Presentation (0 :: slots) (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) α β)
  : Presentation slots Γ α β :=
  .tabs (label .here) (labels .here) (body (.there .here) .here .here)

end Forms.Model.Sugar.Internal
end

public meta section
namespace Forms.Model.Sugar
open Lean

/-- Start a fresh block with `named% body`. Names from enclosing blocks are not imported. -/
scoped syntax "named% " term : term

/-- Start a block using existing `Var` or `InputRef` parameters: `named%[x, y] body`. -/
scoped syntax "named%[" ident,* "] " term : term

/-- Bind writable UI state with `state% x := (initial : T); body`. Use `ref[x]` in the body. -/
scoped syntax "state% " binderIdent " := " term " ; " term : term

/-- Observe a component's output with `observe% x := producer; body`. Use `ref[x]` in the body. -/
scoped syntax "observe% " binderIdent " := " term " ; " term : term

/--
Own a component with `own% child := component; body` inside a presentation.
Use `ref[child]` for its read-only output and `slot[child]` for its view.
-/
scoped syntax "own% " binderIdent " := " term " ; " term : term

/-- Build a component from a presentation with `present% body`. Starts a fresh slot scope. -/
scoped syntax "present% " term : term

/-- Build a `Presentation` directly, keeping variables and starting a fresh slot scope. -/
scoped syntax "presentation% " term : term

/--
Add tabs with `tabs% active, bar := title, labels; body`. Supply at least one label.
For `N` labels, `ref[active] : Var _ (Fin N)` starts at zero. Place the bar with `slot[bar]`.
Own panes separately and choose one in the layout using the active index.
-/
scoped syntax "tabs% " binderIdent ", " binderIdent " := " term ", " term " ; " term : term

/--
Use `row% current, removed => body` whenever a row label contains `ref[...]`.
`current` reads the `PointedList`; `removed` reads or sets its removal flag.
For a collection row presentation, use `presentation% row% current, removed => body`.
-/
scoped syntax "row% " binderIdent ", " binderIdent " => " term : term

/--
Refer to a variable or owned output with `ref[x]` inside `named%`.
Read it as an input, e.g. `inputs[ref[x]]`; update writable state with `.set ref[x] computation`.
-/
scoped syntax "ref[" ident "]" : term

/--
Place an owned component's view with `.place slot[child]` inside `named%`.
For a component with holes, use `.fill` instead.
-/
scoped syntax "slot[" ident "]" : term

namespace Internal

-- MacroM cannot log warnings, so report them during elaboration.
scoped syntax (name := unusedBinding) "named_unused% " ident term : term

@[term_elab unusedBinding] def elabUnusedBinding : Elab.Term.TermElab := fun stx expectedType? => do
  let value ← Elab.Term.elabTermEnsuringType stx[2] expectedType?
  unless ← MonadLog.hasErrors do
    logWarningAt stx[1] m!"Unused binding '{stx[1].getId}'; use '_' to ignore it"
  return value

scoped syntax (name := tabLabels) "named_tab_labels% " term : term

@[term_elab tabLabels] def elabTabLabels : Elab.Term.TermElab := fun stx expectedType? => do
  -- Infer the vector length before exposed layouts elaborate their index bounds.
  let vector? ← Elab.Term.commitIfNoErrors? do
    let value ← Elab.Term.withoutErrToSorry <|
      Elab.Term.elabTerm stx[1] none (catchExPostpone := false)
    let type ← Meta.whnf (← Meta.inferType value)
    unless type.isAppOf ``Vector do throwError "Tab labels are not a vector"
    let value ← Elab.Term.exprToSyntax value
    Elab.Term.elabTermEnsuringType (← `(Computation.const $value)) expectedType?
  match vector? with
  | some vector => return vector
  | none => Elab.Term.elabTermEnsuringType stx[1] expectedType?

end Internal

open Internal

private structure Binding where
  /-- Name used for lookup; absent for `_`. -/
  name : Option Ident
  /-- Lean identifier emitted before applying shifts. -/
  reference : Ident
  shifts : Nat

private inductive Bindings where
  | component (refs : List Binding)
  | presentation (refs : List Binding) (slots : List Binding)

private def Bindings.empty : Bindings :=
  .component []

private def Bindings.refs : Bindings → List Binding
  | .component refs => refs
  | .presentation refs _ => refs

private def Bindings.slots : Bindings → List Binding
  | .component _ => []
  | .presentation (slots := slots) .. => slots

private def Bindings.withRefs
  (bindings : Bindings)
  (refs : List Binding)
  : Bindings :=
  match bindings with
  | .component _ => .component refs
  | .presentation (slots := slots) .. => .presentation refs slots

private def bindingName? (name : Syntax) : Option Ident :=
  if name.isIdent then some ⟨name⟩ else
    match name with
    | `(binderIdent| $id:ident) => some id
    | _ => none

private def ensureFresh
  (name : Syntax)
  (bindings : Bindings)
  : MacroM Unit := do
  let some name := bindingName? name | return
  let used (binding : Binding) := binding.name.any (·.getId == name.getId)
  if bindings.refs.any used || bindings.slots.any used then
    Macro.throwErrorAt name s!"Name '{name.getId}' is already in scope; choose a different name"

private def importRefs (names : Array Ident) : MacroM Bindings := do
  let mut bindings := Bindings.empty
  for name in names do
    ensureFresh name bindings
    bindings := bindings.withRefs ({ name := some name, reference := name, shifts := 0 } :: bindings.refs)
  return bindings

private def lookup
  (kind : String)
  (name : Ident)
  (bindings : List Binding)
  : MacroM (TSyntax `term) := withRef name do
  match bindings.find? (fun binding => binding.name.any (·.getId == name.getId)) with
  | some binding =>
    let mut reference : TSyntax `term := ⟨binding.reference.raw.setInfo (SourceInfo.fromRef name)⟩
    for _ in [:binding.shifts] do
      reference ← `(Member.there $reference)
    return reference
  | none => Macro.throwErrorAt name s!"Unknown {kind} '{name.getId}' in this scope"

private def shift
  (bindings : List Binding)
  (count : Nat)
  : List Binding :=
  bindings.map fun binding => { binding with shifts := binding.shifts + count }

private def extend
  (existing : List Binding)
  (introduced : List Binding)
  : List Binding :=
  introduced ++ shift existing introduced.length

private def freshIdent (name : Syntax) : MacroM Ident := withFreshMacroScope do
  let id := (bindingName? name).map (·.getId) |>.getD `ignored
  return mkIdentFrom name (← MonadQuotation.addMacroScope id)

private def binding (name : Syntax) (reference : Ident) : Binding :=
  { name := bindingName? name, reference, shifts := 0 }

private def warnUnused
  (name : Syntax)
  (used : Bool)
  (body : Syntax)
  : MacroM Syntax := do
  if used then return body
  let some name := bindingName? name | return body
  `(named_unused% $name $(⟨body⟩))

private def requirePresentation
  (form : String)
  (bindings : Bindings)
  : MacroM (List Binding) := do
  match bindings with
  | .component _ =>
    Macro.throwError
      s!"{form} requires a presentation; use present%, or presentation% for a Presentation"
  | .presentation (slots := slots) .. => return slots

private def requireComponent
  (form : String)
  (bindings : Bindings)
  : MacroM (List Binding) := do
  match bindings with
  | .component refs => return refs
  | .presentation .. =>
    Macro.throwError s!"{form} requires a component; use own% inside a presentation"

private abbrev ExpandTerm := Bindings → MacroM (TSyntax `term)

private def expandState
  (name : TSyntax ``Lean.binderIdent)
  (bindings : Bindings)
  (initial : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  ensureFresh name bindings
  let initial ← initial bindings
  let localName ← freshIdent name
  let refs := extend bindings.refs [binding name localName]
  let body ← body (bindings.withRefs refs)
  let used := body.raw.hasIdent localName.getId
  let result ← match bindings with
    | .component _ => `(bindComponent $initial (fun $localName => $body))
    | .presentation .. => `(bindPresentation $initial (fun $localName => $body))
  warnUnused name used result

private def expandObserve
  (name : TSyntax ``Lean.binderIdent)
  (bindings : Bindings)
  (producer : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let refs ← requireComponent "observe%" bindings
  ensureFresh name bindings
  let producer ← producer bindings
  let localName ← freshIdent name
  let body ← body (.component (extend refs [binding name localName]))
  let result ← `(observeComponent $producer (fun $localName => $body))
  warnUnused name (body.raw.hasIdent localName.getId) result

private def expandOwn
  (name : TSyntax ``Lean.binderIdent)
  (bindings : Bindings)
  (component : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let slots ← requirePresentation "own%" bindings
  ensureFresh name bindings
  let component ← component (.component bindings.refs)
  let outputName ← freshIdent name
  let slotName ← freshIdent name
  let refs := extend bindings.refs [binding name outputName]
  let slots := extend slots [binding name slotName]
  let body ← body (.presentation refs slots)
  let result ← `(ownComponent $component (fun $outputName $slotName => $body))
  warnUnused name (body.raw.hasIdent outputName.getId || body.raw.hasIdent slotName.getId) result

private def expandTabs
  (active : TSyntax ``Lean.binderIdent)
  (strip : TSyntax ``Lean.binderIdent)
  (bindings : Bindings)
  (label : ExpandTerm)
  (labels : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let slots ← requirePresentation "tabs%" bindings
  ensureFresh active bindings
  let activeName ← freshIdent active
  let refs := extend bindings.refs [binding active activeName]
  ensureFresh strip (bindings.withRefs refs)
  let labelBindings := Bindings.component refs
  let label ← label labelBindings
  let labels ← labels labelBindings
  let bodyActiveName ← freshIdent active
  let outputName ← freshIdent strip
  let slotName ← freshIdent strip
  let refs := extend bindings.refs [
    binding strip outputName,
    binding active bodyActiveName]
  let slots := extend slots [binding strip slotName]
  let body ← body (.presentation refs slots)
  let result ← `(tabsPresentation
    (fun $activeName => $label)
    (fun $activeName => named_tab_labels% $labels)
    (fun $bodyActiveName $outputName $slotName => $body))
  let activeUsed := label.raw.hasIdent activeName.getId || labels.raw.hasIdent activeName.getId ||
    body.raw.hasIdent bodyActiveName.getId
  let result ← warnUnused active activeUsed result
  warnUnused strip (body.raw.hasIdent outputName.getId || body.raw.hasIdent slotName.getId) result

private def expandRow
  (current : TSyntax ``Lean.binderIdent)
  (removed : TSyntax ``Lean.binderIdent)
  (bindings : Bindings)
  (body : ExpandTerm)
  : MacroM Syntax := do
  ensureFresh current bindings
  let currentName ← freshIdent current
  let removedName ← freshIdent removed
  let currentBinding : Binding := binding current currentName
  ensureFresh removed (bindings.withRefs (extend bindings.refs [currentBinding]))
  let refs := extend bindings.refs [
    binding removed removedName,
    currentBinding]
  let rowBindings := match bindings with
    | .component _ => Bindings.component refs
    | .presentation .. => .presentation refs []
  let body ← body rowBindings
  let result ← match bindings with
    | .component _ => `(rowComputation (fun $currentName $removedName => $body))
    | .presentation .. => `(rowPresentation (fun $currentName $removedName => $body))
  let result ← warnUnused current (body.raw.hasIdent currentName.getId) result
  warnUnused removed (body.raw.hasIdent removedName.getId) result

private def rejectRawBinders (stx : Syntax) : MacroM Unit := do
  match stx with
  | `(.bind) =>
    Macro.throwError "Use state% for bindings inside named%"
  | `(.own) =>
    Macro.throwError "Use own% for ownership inside named%"
  | `(.observe) =>
    Macro.throwError "Use observe% for observation inside named%"
  | `(.present) =>
    Macro.throwError "Use present% for presentations inside named%"
  | _ =>
    if stx.isIdent && [
        `Component.bind, `Forms.Model.Component.bind,
        `Presentation.bind, `Forms.Model.Presentation.bind,
        `Presentation.own, `Forms.Model.Presentation.own,
        `Component.observe, `Forms.Model.Component.observe,
        `Component.present, `Forms.Model.Component.present,
        `Presentation.tabs, `Forms.Model.Presentation.tabs].contains stx.getId then
      Macro.throwError "Use the named% binding syntax here"

private theorem sizeOf_getArg_lt
  (info : SourceInfo)
  (kind : SyntaxNodeKind)
  (args : Array Syntax)
  (i : Nat)
  : sizeOf ((Syntax.node info kind args).getArg i) <
      sizeOf (Syntax.node info kind args) := by
  simp only [Syntax.getArg, Array.getD, Array.getInternal_eq_getElem]
  split
  next h =>
    have := Array.sizeOf_getElem args i h
    simp only [Syntax.node.sizeOf_spec]
    omega
  next =>
    cases args
    simp [Syntax.node.sizeOf_spec, Array.mk.sizeOf_spec]
    omega

private def expand
  (stx : Syntax)
  (bindings : Bindings)
  : MacroM Syntax := withRef stx do
  if stx.isQuot then return stx
  rejectRawBinders stx
  match stx with
  | .node info kind args =>
    match Syntax.node info kind args with
    | `(named% $body) =>
      return ← expand body .empty
    | `(named%[$names,*] $body) =>
      return ← expand body (← importRefs names.getElems)
    | `(ref[$name]) =>
      return (← lookup "variable" name bindings.refs).raw
    | `(slot[$name]) =>
      return (← lookup "slot" name bindings.slots).raw
    | `(state% $name:binderIdent := $initial; $body) =>
      expandState name bindings
        (fun bindings => return ⟨← expand initial bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(observe% $name:binderIdent := $producer; $body) =>
      expandObserve name bindings
        (fun bindings => return ⟨← expand producer bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(own% $name:binderIdent := $component; $body) =>
      expandOwn name bindings
        (fun bindings => return ⟨← expand component bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(present% $body) =>
      let body : TSyntax `term := ⟨← expand body (.presentation bindings.refs [])⟩
      return ← `(Component.present $body)
    | `(presentation% $body) =>
      expand body (.presentation bindings.refs [])
    | `(tabs% $active:binderIdent, $strip:binderIdent := $label, $labels; $body) =>
      expandTabs active strip bindings
        (fun bindings => return ⟨← expand label bindings⟩)
        (fun bindings => return ⟨← expand labels bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(row% $current:binderIdent, $removed:binderIdent => $body) =>
      expandRow current removed bindings
        (fun bindings => return ⟨← expand body bindings⟩)
    | _ => return .node info kind (← args.mapM (expand · bindings))
  | .missing => return stx
  | .atom .. => return stx
  | .ident .. => return stx
termination_by sizeOf stx
decreasing_by
  all_goals first
    | exact sizeOf_getArg_lt ..
    | decreasing_trivial

private def outsideNamed (form : String) : MacroM Syntax :=
  Macro.throwError s!"{form} is only valid inside named%"

/-- Reads a direct `ref[x]` input of this node as `.ui ref[x]`. -/
private def wrapRefInputs (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(computationInput| $name:binderIdent ← ref[$x]) =>
    `(computationInput| $name:binderIdent ← .ui ref[$x])
  | `(computationInput| ($name:binderIdent : $type) ← ref[$x]) =>
    `(computationInput| ($name:binderIdent : $type) ← .ui ref[$x])
  | `(inputs[$inputs,*]) =>
    let inputs ← inputs.getElems.mapM fun input => do
      match input with
      | `(ref[$x]) => `(.ui ref[$x])
      | _ => return ⟨input⟩
    `(inputs[$inputs,*])
  | _ => return stx

/-- Reads every `ref[x]` in an input position as `.ui ref[x]`. -/
private def readRefInputs (stx : Syntax) : MacroM Syntax := do
  match stx with
  | .node info kind args =>
    wrapRefInputs (.node info kind (← args.mapM readRefInputs))
  | .missing => return stx
  | .atom .. => return stx
  | .ident .. => return stx

macro_rules
  | `(named% $body) => do
    expand (← readRefInputs body) .empty
  | `(named%[$names,*] $body) => do
    expand (← readRefInputs body) (← importRefs names.getElems)
  | `(ref[$_name]) => outsideNamed "ref[...]"
  | `(slot[$_name]) => outsideNamed "slot[...]"
  | `(state% $_name:binderIdent := $_initial; $_body) => outsideNamed "state%"
  | `(observe% $_name:binderIdent := $_producer; $_body) => outsideNamed "observe%"
  | `(own% $_name:binderIdent := $_component; $_body) => outsideNamed "own%"
  | `(present% $_body) => outsideNamed "present%"
  | `(presentation% $_body) => outsideNamed "presentation%"
  | `(tabs% $_active:binderIdent, $_strip:binderIdent := $_label, $_labels; $_body) =>
    outsideNamed "tabs%"
  | `(row% $_current:binderIdent, $_removed:binderIdent => $_body) => outsideNamed "row%"

end Forms.Model.Sugar
