module

public import Forms.Model.Component
public meta import Lean.Elab.Term
meta import all Init.Prelude

/-!
# Form sugar

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
scoped syntax "state% " ident " := " term " ; " term : term

/-- Observe a component's output with `observe% x := producer; body`. Use `ref[x]` in the body. -/
scoped syntax "observe% " ident " := " term " ; " term : term

/--
Own a component with `own% child := component; body` inside a presentation.
Use `ref[child]` for its read-only output and `slot[child]` for its view.
-/
scoped syntax "own% " ident " := " term " ; " term : term

/-- Build a component from a presentation with `present% body`. Starts a fresh slot scope. -/
scoped syntax "present% " term : term

/-- Build a `Presentation` directly, keeping variables and starting a fresh slot scope. -/
scoped syntax "presentation% " term : term

/--
Add tabs with `tabs% active, bar := title, labels; body`. Supply at least one label.
For `N` labels, `ref[active] : Var _ (Fin N)` starts at zero. Place the bar with `slot[bar]`.
Own panes separately and choose one in the layout using the active index.
-/
scoped syntax "tabs% " ident ", " ident " := " term ", " term " ; " term : term

/--
Use `row% current, removed => body` whenever a row label contains `ref[...]`.
`current` reads the `PointedList`; `removed` reads or sets its removal flag.
For a collection row presentation, use `presentation% row% current, removed => body`.
-/
scoped syntax "row% " ident ", " ident " => " term : term

/--
Refer to a variable or owned output with `ref[x]` inside `named%`.
Read it through `inputs[.ui ref[x]]`; update writable state with `.set ref[x] computation`.
-/
scoped syntax "ref[" ident "]" : term

/--
Place an owned component's view with `.place slot[child]` inside `named%`.
For a component with holes, use `.fill` instead.
-/
scoped syntax "slot[" ident "]" : term

namespace Internal

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
  /-- Name written by the user, used for lookup. -/
  name : Ident
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

private def ensureFresh
  (name : Ident)
  (bindings : Bindings)
  : MacroM Unit := do
  let used (binding : Binding) := binding.name.getId == name.getId
  if bindings.refs.any used || bindings.slots.any used then
    Macro.throwErrorAt name s!"Name '{name.getId}' is already in scope; choose a different name"

private def importRefs (names : Array Ident) : MacroM Bindings := do
  let mut bindings := Bindings.empty
  for name in names do
    ensureFresh name bindings
    bindings := bindings.withRefs ({ name, reference := name, shifts := 0 } :: bindings.refs)
  return bindings

private def lookup
  (kind : String)
  (name : Ident)
  (bindings : List Binding)
  : MacroM (TSyntax `term) := withRef name do
  match bindings.find? (·.name.getId == name.getId) with
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

private def freshIdent (name : Ident) : MacroM Ident := withFreshMacroScope do
  return mkIdentFrom name (← MonadQuotation.addMacroScope name.getId)

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
  (name : Ident)
  (bindings : Bindings)
  (initial : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  ensureFresh name bindings
  let initial ← initial bindings
  let localName ← freshIdent name
  let refs := extend bindings.refs [{ name, reference := localName, shifts := 0 }]
  let body ← body (bindings.withRefs refs)
  match bindings with
  | .component _ => return ← `(bindComponent $initial (fun $localName => $body))
  | .presentation .. => return ← `(bindPresentation $initial (fun $localName => $body))

private def expandObserve
  (name : Ident)
  (bindings : Bindings)
  (producer : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let refs ← requireComponent "observe%" bindings
  ensureFresh name bindings
  let producer ← producer bindings
  let localName ← freshIdent name
  let body ← body (.component (extend refs [{ name, reference := localName, shifts := 0 }]))
  return ← `(observeComponent $producer (fun $localName => $body))

private def expandOwn
  (name : Ident)
  (bindings : Bindings)
  (component : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let slots ← requirePresentation "own%" bindings
  ensureFresh name bindings
  let component ← component (.component bindings.refs)
  let outputName ← freshIdent name
  let slotName ← freshIdent name
  let refs := extend bindings.refs [{ name, reference := outputName, shifts := 0 }]
  let slots := extend slots [{ name, reference := slotName, shifts := 0 }]
  let body ← body (.presentation refs slots)
  return ← `(ownComponent $component (fun $outputName $slotName => $body))

private def expandTabs
  (active : Ident)
  (strip : Ident)
  (bindings : Bindings)
  (label : ExpandTerm)
  (labels : ExpandTerm)
  (body : ExpandTerm)
  : MacroM Syntax := do
  let slots ← requirePresentation "tabs%" bindings
  ensureFresh active bindings
  let activeName ← freshIdent active
  let refs := extend bindings.refs [{ name := active, reference := activeName, shifts := 0 }]
  ensureFresh strip (bindings.withRefs refs)
  let labelBindings := Bindings.component refs
  let label ← label labelBindings
  let labels ← labels labelBindings
  let bodyActiveName ← freshIdent active
  let outputName ← freshIdent strip
  let slotName ← freshIdent strip
  let refs := extend bindings.refs [
    { name := strip, reference := outputName, shifts := 0 },
    { name := active, reference := bodyActiveName, shifts := 0 }]
  let slots := extend slots [{ name := strip, reference := slotName, shifts := 0 }]
  let body ← body (.presentation refs slots)
  return ← `(tabsPresentation
    (fun $activeName => $label)
    (fun $activeName => named_tab_labels% $labels)
    (fun $bodyActiveName $outputName $slotName => $body))

private def expandRow
  (current : Ident)
  (removed : Ident)
  (bindings : Bindings)
  (body : ExpandTerm)
  : MacroM Syntax := do
  ensureFresh current bindings
  let currentName ← freshIdent current
  let removedName ← freshIdent removed
  let currentBinding : Binding := { name := current, reference := currentName, shifts := 0 }
  ensureFresh removed (bindings.withRefs (extend bindings.refs [currentBinding]))
  let refs := extend bindings.refs [
    { name := removed, reference := removedName, shifts := 0 },
    currentBinding]
  match bindings with
  | .component _ =>
    let body ← body (.component refs)
    return ← `(rowComputation (fun $currentName $removedName => $body))
  | .presentation .. =>
    let body ← body (.presentation refs [])
    return ← `(rowPresentation (fun $currentName $removedName => $body))

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
    | `(state% $name := $initial; $body) =>
      expandState name bindings
        (fun bindings => return ⟨← expand initial bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(observe% $name := $producer; $body) =>
      expandObserve name bindings
        (fun bindings => return ⟨← expand producer bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(own% $name := $component; $body) =>
      expandOwn name bindings
        (fun bindings => return ⟨← expand component bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(present% $body) =>
      let body : TSyntax `term := ⟨← expand body (.presentation bindings.refs [])⟩
      return ← `(Component.present $body)
    | `(presentation% $body) =>
      expand body (.presentation bindings.refs [])
    | `(tabs% $active, $strip := $label, $labels; $body) =>
      expandTabs active strip bindings
        (fun bindings => return ⟨← expand label bindings⟩)
        (fun bindings => return ⟨← expand labels bindings⟩)
        (fun bindings => return ⟨← expand body bindings⟩)
    | `(row% $current, $removed => $body) =>
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

macro_rules
  | `(named% $body) => expand body .empty
  | `(named%[$names,*] $body) => do
    expand body (← importRefs names.getElems)
  | `(ref[$_name]) => outsideNamed "ref[...]"
  | `(slot[$_name]) => outsideNamed "slot[...]"
  | `(state% $_name := $_initial; $_body) => outsideNamed "state%"
  | `(observe% $_name := $_producer; $_body) => outsideNamed "observe%"
  | `(own% $_name := $_component; $_body) => outsideNamed "own%"
  | `(present% $_body) => outsideNamed "present%"
  | `(presentation% $_body) => outsideNamed "presentation%"
  | `(tabs% $_active, $_strip := $_label, $_labels; $_body) =>
    outsideNamed "tabs%"
  | `(row% $_current, $_removed => $_body) => outsideNamed "row%"

end Forms.Model.Sugar
