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

Names must be unique within a block. References adjust automatically as bindings are added.
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

/--
Own a component with `own% child := component; body` inside a presentation.
Use `ref[child]` for its read-only output and `slot[child]` for its view.
-/
scoped syntax "own% " ident " := " term " ; " term : term

/-- Build a component from a presentation with `present% body`. Starts a fresh slot scope. -/
scoped syntax "present% " term : term

/--
Add tabs with `tabs% active, bar := title, labels; body`. Supply at least one label.
For `N` labels, `ref[active] : Var _ (Fin N)` starts at zero. Place the bar with `slot[bar]`.
Own panes separately and choose one in the layout using the active index.
-/
scoped syntax "tabs% " ident ", " ident " := " term ", " term " ; " term : term

/--
Use `row% current, removed => computation` in a collection's row-label computation.
Read the supplied `PointedList` with `ref[current]`; read or set the `Bool` with `ref[removed]`.
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
  name : Ident
  reference : Ident
  shifts : Nat

private inductive Mode where
  | component
  | presentation

private structure Bindings where
  refs : List Binding
  slots : List Binding
  mode : Mode

private def Bindings.empty : Bindings :=
  { refs := [], slots := [], mode := .component }

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
    bindings := { bindings with
      refs := { name, reference := name, shifts := 0 } :: bindings.refs }
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

private def freshIdent (name : Ident) : MacroM Ident := withFreshMacroScope do
  return mkIdentFrom name (← MonadQuotation.addMacroScope name.getId)

private def requirePresentation
  (form : String)
  (bindings : Bindings)
  : MacroM Unit := do
  match bindings.mode with
  | .component => Macro.throwError s!"{form} requires a presentation; use present%"
  | .presentation => pure ()

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
  if let `(named% $body) := stx then
    return ← expand body .empty
  if let `(named%[$names,*] $body) := stx then
    return ← expand body (← importRefs names.getElems)
  if let `(ref[$name]) := stx then
    return (← lookup "variable" name bindings.refs).raw
  if let `(slot[$name]) := stx then
    return (← lookup "slot" name bindings.slots).raw
  if let `(state% $name := $initial; $body) := stx then
    ensureFresh name bindings
    let initial : TSyntax `term := ⟨← expand initial bindings⟩
    let localName ← freshIdent name
    let refs := { name, reference := localName, shifts := 0 } :: shift bindings.refs 1
    let body : TSyntax `term := ⟨← expand body { bindings with refs }⟩
    match bindings.mode with
    | .component => return ← `(bindComponent $initial (fun $localName => $body))
    | .presentation => return ← `(bindPresentation $initial (fun $localName => $body))
  if let `(own% $name := $component; $body) := stx then
    requirePresentation "own%" bindings
    ensureFresh name bindings
    let component : TSyntax `term := ⟨← expand component
      { bindings with slots := [], mode := .component }⟩
    let outputName ← freshIdent name
    let slotName ← freshIdent name
    let refs := { name, reference := outputName, shifts := 0 } :: shift bindings.refs 1
    let slots := { name, reference := slotName, shifts := 0 } :: shift bindings.slots 1
    let body : TSyntax `term := ⟨← expand body { refs, slots, mode := .presentation }⟩
    return ← `(ownComponent $component (fun $outputName $slotName => $body))
  if let `(present% $body) := stx then
    let body : TSyntax `term := ⟨← expand body { bindings with slots := [], mode := .presentation }⟩
    return ← `(Component.present $body)
  if let `(tabs% $active, $strip := $label, $labels; $body) := stx then
    requirePresentation "tabs%" bindings
    ensureFresh active bindings
    let activeName ← freshIdent active
    let refs := { name := active, reference := activeName, shifts := 0 } :: shift bindings.refs 1
    ensureFresh strip { bindings with refs }
    let label : TSyntax `term := ⟨← expand label { bindings with refs }⟩
    let labels : TSyntax `term := ⟨← expand labels { bindings with refs }⟩
    let bodyActiveName ← freshIdent active
    let outputName ← freshIdent strip
    let slotName ← freshIdent strip
    let refs :=
      { name := strip, reference := outputName, shifts := 0 } ::
      { name := active, reference := bodyActiveName, shifts := 0 } :: shift bindings.refs 2
    let slots := { name := strip, reference := slotName, shifts := 0 } :: shift bindings.slots 1
    let body : TSyntax `term := ⟨← expand body { refs, slots, mode := .presentation }⟩
    return ← `(tabsPresentation
      (fun $activeName => $label)
      (fun $activeName => named_tab_labels% $labels)
      (fun $bodyActiveName $outputName $slotName => $body))
  if let `(row% $current, $removed => $body) := stx then
    ensureFresh current bindings
    let currentName ← freshIdent current
    let removedName ← freshIdent removed
    let refs := { name := current, reference := currentName, shifts := 0 } :: shift bindings.refs 2
    ensureFresh removed { bindings with refs }
    let refs := { name := removed, reference := removedName, shifts := 0 } :: refs
    let body : TSyntax `term := ⟨← expand body { refs, slots := [], mode := .component }⟩
    return ← `(rowComputation (fun $currentName $removedName => $body))
  if let `(.bind) := stx then
    Macro.throwError "Use state% for bindings inside named%"
  if let `(.own) := stx then
    Macro.throwError "Use own% for ownership inside named%"
  if let `(.present) := stx then
    Macro.throwError "Use present% for presentations inside named%"
  if stx.isIdent && [
      `Component.bind, `Forms.Model.Component.bind,
      `Presentation.bind, `Forms.Model.Presentation.bind,
      `Presentation.own, `Forms.Model.Presentation.own,
      `Component.present, `Forms.Model.Component.present,
      `Presentation.tabs, `Forms.Model.Presentation.tabs].contains stx.getId then
    Macro.throwError "Use the named% binding syntax here"
  match stx with
  | .node info kind args => return .node info kind (← args.mapM (expand · bindings))
  | .missing => return stx
  | .atom .. => return stx
  | .ident .. => return stx
termination_by sizeOf stx
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | cases stx <;> first
      | exact sizeOf_getArg_lt ..
      | simp_all +zetaDelta [Syntax.isOfKind, Syntax.getKind]

macro_rules
  | `(named% $body) => expand body .empty
  | `(named%[$names,*] $body) => do
    expand body (← importRefs names.getElems)
  | `(ref[$_name]) => Macro.throwError "ref[...] is only valid inside named%"
  | `(slot[$_name]) => Macro.throwError "slot[...] is only valid inside named%"
  | `(state% $_name := $_initial; $_body) => Macro.throwError "state% is only valid inside named%"
  | `(own% $_name := $_component; $_body) => Macro.throwError "own% is only valid inside named%"
  | `(present% $_body) => Macro.throwError "present% is only valid inside named%"
  | `(tabs% $_active, $_strip := $_label, $_labels; $_body) =>
    Macro.throwError "tabs% is only valid inside named%"
  | `(row% $_current, $_removed => $_body) => Macro.throwError "row% is only valid inside named%"

end Forms.Model.Sugar
