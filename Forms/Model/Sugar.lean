module

public import Forms.Model.Component
public meta import Lean.Elab.Term

/-! Form authoring sugar, enabled with `open Forms.Model.Sugar`. -/

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

scoped syntax "named% " term : term
scoped syntax "named%[" ident,* "] " term : term
scoped syntax "state% " ident " := " term " ; " term : term
scoped syntax "own% " ident " := " term " ; " term : term
scoped syntax "present% " term : term
scoped syntax "tabs% " ident ", " ident " := " term ", " term " ; " term : term
scoped syntax "alias% " ident " := " ident " ; " term : term
scoped syntax "row% " ident ", " ident " => " term : term
scoped syntax "ref[" ident "]" : term
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

private def findBinding
  (kind : String)
  (name : Ident)
  (bindings : List Binding)
  : MacroM Binding := do
  match bindings.find? (·.name.getId == name.getId) with
  | some binding => return binding
  | none => Macro.throwErrorAt name s!"Unknown {kind} '{name.getId}' in this scope"

private def lookup
  (kind : String)
  (name : Ident)
  (bindings : List Binding)
  : MacroM (TSyntax `term) := withRef name do
  let binding ← findBinding kind name bindings
  let mut reference : TSyntax `term := ⟨binding.reference.raw.setInfo (SourceInfo.fromRef name)⟩
  for _ in [:binding.shifts] do
    reference ← `(Member.there $reference)
  return reference

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

private partial def expand
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
  if let `(alias% $name := $original; $body) := stx then
    ensureFresh name bindings
    let binding ← findBinding "variable" original bindings.refs
    let refs := { binding with name } :: bindings.refs
    let slots := match bindings.slots.find? (·.name.getId == original.getId) with
      | some binding => { binding with name } :: bindings.slots
      | none => bindings.slots
    return ← expand body { bindings with refs, slots }
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
  | `(alias% $_name := $_original; $_body) => Macro.throwError "alias% is only valid inside named%"
  | `(row% $_current, $_removed => $_body) => Macro.throwError "row% is only valid inside named%"

end Forms.Model.Sugar
