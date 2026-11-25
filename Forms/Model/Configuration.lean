module

public import Forms.Model.Component
public import Mathlib.Data.FinEnum
public import Mathlib.Data.List.Perm.Basic

@[expose] public section
namespace Forms.Model

/-- How a field appears under a form's settings. -/
inductive FieldState where
  | shown
  | readOnly
  | excluded
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

def FieldState.describe : FieldState → String
  | .shown => "shown"
  | .readOnly => "read-only"
  | .excluded => "excluded"

/-- One configurable field, named by the encoding of its key. -/
structure FieldSetting where
  key : String
  state : FieldState
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- A tenant's settings for one form, as stored; the order of `fields` is the order they are
shown in. -/
structure Settings where
  fields : List FieldSetting
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

def Settings.empty : Settings where
  fields := []

/-- What happens to an excluded field's value. -/
inductive ExclusionPolicy (Fallback : Type) where
  | keep
  | reset (fallback : Fallback)

/-- The state of a field that saved settings do not mention yet. -/
inductive NewFieldState where
  | shown
  | excluded
  deriving DecidableEq

inductive Exclusion (Fallback : Type) where
  | forbidden
  | allowed (policy : ExclusionPolicy Fallback) (whenNew : NewFieldState)

/-- Whether settings may exclude a field, and its state while they do not mention it. -/
inductive Excludability where
  | forbidden
  | allowed (whenNew : NewFieldState)
  deriving DecidableEq

def Exclusion.excludability {Fallback : Type} : Exclusion Fallback → Excludability
  | .forbidden => .forbidden
  | .allowed _ whenNew => .allowed whenNew

/-- What settings may change about a field, independent of the model. -/
structure Capabilities where
  excludability : Excludability
  lockable : Bool
  deriving DecidableEq

def Capabilities.excludable (can : Capabilities) : Bool :=
  match can.excludability with
  | .forbidden => false
  | .allowed _ => true

/-- A field's state, allowed by its capabilities. -/
inductive Placement (can : Capabilities) where
  | shown
  | readOnly (lockable : can.lockable = true)
  | excluded (excludable : can.excludable = true)

def Placement.state {can : Capabilities} : Placement can → FieldState
  | .shown => .shown
  | .readOnly _ => .readOnly
  | .excluded _ => .excluded

/-- `state` as a placement, if `can` allows it. -/
def Placement.ofState (can : Capabilities) : FieldState → Option (Placement can)
  | .shown => some .shown
  | .readOnly => if lockable : can.lockable = true then some (.readOnly lockable) else none
  | .excluded => if excludable : can.excludable = true then some (.excluded excludable) else none

theorem Placement.ofState_state
  {can : Capabilities}
  {state : FieldState}
  {placement : Placement can}
  (allowed : Placement.ofState can state = some placement)
  : placement.state = state := by
  cases state <;> simp only [Placement.ofState] at allowed
  · cases allowed
    rfl
  all_goals
    split at allowed
    · cases allowed
      rfl
    · cases allowed

def Placement.initial (can : Capabilities) : Placement can :=
  match excludability : can.excludability with
  | .forbidden => .shown
  | .allowed .shown => .shown
  | .allowed .excluded => .excluded (by simp [Capabilities.excludable, excludability])

/-- Settings checked against a form's keys: every key has a placement its capabilities allow. -/
structure Resolution (K : Type) (can : K → Capabilities) where
  /-- Where a field goes among the configurable fields of its group. -/
  position : K → Nat
  placement : (key : K) → Placement (can key)

def Resolution.comap
  {K K' : Type}
  {can : K → Capabilities}
  (f : K' → K)
  (resolution : Resolution K can)
  : Resolution K' (can ∘ f) where
  position := resolution.position ∘ f
  placement key := resolution.placement (f key)

/-- Decodes by looking names up among all keys; the names must be distinct and non-empty. -/
@[instance_reducible] def Key.ofFinEnum
  {K : Type}
  [FinEnum K]
  (encode : K → String)
  (distinct : ((FinEnum.toList K).map encode).Nodup := by decide +kernel)
  (named : ∀ key ∈ FinEnum.toList K, encode key ≠ "" := by decide +kernel)
  : Key K where
  encode
  decode name := (FinEnum.toList K).find? (encode · == name)
  decode_encode key := Key.find?_encode encode _ key (FinEnum.mem_toList key) distinct
  encode_ne_empty key := named key (FinEnum.mem_toList key)

class FieldKey (K : Type) extends Key K, FinEnum K

/-- The keys of a form with nothing to configure. -/
instance : FieldKey Empty where
  encode := nofun
  decode _ := none
  decode_encode := nofun
  encode_ne_empty := nofun
  toFinEnum := inferInstance

/-- No location is a prefix of another's, so no two keys name overlapping fields. -/
def PrefixFree {K : Type} [FinEnum K] (location : K → ErasedLocation) : Prop :=
  ∀ a ∈ FinEnum.toList K, ∀ b ∈ FinEnum.toList K, a ≠ b → (location a).isPrefixOf (location b) = false

instance {K : Type} [FinEnum K] (location : K → ErasedLocation) : Decidable (PrefixFree location) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Where each key's field lives in `α`. -/
class FieldPaths (α K : Type) [FinEnum K] where
  Field : K → Type
  path : (key : K) → Path α (Field key)
  -- TODO: Quadratic in the keys; if slow, switch this and the other `decide +kernel` checks to `native_decide`.
  prefixFree : PrefixFree fun key => (path key).erase := by decide +kernel

/-- Settings for field -/
structure FieldTag (α K : Type) [FieldKey K] [FieldPaths α K] where
  key : K
  /-- Shown in errors raised while the field is excluded. -/
  displayName : String
  /-- Whether settings may exclude the field, and what then happens to its value. -/
  exclusion : Exclusion (FieldPaths.Field α key)
  /-- Whether settings may make the field read-only. -/
  lockable : Bool

/-- Where the field lives: a reset writes its fallback here, and diagnostics inside it are moved
or dropped while it is excluded. -/
def FieldTag.path
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (tag : FieldTag α K)
  : Path α (FieldPaths.Field α tag.key) :=
  FieldPaths.path tag.key

def FieldTag.capabilities
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (tag : FieldTag α K)
  : Capabilities where
  excludability := tag.exclusion.excludability
  lockable := tag.lockable

/-- The value of a field the placement excludes, under the tag's policy. -/
def FieldTag.fallback
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (tag : FieldTag α K)
  : Placement tag.capabilities → α → α
  | .shown => id
  | .readOnly _ => id
  | .excluded excludable =>
    match exclusion : tag.exclusion with
    | .forbidden => nomatch (by
        simp [Capabilities.excludable, FieldTag.capabilities, Exclusion.excludability, exclusion]
          at excludable : False)
    | .allowed .keep _ => id
    | .allowed (.reset fallback) _ => tag.path.set fallback

theorem Exclusion.excludability_cast
  {A B : Type}
  (same : A = B)
  (exclusion : Exclusion A)
  : (cast (congrArg Exclusion same) exclusion).excludability = exclusion.excludability := by
  subst same
  rfl

def FieldTag.nest
  {α β K K' : Type}
  [FieldKey K]
  [FieldKey K']
  [FieldPaths α K]
  [FieldPaths β K']
  (wrap : K' → K)
  (field_wrap : ∀ key, FieldPaths.Field α (wrap key) = FieldPaths.Field β key)
  (tag : FieldTag β K')
  : FieldTag α K where
  key := wrap tag.key
  displayName := tag.displayName
  exclusion := cast (congrArg Exclusion (field_wrap tag.key).symm) tag.exclusion
  lockable := tag.lockable

theorem FieldTag.capabilities_nest
  {α β K K' : Type}
  [FieldKey K]
  [FieldKey K']
  [FieldPaths α K]
  [FieldPaths β K']
  (wrap : K' → K)
  (field_wrap : ∀ key, FieldPaths.Field α (wrap key) = FieldPaths.Field β key)
  (tag : FieldTag β K')
  : (tag.nest wrap field_wrap).capabilities = tag.capabilities := by
  simp only [FieldTag.capabilities, FieldTag.nest]
  rw [Exclusion.excludability_cast (field_wrap tag.key).symm]

/-- A setting whose key decoded, with a placement its capabilities allow. -/
structure Accepted (K : Type) (can : K → Capabilities) where
  key : K
  placement : Placement (can key)

/-- Keeps the usable settings and describes each one it drops. Keys the settings do not mention
take their initial placement, after the keys they order. -/
def Settings.resolve
  {K : Type}
  [FieldKey K]
  (settings : Settings)
  (can : K → Capabilities)
  : Resolution K can × List String :=
  let step := fun (accepted : List (Accepted K can) × List String) (setting : FieldSetting) =>
    let (accepted, warnings) := accepted
    match Key.decode setting.key with
    | none => (accepted, warnings ++ [s!"Unknown field \"{setting.key}\" in the settings."])
    | some key =>
      if accepted.any (·.key == key) then
        (accepted, warnings ++ [s!"Field \"{setting.key}\" appears twice in the settings."])
      else
        match Placement.ofState (can key) setting.state with
        | some placement => (accepted ++ [{ key, placement }], warnings)
        | none =>
          (accepted ++ [{ key, placement := .shown }], warnings ++
            [s!"Field \"{setting.key}\" cannot be {setting.state.describe}; it is shown."])
  let (accepted, warnings) := settings.fields.foldl step ([], [])
  let placement (key : K) : Placement (can key) :=
    (accepted.findSome? fun setting =>
      if same : setting.key = key then some (same ▸ setting.placement) else none).getD
      (.initial (can key))
  ({ position key := (accepted.findIdx? (·.key == key)).getD accepted.length, placement },
    warnings)

/-- Puts `queue` into the positions of `slots` that satisfy `p`, in order. -/
def fillPositions {σ : Type _} (p : σ → Bool) : List σ → List σ → List σ
  | [], _ => []
  | slot :: rest, queue =>
    if p slot then
      match queue with
      | next :: later => next :: fillPositions p rest later
      | [] => slot :: fillPositions p rest []
    else slot :: fillPositions p rest queue

theorem fillPositions_perm_append
  {σ : Type _}
  (p : σ → Bool)
  : ∀ (slots queue : List σ), queue.length = (slots.filter p).length →
    (fillPositions p slots queue).Perm (slots.filter (! p ·) ++ queue)
  | [], queue, length => by simp_all [fillPositions]
  | slot :: rest, queue, length => by
    by_cases tagged : p slot
    · match queue, length with
      | [], length => simp [tagged] at length
      | next :: later, length =>
        simp only [fillPositions, tagged, ite_true, List.filter_cons, Bool.not_true,
          Bool.false_eq_true, ite_false]
        simp only [List.filter_cons, tagged, ite_true, List.length_cons] at length
        exact ((fillPositions_perm_append p rest later (by omega)).cons next).trans
          List.perm_middle.symm
    · simp only [fillPositions, tagged, Bool.false_eq_true, ite_false, List.filter_cons,
        Bool.not_false, ite_true, List.cons_append]
      simp only [List.filter_cons, tagged, Bool.false_eq_true, ite_false] at length
      exact (fillPositions_perm_append p rest queue length).cons slot

/-- Reordering the positions that satisfy `p` keeps every slot. -/
theorem fillPositions_perm
  {σ : Type _}
  (p : σ → Bool)
  (slots queue : List σ)
  (reordered : queue.Perm (slots.filter p))
  : (fillPositions p slots queue).Perm slots :=
  (fillPositions_perm_append p slots queue reordered.length_eq).trans <|
    (reordered.append_left _).trans <|
      List.perm_append_comm.trans (List.filter_append_perm p slots)

/-- A component of `α` whose fields its settings can exclude, reorder, or make read-only.
`build` needs the capabilities of each key to agree with the tags that use it. -/
structure Configured (Γ : Context) (α K : Type) [FieldKey K] [FieldPaths α K] where
  tags : List (FieldTag α K)
  build
    : {can : K → Capabilities}
    → (∀ tag ∈ tags, can tag.key = tag.capabilities)
    → Resolution K can
    → Component Γ α

inductive Slot (Γ : Context) (α K : Type) [FieldKey K] [FieldPaths α K] where
  | fixed (component : Component Γ α)
  | tagged (tag : FieldTag α K) (component : Component Γ α)
  /-- Keeps its position; its own fields follow the settings. -/
  | nested (part : Configured Γ α K)

def Slot.tags
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  : Slot Γ α K → List (FieldTag α K)
  | .fixed _ => []
  | .tagged tag _ => [tag]
  | .nested part => part.tags

def Slot.isTagged
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  : Slot Γ α K → Bool
  | .fixed _ => false
  | .tagged _ _ => true
  | .nested _ => false

def Slot.position
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (resolution : Resolution K can)
  : Slot Γ α K → Nat
  | .fixed _ => 0
  | .tagged tag _ => resolution.position tag.key
  | .nested _ => 0

def Slot.render
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (resolution : Resolution K can)
  : (slot : Slot Γ α K) → (∀ tag ∈ slot.tags, can tag.key = tag.capabilities) →
    Option (Component Γ α)
  | .fixed component, _ => some component
  | .nested part, agree => some (part.build agree resolution)
  | .tagged tag component, agree =>
    match agree tag (by simp [Slot.tags]) ▸ resolution.placement tag.key with
    | .shown => some component
    | .readOnly _ => some (.withAvailability (.const .disabled) component)
    | .excluded _ => none

/-- A tagged slot for the field `key` names. -/
def Slot.configurable
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (key : K)
  (displayName : String)
  (exclusion : Exclusion (FieldPaths.Field α key))
  (lockable : Bool)
  (component : Component Γ α)
  : Slot Γ α K :=
  .tagged { key, displayName, exclusion, lockable } component

/-- A tagged editor for the field `key` names. -/
def Slot.field
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (key : K)
  (displayName : String)
  (editor : Editor (FieldPaths.Field α key))
  (exclusion : Exclusion (FieldPaths.Field α key))
  (lockable : Bool)
  : Slot Γ α K :=
  .configurable key displayName exclusion lockable (.field (FieldPaths.path key) displayName editor)

/-- Tagged slots take the positions of tagged slots, in the order the settings give. -/
def Slot.arrange
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (resolution : Resolution K can)
  (slots : List (Slot Γ α K))
  : List (Slot Γ α K) :=
  let ordered := (slots.filter Slot.isTagged).mergeSort
    (fun first second => first.position resolution ≤ second.position resolution)
  fillPositions Slot.isTagged slots ordered

theorem Slot.arrange_perm
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (resolution : Resolution K can)
  (slots : List (Slot Γ α K))
  : (Slot.arrange resolution slots).Perm slots :=
  fillPositions_perm _ _ _ (List.mergeSort_perm _ _)

def Configured.ofComponent
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (component : Component Γ α)
  : Configured Γ α K where
  tags := []
  build _ _ := component

def Configured.group
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (label : Computation Γ α String)
  (slots : List (Slot Γ α K))
  : Configured Γ α K where
  tags := slots.flatMap Slot.tags
  build agree resolution :=
    let arranged := Slot.arrange resolution slots
    .group label <| arranged.attach.filterMap fun ⟨slot, placed⟩ =>
      slot.render resolution fun tag tagged =>
        agree tag (List.mem_flatMap.mpr
          ⟨slot, (Slot.arrange_perm resolution slots).mem_iff.mp placed, tagged⟩)

/-- A part of the sub-record at `path`, whose keys `wrap` makes keys of the whole form. The whole
form's `FieldPaths` must agree with the sub-record's. -/
def Configured.nest
  {Γ : Context}
  {α β K K' : Type}
  [FieldKey K]
  [FieldKey K']
  [FieldPaths α K]
  [FieldPaths β K']
  (wrap : K' → K)
  (path : Path α β)
  (part : Configured Γ β K')
  (field_wrap : ∀ key, FieldPaths.Field α (wrap key) = FieldPaths.Field β key := by intro _; rfl)
  (_path_wrap : ∀ key ∈ FinEnum.toList K',
      (FieldPaths.path (α := α) (wrap key)).erase = (path.trans (FieldPaths.path key)).erase := by decide +kernel)
  : Configured Γ α K where
  tags := part.tags.map (FieldTag.nest wrap field_wrap)
  build agree resolution :=
    .zoom path <| part.build
      (fun tag tagged =>
        (agree (tag.nest wrap field_wrap) (List.mem_map_of_mem tagged)).trans
          (FieldTag.capabilities_nest wrap field_wrap tag))
      (resolution.comap wrap)

/-- The capabilities of the tag that uses `key`. -/
def Configured.capabilities
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (form : Configured Γ α K)
  (key : K)
  : Capabilities :=
  match form.tags.find? (·.key == key) with
  | some tag => tag.capabilities
  | none => { excludability := .forbidden, lockable := false }

/-- Every key is used by exactly one tag, and `capabilities` agrees with each tag. -/
def Configured.WellKeyed
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  (form : Configured Γ α K)
  : Prop :=
  (form.tags.map (·.key)).Perm (FinEnum.toList K) ∧
    ∀ tag ∈ form.tags, form.capabilities tag.key = tag.capabilities

instance
    {Γ : Context}
    {α K : Type}
    [FieldKey K]
    [FieldPaths α K]
    (form : Configured Γ α K)
    : Decidable form.WellKeyed :=
  inferInstanceAs (Decidable (_ ∧ _))

def Configured.excluded
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (form : Configured Γ α K)
  (resolution : Resolution K can)
  : List ExcludedField :=
  (form.tags.filter fun tag => (resolution.placement tag.key).state == .excluded).map fun tag =>
    { scope := tag.path.erase, label := tag.displayName }

/-- Applies the fallback of every excluded field whose policy resets it. -/
def Configured.applyFallbacks
  {Γ : Context}
  {α K : Type}
  [FieldKey K]
  [FieldPaths α K]
  {can : K → Capabilities}
  (form : Configured Γ α K)
  (agree : ∀ tag ∈ form.tags, can tag.key = tag.capabilities)
  (resolution : Resolution K can)
  (value : α)
  : α :=
  form.tags.attach.foldl (init := value) fun value ⟨tag, tagged⟩ =>
    tag.fallback (agree tag tagged ▸ resolution.placement tag.key) value

end Forms.Model
