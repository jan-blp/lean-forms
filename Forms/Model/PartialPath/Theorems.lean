module

public import Forms.Model.PartialPath

public section
namespace Forms.Model

private theorem modifyAt_eq_self_of_fixed
  {α : Type}
  (value : Collection α)
  (position : Nat)
  (f : α → α)
  (fixed : ∀ child, value.entries[position]? = some child → f child.value = child.value)
  : value.modifyAt position f = value := by
  apply Collection.ext
  apply List.ext_getElem?
  intro index
  simp only [Collection.modifyAt, List.getElem?_modify]
  split
  · cases found : value.entries[index]? <;> simp_all [Item.mapValue]
  · simp

theorem PartialPath.set_get
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  (old : β)
  (present : path.get? value = some old)
  : path.set old value = value := by
  induction path with
  | self => simpa [get?, set] using present.symm
  | field f rest ih =>
    simp only [set, ih _ _ present]
    exact (Fields.lawful f).set_view value
  | constructor ctor rest ih =>
    grind [get?, set, LawfulConstructors.inject_project]
  | item id rest ih =>
    simp only [get?, set, List.find?_eq_bind_findIdx?_getElem?] at present ⊢
    cases found : value.entries.findIdx? (·.id == id) with
    | none => rfl
    | some position =>
      simp only [found, Option.bind_some] at present ⊢
      exact modifyAt_eq_self_of_fixed _ _ _ fun child here =>
        ih child.value old (by simpa [here] using present)

theorem PartialPath.set_absent
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  (new : β)
  (absent : path.get? value = none)
  : path.set new value = value := by
  induction path with
  | self => simp [get?] at absent
  | field f rest ih =>
    simp only [set, ih _ _ absent]
    exact (Fields.lawful f).set_view value
  | constructor ctor rest ih =>
    grind [get?, set, LawfulConstructors.inject_project]
  | item id rest ih =>
    simp only [get?, set, List.find?_eq_bind_findIdx?_getElem?] at absent ⊢
    cases found : value.entries.findIdx? (·.id == id) with
    | none => rfl
    | some position =>
      simp only [found, Option.bind_some] at absent ⊢
      exact modifyAt_eq_self_of_fixed _ _ _ fun child here =>
        ih child.value new (by simpa [here] using absent)

/-- Writing through an entry never changes the ids of the collection. -/
theorem PartialPath.ids_set_item
  {α β : Type}
  (id : Uuid)
  (rest : PartialPath α β)
  (new : β)
  (value : Collection α)
  : ((PartialPath.item id rest).set new value).ids = value.ids := by
  simp only [set]
  split
  · rfl
  · exact Collection.ids_modifyAt ..

theorem PartialPath.erase_ofPath
  {α β : Type}
  (path : Path α β)
  : (PartialPath.ofPath path).erase = path.erase := by
  induction path with
  | self => rfl
  | stepField f rest ih => simp [ofPath, erase, Path.erase, ih]

theorem PartialPath.erase_trans
  {α β γ : Type}
  (first : PartialPath α β)
  (second : PartialPath β γ)
  : (first.trans second).erase = first.erase ++ second.erase := by
  induction first with
  | self => rfl
  | field f rest ih => simp [trans, erase, ih]
  | constructor ctor rest ih => simp [trans, erase, ih]
  | item id rest ih => simp [trans, erase, ih]

end Forms.Model
