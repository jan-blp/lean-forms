module

public import Forms.Model.PartialPath

public section
namespace Forms.Model

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
    simp only [get?, set] at present ⊢
    cases found : value.findIdx? (HasUuid.id · == id) with
    | none => simp
    | some position =>
      simp only [found] at present ⊢
      apply List.ext_getElem?
      intro index
      rw [List.getElem?_modify]
      split
      · cases child : value[index]? <;> simp_all
      · simp

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
    simp only [get?, set] at absent ⊢
    cases found : value.findIdx? (HasUuid.id · == id) with
    | none => simp
    | some position =>
      simp only [found] at absent ⊢
      apply List.ext_getElem?
      intro index
      rw [List.getElem?_modify]
      split
      · cases child : value[index]? <;> simp_all
      · simp

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
