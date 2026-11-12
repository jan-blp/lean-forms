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
  | empty => rfl
  | field f rest ih =>
    simp only [set, ih _ _ present]
    exact (Fields.lawful f).set_view value
  | constructor ctor rest ih =>
    grind [get?, set, LawfulConstructors.inject_project]
  | index position rest ih => grind [get?, set, List.set_getElem_self]

theorem PartialPath.get_set
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  (old new : β)
  (present : path.get? value = some old)
  : path.get? (path.set new value) = some new := by
  induction path with
  | self => rfl
  | empty => simp [get?] at present
  | field f rest ih =>
    simpa only [set, get?, Fields.get, Fields.set, (Fields.lawful f).view_set]
      using ih _ _ _ present
  | constructor ctor rest ih =>
    grind [get?, set, LawfulConstructors.project_inject]
  | index position rest ih => grind [get?, set]

theorem PartialPath.set_absent
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  (new : β)
  (absent : path.get? value = none)
  : path.set new value = value := by
  induction path with
  | self => simp [get?] at absent
  | empty => rfl
  | field f rest ih =>
    simp only [set, ih _ _ absent]
    exact (Fields.lawful f).set_view value
  | constructor ctor rest ih =>
    grind [get?, set, LawfulConstructors.inject_project]
  | index position rest ih => grind [get?, set, List.set_getElem_self]

theorem PartialPath.set_set
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  (first second : β)
  : path.set second (path.set first value) = path.set second value := by
  induction path with
  | self => rfl
  | empty => rfl
  | field f rest ih =>
    simp only [set, Fields.get, Fields.set, (Fields.lawful f).view_set, ih,
      (Fields.lawful f).set_set]
  | constructor ctor rest ih =>
    grind [set, LawfulConstructors.project_inject]
  | index position rest ih => grind [set, List.set_set]

end Forms.Model
