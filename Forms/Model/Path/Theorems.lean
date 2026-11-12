module

public import Forms.Model.Basic

public section
namespace Forms.Model

theorem Path.get_set
  {α β : Type}
  (path : Path α β)
  (new : β)
  (value : α)
  : path.get (path.set new value) = new := by
  induction path with
  | self => rfl
  | @stepField α γ β inst f rest ih =>
    simp only [get, set, Fields.get, Fields.set, (Fields.lawful f).view_set]
    exact ih _ _

theorem Path.set_get
  {α β : Type}
  (path : Path α β)
  (value : α)
  : path.set (path.get value) value = value := by
  induction path with
  | self => rfl
  | @stepField α γ β inst f rest ih =>
    simp only [get, set, ih, Fields.get, Fields.set, (Fields.lawful f).set_view]

theorem Path.set_set
  {α β : Type}
  (path : Path α β)
  (first second : β)
  (value : α)
  : path.set second (path.set first value) = path.set second value := by
  induction path with
  | self => rfl
  | @stepField α γ β inst f rest ih =>
    simp only [set, Fields.get, Fields.set, (Fields.lawful f).view_set, ih,
      (Fields.lawful f).set_set]

instance {α β : Type} (path : Path α β) : LeanLens.LawfulLens path.toLens where
  view_set := path.get_set
  set_view := path.set_get
  set_set := path.set_set

end Forms.Model
