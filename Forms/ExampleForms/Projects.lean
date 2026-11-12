module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure PlannerTask where
  title : String
  owner : String
  hours : Nat
  completed : Bool
  notes : String
  title_valid : title ≠ ""
  owner_valid : owner ≠ ""
  hours_valid : 1 ≤ hours
  deriving FormModel

instance PlannerTask.title_valid_rule : ConstraintRule PlannerTask.Constraint.title_valid where
  check parts :=
    if h : parts.title ≠ "" then .valid h
    else .invalid (proof := h) (message := "Give the task a title.")
      (targets := locations[PlannerTask.Field.title])

instance PlannerTask.owner_valid_rule : ConstraintRule PlannerTask.Constraint.owner_valid where
  check parts :=
    if h : parts.owner ≠ "" then .valid h
    else .invalid (proof := h) (message := "Assign an owner to the task.")
      (targets := locations[PlannerTask.Field.owner])

instance PlannerTask.hours_valid_rule : ConstraintRule PlannerTask.Constraint.hours_valid where
  check parts :=
    if h : 1 ≤ parts.hours then .valid h
    else .invalid (proof := h) (message := "Estimate at least one hour.")
      (targets := locations[PlannerTask.Field.hours])

def PlannerTask.initial : PlannerTask.Raw := ⟨"New task", "Unassigned", 1, false, ""⟩

def PlannerTask.details {Γ : Context} : Component Γ PlannerTask.Raw :=
  .group "Task details" [
    .field path[PlannerTask.Field.title] "Task title" .text,
    .field path[PlannerTask.Field.owner] "Owner" .text,
    .field path[PlannerTask.Field.hours] "Estimated hours" .natural,
    .field path[PlannerTask.Field.completed] "Completed" .checkbox,
    .field path[PlannerTask.Field.notes] "Notes" .text]

def PlannerTask.columns {Γ : Context} : Columns Γ PlannerTask.Raw := columns[
  "Task" => .computed "Task" { inputs := inputs[path[PlannerTask.Field.title]], run := id },
  "Owner" => .computed "Owner" { inputs := inputs[path[PlannerTask.Field.owner]], run := id },
  "Estimate" => .computed "Estimate" {
    inputs := inputs[path[PlannerTask.Field.hours]], run := fun hours => s!"{hours} h" },
  "Status" => .computed "Status" {
    inputs := inputs[path[PlannerTask.Field.completed]], run := fun completed => if completed then "Done" else "To do" }]

structure PlannerProject where
  name : String
  tasks : List PlannerTask
  name_valid : name ≠ ""
  deriving FormModel

instance PlannerProject.name_valid_rule : ConstraintRule PlannerProject.Constraint.name_valid where
  check parts :=
    if h : parts.name ≠ "" then .valid h
    else .invalid (proof := h) (message := "Give the project a name.")
      (targets := locations[PlannerProject.Field.name])

def PlannerProject.initial : PlannerProject.Raw := ⟨"New project", [PlannerTask.initial]⟩

/-- Every project instance owns its selection. The table and editor share only that local variable. -/
def PlannerProject.form {Γ : Context} : Component Γ PlannerProject.Raw :=
  .bind RowSelection.none <|
    let selectedTask : Var (⟨.writable, RowSelection⟩ :: Γ) RowSelection := .here
    .group "" [
      .field path[PlannerProject.Field.name] "Project name" .text,
      .computed "Progress" {
        inputs := inputs[path[PlannerProject.Field.tasks]]
        run := fun tasks =>
          s!"{(tasks.filter (·.completed)).length} / {tasks.length} tasks complete · {(tasks.map (·.hours)).sum} h planned" },
      .table path[PlannerProject.Field.tasks] "Tasks" "Task" PlannerTask.initial PlannerTask.columns
        (some selectedTask),
      .visibleWhen
        { inputs := inputs[.ui selectedTask], run := fun selected => selected == .none }
        (.computed "" (.const "Choose a task to see its details.")),
      .visibleWhen
        { inputs := inputs[.ui selectedTask], run := fun selected => selected != .none }
        (.button "Close task" (.set selectedTask (.const .none))),
      .focus
        { inputs := inputs[.ui selectedTask]
          run := RowSelection.itemPath path[PlannerProject.Field.tasks] }
        PlannerTask.details]

structure ProjectPlanner where
  name : String
  projects : List PlannerProject
  name_valid : name ≠ ""
  deriving FormModel

instance ProjectPlanner.name_valid_rule : ConstraintRule ProjectPlanner.Constraint.name_valid where
  check parts :=
    if h : parts.name ≠ "" then .valid h
    else .invalid (proof := h) (message := "Give the plan a name.")
      (targets := locations[ProjectPlanner.Field.name])

def ProjectPlanner.initial : ProjectPlanner.Raw := ⟨"Team launch plan", [
  ⟨"Website refresh", [
    ⟨"Map the new navigation", "Ada", 3, true, "Agree on the page hierarchy before wireframes."⟩,
    ⟨"Build accessible navigation", "Grace", 5, false, "Keyboard support, focus states, and the mobile menu."⟩,
    ⟨"Check the release", "Linus", 2, false, "Run smoke tests and prepare the rollout."⟩]⟩,
  ⟨"Customer onboarding", [
    ⟨"Draft the welcome email", "Maya", 2, false, "Keep it short and include the first useful action."⟩,
    ⟨"Measure activation", "Sam", 3, false, "Choose an activation event and add a dashboard."⟩]⟩]⟩

def ProjectPlanner.counted (count : Nat) (noun : String) : String :=
  s!"{count} {noun}{if count == 1 then "" else "s"}"

def ProjectPlanner.form : Component [] ProjectPlanner.Raw := .group "Project planner" [
  .computed "How it works" (.const "Choose a task to edit its details. Each project keeps its own task open."),
  .field path[ProjectPlanner.Field.name] "Plan name" .text,
  .computed "Overview" {
    inputs := inputs[path[ProjectPlanner.Field.projects]]
    run := fun projects =>
      let tasks := projects.flatMap (·.tasks)
      s!"{ProjectPlanner.counted projects.length "project"} · {ProjectPlanner.counted tasks.length "task"} · {(tasks.filter (·.completed)).length} complete · {(tasks.map (·.hours)).sum} h planned" },
  .list path[ProjectPlanner.Field.projects] "Projects" "Project" PlannerProject.initial PlannerProject.form]

end Forms.ExampleForms
