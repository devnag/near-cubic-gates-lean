import Proof.CaseAnalysis.RowsOriginalTupleFold
import Proof.CaseAnalysis.RowsOriginalSchedule

/-! A finite task list composes ordinary workers in exactly its stated
order. The task list is fixed in control, not serialized as a new input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFixedLoop
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsOriginalTask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def program {t : ℕ} (worker : Task→Σ s,Machine t s) : List Task→Σ s,Machine t s
  | []=>⟨_,SubstitutionRepeat.idle t⟩
  | task::rest=>⟨_,Composition.machine (worker task).2 (program worker rest).2⟩
noncomputable def machine {t : ℕ} (worker : Task→Σ s,Machine t s) (tasks : List Task):=(program worker tasks).2
def budget (cost : Task→ℕ) (tasks : List Task):=(tasks.map (fun task=>cost task+1)).sum

theorem run {t : ℕ} {α : Type} (worker : Task→Σ s,Machine t s) (cost : Task→ℕ)
    (H : α→Fin t→ℕ) (A : α→Fin t→List Bool) (next : α→Task→α)
    (supplier : ∀ task st,Step (worker task).2 (cost task) (H st) (A st) (H (next st task)) (A (next st task)))
    (tasks : List Task) (st : α) :
    Step (machine worker tasks) (budget cost tasks) (H st) (A st)
      (H (tasks.foldl next st)) (A (tasks.foldl next st)) := by
  induction tasks generalizing st with
  | nil=>
    have empty : Step (SubstitutionRepeat.idle t) 0 (H st) (A st) (H st) (A st) :=
      ⟨⟨⟨0,H st,A st⟩,0,(⟨0,H st,A st⟩ : Configuration t 1).tapeCells⟩,rfl,rfl,rfl,le_rfl⟩
    exact empty
  | cons task rest ih=>
    have joined:=(supplier task st).seq (ih (next st task))
    simpa only [machine,program,budget,List.map_cons,List.sum_cons,List.foldl_cons] using joined

theorem budget_bound (cost : Task→ℕ) (tasks : List Task) (C : ℕ) (hc : ∀ task∈tasks,cost task≤C) :
    budget cost tasks≤tasks.length*(C+1) := by
  induction tasks with
  | nil=>simp [budget]
  | cons task rest ih=>
    have h:=hc task (by simp)
    have ht:=ih (fun x hx=>hc x (by simp [hx]))
    simp only [budget,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul] at *
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFixedLoop
