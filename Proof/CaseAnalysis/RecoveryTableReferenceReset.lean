import Proof.CaseAnalysis.RecoveryTableReferenceAppend

/-! Rewind the updated original prior-reference stream using its existing
reusable D log. Every other head, including the count sentinel, is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceReset
open LocalBitMultitape RepairRepresentation
open RecoveryBoundedTableReferenceAppend RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 8):=decide (i=4)
noncomputable def machine:=MaskedReset.machine RecoveryBoundedTableReferenceAppend.machine selected
def budget (refs : List ℕ) (node C : ℕ):=2*RecoveryBoundedTableReferenceAppend.budget refs node C+2
noncomputable def entry (refs : List ℕ) (node C D : ℕ):=
  ZeroPadding.config (Rewind.Workspace.capacities 8 D)
    (Rewind.recording (⟨RecoveryBoundedTableReferenceAppend.machine.start,heads [],data node C refs.length (sourceWord refs)⟩) 0)
def finalHeads : Fin 9→ℕ:=Fin.addCases (m:=8) (n:=1) (motive:=fun _=>ℕ) (heads []) (fun _=>0)
def finalData (refs : List ℕ) (node C D : ℕ) : Fin 9→List Bool:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (data node C refs.length (sourceWord (refs++[node]))) (fun _=>List.replicate D false)

theorem entry_heads (refs : List ℕ) (node C D : ℕ) :
    (entry refs node C D).heads=finalHeads := by rfl
theorem entry_tapes (refs : List ℕ) (node C D : ℕ) :
    (entry refs node C D).tapes=
      Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
        (data node C refs.length (sourceWord refs)) (fun _=>List.replicate D false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero]
  · simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      Rewind.Workspace.capacities,Fin.addCases_right]
    rfl
theorem reset_heads (out : List Bool) :
    (fun i=>if selected i then 0 else heads out i)=heads [] := by
  funext i
  fin_cases i <;> rfl

theorem reset_run (refs : List ℕ) (node C D : ℕ) (hC : 2*node+1 ≤ C)
    (hD : RecoveryBoundedTableReferenceAppend.budget refs node C ≤ D) :
    ∃ r,runFrom machine (budget refs node C) (entry refs node C D)=some r ∧
      r.steps ≤ budget refs node C ∧ r.final.heads=finalHeads ∧ r.final.tapes=finalData refs node C D := by
  obtain ⟨p,pr,ps,ph,pt⟩:=reference_run refs node C hC
  have hstart : ∀ i,selected i=true → heads [] i=0 := by
    intro i hs
    have he : i=4:=by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.workspace_run RecoveryBoundedTableReferenceAppend.machine selected _ D _ p pr
    hstart (ps.trans hD)
  have hb : 2*p.steps+2 ≤ budget refs node C := by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget refs node C-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [ph,reset_heads]
    rfl
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [pt]
    rfl

theorem source_length_bound (refs : List ℕ) (W : ℕ) (hr : ∀ r∈refs,r≤W) :
    (sourceWord refs).length ≤ refs.length*(2*W+1) := by
  induction refs with
  | nil => simp [sourceWord]
  | cons ref refs ih =>
    have href:=hr ref (by simp)
    have hrest:=ih (by intro r h;exact hr r (by simp [h]))
    simp only [sourceWord,List.flatMap_cons,List.length_append,frame_length,List.length_replicate,List.length_cons]
    change 2*ref+1+(sourceWord refs).length ≤ (refs.length+1)*(2*W+1)
    nlinarith

theorem append_budget_quadratic (refs : List ℕ) (node W : ℕ)
    (hc : refs.length ≤ W) (hr : ∀ r∈refs,r≤W) (hn : node ≤ W) :
    RecoveryBoundedTableReferenceAppend.budget refs node (capacity W) ≤ 65536*(W+1)^2 := by
  have hs:=source_length_bound refs W hr
  have hm:=Nat.mul_le_mul_right (2*W+1) hc
  unfold RecoveryBoundedTableReferenceAppend.budget RecoveryBoundedTableReferenceSeek.budget
    RecoveryBoundedTagReferenceAppend.budget capacity
  nlinarith [Nat.zero_le (W^2)]

theorem budget_quadratic (refs : List ℕ) (node W : ℕ)
    (hc : refs.length ≤ W) (hr : ∀ r∈refs,r≤W) (hn : node ≤ W) :
    budget refs node (capacity W) ≤ 262144*(W+1)^2 := by
  have h:=append_budget_quadratic refs node W hc hr hn
  unfold budget
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceReset
