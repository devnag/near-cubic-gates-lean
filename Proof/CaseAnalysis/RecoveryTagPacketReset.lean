import Proof.CaseAnalysis.RecoveryTagPacketRun

/-! Rewind the actual five-reference packet with the existing reusable D
log. The graph counter has advanced four times and every head returns to zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacketReset
open LocalBitMultitape RepairRepresentation
open RecoveryBoundedTagPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 8):=decide (i=7)
noncomputable def machine:=MaskedReset.machine RecoveryBoundedTagPacket.machine selected
def budget (constant current C : ℕ):=2*RecoveryBoundedTagPacket.budget constant current C+2
noncomputable def entry (constant current C D : ℕ):=
  ZeroPadding.config (Rewind.Workspace.capacities 8 D)
    (Rewind.recording (⟨RecoveryBoundedTagPacket.machine.start,heads [],data current constant C []⟩) 0)
def finalData (constant current C D : ℕ) : Fin 9→List Bool:=
  Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
    (data (current+4) constant C (word constant current)) (fun _=>List.replicate D false)

theorem entry_heads (constant current C D : ℕ) :
    (entry constant current C D).heads=fun _=>0 := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;> rfl
  · simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,Fin.addCases_right]

theorem entry_tapes (constant current C D : ℕ) :
    (entry constant current C D).tapes=
      Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool)
        (data current constant C []) (fun _=>List.replicate D false) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero]
  · simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      Rewind.Workspace.capacities,Fin.addCases_right]
    rfl

theorem reset_heads (out : List Bool) :
    (fun i=>if selected i then 0 else heads out i)=fun _=>0 := by
  funext i
  fin_cases i <;> rfl

theorem reset_run (constant current C D : ℕ)
    (hk : 2*constant+1 ≤ C) (hi : 2*(current+3)+1 ≤ C)
    (hD : RecoveryBoundedTagPacket.budget constant current C ≤ D) :
    ∃ r,runFrom machine (budget constant current C) (entry constant current C D)=some r ∧
      r.steps ≤ budget constant current C ∧ r.final.heads=(fun _=>0) ∧
      r.final.tapes=finalData constant current C D := by
  obtain ⟨p,pr,ps,ph,pt⟩:=packet_run constant current C [] hk hi
  have hstart : ∀ i,selected i=true → heads [] i=0 := by
    intro i hs
    have he : i=7:=by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.workspace_run RecoveryBoundedTagPacket.machine selected _ D _ p pr hstart (ps.trans hD)
  have hb : 2*p.steps+2 ≤ budget constant current C := by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget constant current C-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [ph,reset_heads]
    funext i
    exact Fin.addCases (fun _=>by simp only [Fin.addCases_left]) (fun _=>by simp only [Fin.addCases_right]) i
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config]
    rw [pt]
    rfl

theorem packet_fits (constant current W : ℕ) (hk : constant ≤ W) (hi : current ≤ W) :
    (word constant current).length ≤ RecoveryBoundedSelectorLoop.capacity W := by
  rw [word_length]
  unfold RecoveryBoundedSelectorLoop.capacity
  nlinarith [Nat.zero_le (W^2)]

theorem budget_quadratic (constant current W : ℕ) (hk : constant ≤ W) (hi : current ≤ W) :
    budget constant current (RecoveryBoundedSelectorLoop.capacity W) ≤ 2097154*(W+1)^2 := by
  have h:=RecoveryBoundedTagPacket.budget_quadratic constant current W hk hi
  unfold budget
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacketReset
