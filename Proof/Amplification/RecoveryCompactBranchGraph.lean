import Proof.Amplification.RecoveryMarkerReplayCall

/-! One prepared compact branch from the retained original code: replay
the marker, perform the selected actual payload checker on success, or
physically copy the marker's false result to the common answer cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCompactBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable def sizes : Fin 3→Nat := ![stateCount replayMachine,stateCount RecoveryMarkerPayload.machine,2]
noncomputable def programs : (j : Fin 3)→Machine 212 (sizes j)
  | ⟨0,_⟩=>replayMachine
  | ⟨1,_⟩=>RecoveryMarkerPayload.machine
  | ⟨2,_⟩=>RecoveryBankPair.flagMachine 107 28
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 212→Bool) : Option (Fin 3) :=
  ![some (if bits 28 then 1 else 2),none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (width : Nat) := RecoveryMarker.budget width+RecoveryMarkerPayload.budget width+4

theorem budget_le (width : Nat) : budget width ≤ 1073741824*(width+1)^3 := by
  have h := RecoveryMarkerPayload.budget_le width
  have hpow : (width+1)^2 ≤ (width+1)^3 := by
    calc
      _ = 1*(width+1)^2 := by omega
      _ ≤ (width+1)*(width+1)^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hpos : 1 ≤ (width+1)^3 := Nat.one_le_pow _ _ (by omega)
  unfold budget RecoveryMarker.budget
  omega

theorem finish_run (width code n : Nat) (source : Configuration 212 (Fintype.card (RecoveryCalls.Control sizes)))
    (outHeads : Fin 212→Nat) (outTapes : Fin 212→List Bool)
    (h : Timed machine n source (RecoveryCalls.stopped sizes outHeads outTapes))
    (hb : n ≤ budget width) (hh : outHeads 107=0) (ht : ∃ bit,outTapes 107=[bit])
    (hs : outTapes 107=[true] → RepairSource.RecoveryOracle.correctedSat code=true) :
    ∃ r,runFrom machine (budget width) source=some r ∧
      r.steps ≤ 1073741824*(width+1)^3 ∧ r.final.heads 107=0 ∧
      (∃ bit,r.final.tapes 107=[bit]) ∧
      (r.final.tapes 107=[true] → RepairSource.RecoveryOracle.correctedSat code=true) := by
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine n (budget width-n) source r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,hm,(hsteps.le.trans hb).trans (budget_le width),?_,?_,?_⟩
  · rw [hf]; exact hh
  · rw [hf]; exact ht
  · rw [hf]; exact hs

end NearCubicWires.RepairOrdinary.RecoveryCompactBranch
