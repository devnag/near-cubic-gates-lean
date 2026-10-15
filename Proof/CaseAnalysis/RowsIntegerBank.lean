import Proof.CaseAnalysis.RowsIntegerBankLayout

/-! One real sweep allocates the signed-integer stream bank from its cold
capacity driver. The source, native output and codec flag are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 215)

theorem bank_ready (cap : ℕ) (out source : List Bool) (flag : Bool) (hcap : 1≤cap) :
    ReadyRun machine (2*cap+4) (input cap out source flag)
      (CloseoutRowsIntegerRound.data cap [] out source flag):=by
  have raw:ReadyRun (RecoveryScratchErase.resetMachine 215) (2*cap+4)
      (Fin.addCases (Fin.addCases (fun _ : Fin 215=>[]) (fun _ : Fin 1=>List.replicate cap true))
        (fun _ : Fin 1=>[])) (PCPTraversal.clearedLocal 215 cap (cap+1)):=by
    unfold PCPTraversal.clearedLocal
    simpa only [List.replicate_zero,PCPTraversal.clearedLocal,Nat.zero_max,Nat.max_self] using
      RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 215=>[]) (by intro i;simp)
  have h:=raw.focus slots slots_injective (input cap out source flag) (by
    intro i
    refine Fin.addCases (m:=216) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=215) (n:=1) ?_ ?_ j
      · intro k
        simp only [Fin.addCases_left]
        have he:(k.castAdd 1).castAdd 1=k.castAdd 2:=Fin.ext rfl
        rw [he]
        exact input_work cap out source flag k
      · intro k
        have hk:k=0:=Fin.eq_zero k
        subst k
        rfl
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl)
  change ReadyRun machine (2*cap+4) (input cap out source flag) (erased cap out source flag) at h
  rw [erased_data cap out source flag hcap] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerBank
