import Proof.MachineModel.OrdinarySourceSATLiftPrepared

/-! The four actual canonical-pair calls of the marker kernel. Each call
uses a distinct finite work bank; its output is the next call's operand. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pair_upper (k : Fin 4) (i : Fin 38) :
    (pairSlots k i).val < 3+38*(k.val+1) := by
  have hi := i.isLt
  fin_cases k <;> dsimp [pairSlots,bank] <;> (try split_ifs) <;> (try dsimp) <;> omega

theorem install_pair_above (k : Fin 4) (ambient : Fin 156 → List Bool)
    (out : Fin 38 → List Bool) (i : Fin 156) (hi : 3+38*(k.val+1) ≤ i.val) :
    install (pairSlots k) ambient out i = ambient i := by
  apply install_other
  intro j he
  have h := pair_upper k j
  rw [he] at h
  omega

theorem install_pair_small (k : Fin 4) (ambient : Fin 156 → List Bool)
    (out : Fin 38 → List Bool) (i : Fin 156) (hi : i.val < 3) :
    install (pairSlots k) ambient out i = ambient i := by
  apply install_other
  intro j he
  have h := (pair_work k j).1
  rw [he] at h
  omega

theorem prepared_bank (cap : ℕ) (source bits : List Bool) (k : Fin 4) (i : Fin 38) :
    prepared cap source bits (bank k i) =
      if k.val=0 ∧ i.val=3 then ZeroPadding.pad cap (frame bits)
      else if i.val=(if k.val=0 ∨ k.val=3 then 2 else 3) then
        ZeroPadding.pad cap (frame [true]) else List.replicate cap false := by
  fin_cases k <;> fin_cases i <;>
    simp [prepared,printed,cleared,oneSlot,bank,Function.update]

theorem pair_focus (k : Fin 4) (cap : ℕ) (left right : List Bool)
    (ambient : Fin 156 → List Bool)
    (hin : ∀ i,ambient (pairSlots k i)=PCPPairReusable.input cap left right i)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1 ≤ cap) :
    ∃ out : Fin 38 → List Bool,
      ClockJoin.ReadyRun (focused (pairSlots k) PCPPairCanonical.machine).2
        (PCPPairCanonical.budget left right) ambient (install (pairSlots k) ambient out) ∧
      out 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      (∀ i,(out i).length ≤ cap) := by
  obtain ⟨out,hr,hf,hb⟩ := PCPPairReusable.pair_run cap left right hpos hcap
  exact ⟨out,hr.focus (pairSlots k) (pair_injective k) ambient hin,hf,hb⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
