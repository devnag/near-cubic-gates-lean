import Proof.MachineModel.OrdinarySourceSATLiftPairs

/-! Exact tape interfaces between the four executed pair calls. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_zero (cap : ℕ) (source bits : List Bool) (i : Fin 38) :
    prepared cap source bits (pairSlots 0 i)=PCPPairReusable.input cap [true] bits i := by
  rw [show pairSlots 0 i=bank 0 i by simp [pairSlots]]
  rw [prepared_bank]
  by_cases h2 : i.val=2
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2]
  by_cases h3 : i.val=3
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h3]
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2,h3,ZeroPadding.pad]

theorem input_one (cap : ℕ) (source bits left : List Bool) (out : Fin 38 → List Bool)
    (ho : out 26=ZeroPadding.pad cap (frame left)) (i : Fin 38) :
    install (pairSlots 0) (prepared cap source bits) out (pairSlots 1 i)=
      PCPPairReusable.input cap left [true] i := by
  by_cases h2 : i.val=2
  · have hi : i=2 := Fin.ext h2
    subst i
    rw [show pairSlots 1 2=pairSlots 0 26 by rfl,install_slot _ (pair_injective 0)]
    simpa [PCPPairReusable.input,PCPPairCanonical.input] using ho
  rw [show pairSlots 1 i=bank 1 i by simp [pairSlots,h2]]
  rw [install_pair_above 0 _ _ _ (by dsimp [bank]; omega),prepared_bank]
  by_cases h3 : i.val=3
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h3]
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2,h3,ZeroPadding.pad]

theorem input_two (cap : ℕ) (source bits left : List Bool)
    (out0 out1 : Fin 38 → List Bool) (ho : out1 26=ZeroPadding.pad cap (frame left)) (i : Fin 38) :
    install (pairSlots 1) (install (pairSlots 0) (prepared cap source bits) out0) out1 (pairSlots 2 i)=
      PCPPairReusable.input cap left [true] i := by
  by_cases h2 : i.val=2
  · have hi : i=2 := Fin.ext h2
    subst i
    rw [show pairSlots 2 2=pairSlots 1 26 by rfl,install_slot _ (pair_injective 1)]
    simpa [PCPPairReusable.input,PCPPairCanonical.input] using ho
  rw [show pairSlots 2 i=bank 2 i by simp [pairSlots,h2]]
  rw [install_pair_above 1 _ _ _ (by dsimp [bank]; omega),
    install_pair_above 0 _ _ _ (by dsimp [bank]; omega),prepared_bank]
  by_cases h3 : i.val=3
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h3]
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2,h3,ZeroPadding.pad]

theorem input_three (cap : ℕ) (source bits right : List Bool)
    (out0 out1 out2 : Fin 38 → List Bool) (ho : out2 26=ZeroPadding.pad cap (frame right)) (i : Fin 38) :
    install (pairSlots 2) (install (pairSlots 1)
      (install (pairSlots 0) (prepared cap source bits) out0) out1) out2 (pairSlots 3 i)=
      PCPPairReusable.input cap [true] right i := by
  by_cases h3 : i.val=3
  · have hi : i=3 := Fin.ext h3
    subst i
    rw [show pairSlots 3 3=pairSlots 2 26 by rfl,install_slot _ (pair_injective 2)]
    simpa [PCPPairReusable.input,PCPPairCanonical.input] using ho
  rw [show pairSlots 3 i=bank 3 i by simp [pairSlots,h3]]
  rw [install_pair_above 2 _ _ _ (by dsimp [bank]; omega),
    install_pair_above 1 _ _ _ (by dsimp [bank]; omega),
    install_pair_above 0 _ _ _ (by dsimp [bank]; omega),prepared_bank]
  by_cases h2 : i.val=2
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2]
  · simp [PCPPairReusable.input,PCPPairCanonical.input,h2,h3,ZeroPadding.pad]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
