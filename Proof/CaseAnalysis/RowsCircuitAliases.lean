import Proof.CaseAnalysis.RowsCircuitMeaning

/-! The aliased original raw word and paid internal driver survive every
top branch. Rejection requires no private workspace restoration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdAliases
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem symmetric_middle (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool)
    (i : Fin 2) : CloseoutRowsCircuitSymmetricTop.middle C A bank (![1,1694] i)=A (![1,1694] i):=by
  apply install_other
  intro j he
  have hv:=congrArg Fin.val he
  rw [CloseoutRowsCircuitSymmetricTop.slots_val] at hv
  fin_cases i <;> dsimp at hv
  all_goals split_ifs at hv <;> omega

theorem threshold_middle (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool)
    (i : Fin 2) : CloseoutRowsCircuitThresholdTop.middle C A bank (![1,1694] i)=A (![1,1694] i):=by
  apply install_other
  intro j he
  have hv:=congrArg Fin.val he
  rw [gate_val] at hv
  fin_cases i <;> dsimp at hv
  all_goals split_ifs at hv <;> omega

theorem threshold_driver {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool)
    (g : SupportedNormalizedGate n) : CloseoutRowsCircuitThresholdTop.output C A bank g 1694=List.replicate C true:=by
  exact install_slot topPublishSlots topPublish_injective A _ 5

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdAliases
