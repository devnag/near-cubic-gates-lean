import Proof.CaseAnalysis.RowsCircuitWords

/-! The two original top decisions retain the prefix verdict and leave
the final circuit flag false until the common body decides its guards. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdFlags
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem symmetric_middle_kept (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool)
    (i : Fin 2) : CloseoutRowsCircuitSymmetricTop.middle C A bank (![638,1700] i)=A (![638,1700] i):=by
  apply install_other
  intro j he
  have hv:=congrArg Fin.val he
  rw [CloseoutRowsCircuitSymmetricTop.slots_val] at hv
  fin_cases i <;> dsimp at hv
  all_goals split_ifs at hv <;> omega

theorem threshold_middle_kept (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool)
    (i : Fin 2) : CloseoutRowsCircuitThresholdTop.middle C A bank (![638,1700] i)=A (![638,1700] i):=by
  apply install_other
  intro j he
  have hv:=congrArg Fin.val he
  rw [gate_val] at hv
  fin_cases i <;> dsimp at hv
  all_goals split_ifs at hv <;> omega

theorem symmetric_middle_flag (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool) :
    readTapeBit (CloseoutRowsCircuitSymmetricTop.middle C A bank 1676) 0=readTapeBit (bank 179) 0:=by
  change readTapeBit (CloseoutRowsCircuitSymmetricTop.middle C A bank
    (CloseoutRowsCircuitSymmetricTop.slots 179)) 0=_
  rw [CloseoutRowsCircuitSymmetricTop.middle,install_slot _ CloseoutRowsCircuitSymmetricTop.slots_injective]
  exact ZeroPadding.read_pad _ _ _

theorem symmetric_output_flag (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool)
    (bank : Fin 181 → List Bool) :
    readTapeBit (CloseoutRowsCircuitSymmetricTop.output C n bits A bank 1676) 0=readTapeBit (bank 179) 0:=by
  rw [CloseoutRowsCircuitSymmetricTop.output,install_other _ _ _ _ (by decide)]
  exact symmetric_middle_flag C A bank

theorem threshold_middle_flag (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool) :
    readTapeBit (CloseoutRowsCircuitThresholdTop.middle C A bank 1676) 0=readTapeBit (bank 1037) 0:=by
  change readTapeBit (CloseoutRowsCircuitThresholdTop.middle C A bank (gateSlots 1037)) 0=_
  rw [CloseoutRowsCircuitThresholdTop.middle,install_slot _ gate_injective]
  exact ZeroPadding.read_pad _ _ _

theorem threshold_output_flag {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool)
    (bank : Fin 1049 → List Bool) (g : SupportedNormalizedGate n) :
    readTapeBit (CloseoutRowsCircuitThresholdTop.output C A bank g 1676) 0=readTapeBit (bank 1037) 0:=by
  rw [CloseoutRowsCircuitThresholdTop.output,install_other _ _ _ _ (by decide)]
  exact threshold_middle_flag C A bank

theorem cold_heads (out : List Bool) (i : Fin 3) :
    CloseoutRowsCircuitColdEntry.heads out (![638,1676,1700] i)=0:=by
  fin_cases i <;> rfl

theorem threshold_heads (out : List Bool) (D : ℕ) (i : Fin 3) :
    (Function.update (CloseoutRowsCircuitColdThreshold.heads out) 1689 D) (![638,1676,1700] i)=0:=by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdFlags
