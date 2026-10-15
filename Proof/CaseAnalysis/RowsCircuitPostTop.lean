import Proof.CaseAnalysis.RowsCircuitTopSupport
import Proof.CaseAnalysis.RowsCircuitPublic

/-! The published top retains exactly the existing public body fields.
The actual serialized count template stays distinct from retained count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPostTop
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit SupplierPipeline
open CloseoutRowsCircuitPublishedFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem symmetric_kept (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool)
    (bank : Fin 181 → List Bool) (i : Fin 11) :
    CloseoutRowsCircuitSymmetricTop.output C n bits A bank
      (![1,297,638,1674,1688,1690,1693,1697,1698,1699,1700] i)=
      A (![1,297,638,1674,1688,1690,1693,1697,1698,1699,1700] i):=by
  apply symmetric_other
  · fin_cases i <;> decide
  · intro j he
    have hv:=congrArg Fin.val he
    rw [CloseoutRowsCircuitSymmetricTop.slots_val] at hv
    fin_cases i <;> dsimp at hv
    all_goals split_ifs at hv <;> omega

theorem threshold_kept {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool)
    (bank : Fin 1049 → List Bool) (g : SupportedNormalizedGate n) (i : Fin 12) :
    CloseoutRowsCircuitThresholdTop.output C A bank g
      (![1,297,638,1674,1688,1690,1693,1697,1698,1699,1700,622] i)=
      A (![1,297,638,1674,1688,1690,1693,1697,1698,1699,1700,622] i):=by
  apply threshold_other
  · fin_cases i <;> decide
  · intro j he
    have hv:=congrArg Fin.val he
    rw [gate_val] at hv
    fin_cases i <;> dsimp at hv
    all_goals split_ifs at hv <;> omega

theorem symmetric_count (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool)
    (bank : Fin 181 → List Bool) (hc : bank 178=UnaryTemplate.tape n) :
    CloseoutRowsCircuitSymmetricTop.output C n bits A bank 624=UnaryTemplate.tape n:=by
  rw [CloseoutRowsCircuitSymmetricTop.output,install_other _ _ _ _ (by decide)]
  change CloseoutRowsCircuitSymmetricTop.middle C A bank (CloseoutRowsCircuitSymmetricTop.slots 178)=_
  rw [CloseoutRowsCircuitSymmetricTop.middle,install_slot _ CloseoutRowsCircuitSymmetricTop.slots_injective]
  change ZeroPadding.pad 0 (bank 178)=_
  rw [ZeroPadding.pad_zero,hc]

theorem threshold_count {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool)
    (bank : Fin 1049 → List Bool) (g : SupportedNormalizedGate n)
    (hc : bank 1035=UnaryTemplate.tape n) :
    CloseoutRowsCircuitThresholdTop.output C A bank g 624=UnaryTemplate.tape n:=by
  rw [CloseoutRowsCircuitThresholdTop.output,install_other _ _ _ _ (by decide)]
  change CloseoutRowsCircuitThresholdTop.middle C A bank (gateSlots 1035)=_
  rw [CloseoutRowsCircuitThresholdTop.middle,install_slot _ gate_injective]
  change ZeroPadding.pad 0 (bank 1035)=_
  rw [ZeroPadding.pad_zero,hc]

theorem symmetric_heads (out : List Bool) : CloseoutRowsCircuitColdEntry.heads out=
    CloseoutRowsCircuitBottomEntry.heads false out 0 0:=by
  funext i
  simp only [CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads,
    CloseoutRowsCircuitBottomEntry.heads]
  split_ifs <;> first | rfl | omega

theorem threshold_heads (out : List Bool) (D : ℕ) :
    Function.update (CloseoutRowsCircuitColdThreshold.heads out) 1689 D=
      CloseoutRowsCircuitBottomEntry.heads true out D 0:=by
  funext i
  by_cases hd:i=1689
  · subst i;rfl
  by_cases hn:i=624
  · subst i;rfl
  rw [Function.update_of_ne hd,CloseoutRowsCircuitColdThreshold.heads,Function.update_of_ne hn]
  simp only [CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads,
    CloseoutRowsCircuitBottomEntry.heads,if_neg hd,if_neg hn]
  split_ifs <;> first | rfl | omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPostTop
