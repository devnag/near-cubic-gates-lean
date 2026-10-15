import Proof.CaseAnalysis.CloseoutRowsEstimatorRetained
import Proof.CaseAnalysis.CaseTwoAddressRetention

/-! The original native cut bytes are read-only throughout the estimator.
Together with the returned zero head this preserves the native C support
needed by the enclosing row-generation bank's own paid clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.NativeReadOnly
open LocalBitMultitape RepairRepresentation RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scan : NoWrite Scan.machine 0:=by
  intro q bits a ha
  simp only [Scan.machine] at ha
  split_ifs at ha <;>cases ha <;>rfl
theorem prepare : NoWrite Prepare.machine 52:=by
  apply composition
  · exact unselected Prepare.fieldSlots Fields.machine 52 (by decide)
  · change NoWrite (RecoveryFocus.machine Prepare.scanSlots Scan.readyMachine) (Prepare.scanSlots 0)
    exact focus _ (by decide) _ 0 (rewind Scan.machine 0 scan)
theorem header : NoWrite Header.machine 52:=by
  apply composition
  · intro q bits a ha
    obtain ⟨b,_hb,he⟩:=Option.map_eq_some_iff.mp ha
    subst a
    change (TapeEmbedding.action 3 b).write ((0 : Fin 3).natAdd 52)=none
    simp only [TapeEmbedding.action,Fin.addCases_right]
  · change NoWrite (RecoveryFocus.machine Header.slots Tail.machine) (Header.slots 0)
    apply focus _ (by decide)
    intro q bits a ha
    simp only [Tail.machine] at ha
    split_ifs at ha <;>cases ha <;>rfl
theorem framed : NoWrite Framed.machine 52:=by
  apply composition
  · exact embedded 4 Prepare.machine 52 prepare
  · change NoWrite (RecoveryFocus.machine Framed.slots Header.framed) (Framed.slots 52)
    apply focus _ Framed.injective
    exact CloseoutCaseTwo.AddressRetention.frame_readonly Header.machine 51 52 (by decide) header
theorem cold : NoWrite Cold.machine 52:=by
  apply composition
  · change NoWrite (RecoveryFocus.machine Cold.slots CompetitorRecordRewind.machine) (Cold.slots 0)
    apply focus _ (by decide)
    intro q bits a ha
    simp only [CompetitorRecordRewind.machine] at ha
    split_ifs at ha <;>cases ha <;>rfl
  · exact embedded 2 Framed.machine 52 framed

def slot (p : Program) : Fin (WholePrefix.tapes p):=(52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)
theorem whole (a : WilliamsAlgorithm) : NoWrite (Whole.machine a) (slot (CompetitorCrossScheduler.producer a)):=by
  apply composition
  · exact embedded _ Cold.machine 52 cold
  · apply unselected
    intro j he
    have hv:=congrArg Fin.val he
    simp only [WholePrefix.slots,slot,Fin.val_castAdd] at hv
    split_ifs at hv <;>simp only [Fin.val_natAdd] at hv <;>omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.NativeReadOnly
