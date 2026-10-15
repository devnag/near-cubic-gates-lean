import Proof.Amplification.RecoveryCaseOnePaddedBitLayout

/-! Exact generated output and retained-address handoff at the ordinary
Case-1 bit consumer. Every evaluator scratch tape is still empty. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

theorem eval_tapes (k : Nat) (word address payload : List Bool) (out : Fin (base source amp k)→List Bool)
    (hout : out (RecoveryCaseOneHierarchy.ports source amp k).outputTape=frame payload) (i : Fin 46) :
    install (sourceSlots source amp k) (input source amp k word address) out (evalSlots source amp k i)=
      RecoveryCaseOnePaddedEvaluation.input payload address i := by
  by_cases h0 : i.val=0
  · simp only [evalSlots,RecoveryCaseOnePaddedEvaluation.input,h0,ite_true]
    exact (install_slot (sourceSlots source amp k) (source_injective source amp k) _ out
      (RecoveryCaseOneHierarchy.ports source amp k).outputTape).trans hout
  · have hp : (1 : Nat)≤(i : Fin 46).val := by omega
    let j : Fin 45:=⟨i.val-1,by have hi:=i.isLt; omega⟩
    have he : evalSlots source amp k i=j.natAdd (base source amp k) := by
      apply Fin.ext
      simp only [evalSlots,h0,ite_false,Fin.val_natAdd]
      dsimp only [j]
      omega
    rw [he,install_other _ _ _ _ (by
      intro l hl
      have hv:=congrArg (fun i : Fin (tapes source amp k)=>i.val) hl
      have hb:=l.isLt
      change l.val=base source amp k+j.val at hv
      omega)]
    simp only [input,Fin.addCases_right,RecoveryCaseOnePaddedEvaluation.input,h0,ite_false]
    have hj : j.val=16 ↔i.val=17 := by dsimp [j]; omega
    simp only [hj]

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
