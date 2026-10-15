import Proof.Amplification.RecoveryCaseOnePaddedBitRun

/-! The exact two physical data ports of the whole Case-1 bit program. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

theorem input_lookup (k : Nat) (word address : List Bool) (i : Fin (tapes source amp k)) :
    input source amp k word address i=if i.val=0 then word else
      if i.val=base source amp k+16 then frame address else [] := by
  have hb : 0<base source amp k := by
    dsimp [base,RecoveryCaseOneHierarchy.tapes,RecoveryCaseOneConstruct.tapes]
    omega
  refine Fin.addCases (m:=base source amp k) (n:=45) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left,SourceHandoff.sourceTapes,Fin.val_castAdd]
    have hj : j.val≠base source amp k+16 := by have hlt:=j.isLt; omega
    rw [if_neg hj]
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    have hn : base source amp k+j.val≠0 := by omega
    rw [if_neg hn]
    have he : base source amp k+j.val=base source amp k+16 ↔j.val=16 := by omega
    simp only [he]

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
