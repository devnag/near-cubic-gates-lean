import Proof.Amplification.RecoveryPCPFormulaResumeSearchParts

/-! Pay the ordinary constructor's return scan so the actual payload and
archived proof count are available together at head zero for request assembly. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readyMachine := Rewind.machine machine
noncomputable def readyInput (p : RawProjectionPCP) (R Q : Nat) : Fin 789→List Bool :=
  Fin.addCases (m:=788) (n:=1) (motive:=fun _=>List Bool) (input p R Q) (fun _=>[])
def readyBudget (R Q count : Nat) (words : List (List Bool)) := 2*budget R Q count words+2

theorem ready_parts (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ out,
    ClockJoin.ReadyRun readyMachine (readyBudget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (readyInput p R Q) out ∧
      out 783=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      out 787=frame (List.replicate (2^R) true) := by
  obtain ⟨base,hbase,b783,b787,bSteps⟩ := parts_run p R Q hr hq x
  obtain ⟨r,hrun,rt,rh,rSteps,_rPeak⟩ := Rewind.reset_run machine _ _ base hbase
  have hbudget : 2*base.steps+2≤readyBudget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
    unfold readyBudget
    omega
  have hm:=run_moreFuel readyMachine _
    (readyBudget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hbudget] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rSteps.trans_le hbudget⟩,
    (rt (783 : Fin 788)).trans b783,(rt (787 : Fin 788)).trans b787⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
