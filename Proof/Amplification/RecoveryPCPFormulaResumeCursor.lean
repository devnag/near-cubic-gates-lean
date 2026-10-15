import Proof.Amplification.RecoveryPCPFormulaResumeRun

/-! The hierarchy source retains the original clause counter at head one.
Pay its single-cell retreat before executing the complete cold constructor. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countHeads (i : Fin 785) := if i.val=68 then 1 else 0
def retreat : Machine 785 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some
    ⟨1,fun _=>none,fun i=>if i.val=68 then .left else .stay⟩ else none

theorem retreat_step (data : Fin 785→List Bool) :
    step retreat ⟨0,countHeads,data⟩=some ⟨1,fun _=>0,data⟩ := by
  simp only [step,retreat,ite_true,Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    simp only [applyAction,countHeads]
    split_ifs <;> rfl
  · funext i
    simp only [applyAction]

noncomputable def cursorMachine := Composition.machine retreat machine
def cursorBudget (R Q count : Nat) (words : List (List Bool)) := budget R Q count words+2

theorem cursor_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ r,
    runFrom cursorMachine (cursorBudget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      ⟨cursorMachine.start,countHeads,input p R Q⟩=some r ∧
      r.final.tapes 783=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.steps≤cursorBudget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  obtain ⟨a,ha,af,aSteps⟩ := (Timed.single (by rfl) (retreat_step (input p R Q))).run (by rfl)
  obtain ⟨b,hb,bt,bSteps⟩ := cold_run p R Q hr hq x
  have he : Composition.restart a.final machine.start=initialConfiguration machine (input p R Q) := by
    rw [af]
    rfl
  change runFrom machine _ (initialConfiguration machine (input p R Q))=some b at hb
  rw [←he] at hb
  have whole:=Composition.run_join retreat machine _ _ _ a b ha hb
  have hbudget : 1+1+budget R Q (Codec.clauses p).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)=
      cursorBudget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
    unfold cursorBudget
    omega
  rw [hbudget] at whole
  refine ⟨_,whole,bt,?_⟩
  change a.steps+1+b.steps≤_
  unfold cursorBudget
  omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
