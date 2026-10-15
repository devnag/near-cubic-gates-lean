import Proof.Amplification.RecoveryPCPFormulaResumeState

/-! One fixed ordinary machine constructs the exact original outer-proof
formula from the five literal hierarchy fields. All drivers, banks, tautologies,
randomness rows, framing and balanced-CNF serialization are executed here. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (R Q count : Nat) (words : List (List Bool)) :=
  RecoveryPCPFormulaResumeColdScalars.budget R.bits Q.bits+1+
    RecoveryPCPFormulaResumeSerialize.budget (RecoverySourceClauseLoad.uniformBudget Q R) R Q count words

theorem cold_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ r,
    run machine (budget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (input p R Q)=some r ∧
      r.final.tapes 783=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.steps≤budget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  obtain ⟨scalars,hscalars,o3,o17,o31,o37,o58,o61,o64⟩ :=
    RecoveryPCPFormulaResumeColdScalars.scalars_ready R.bits Q.bits
  simp only [CanonicalPositiveOutput.nat_bits_value] at o3 o17 o31 o37 o58 o61 o64
  have hfirst:=hscalars.focus scalarSlots scalar_injective (input p R Q) (scalar_input p R Q)
  obtain ⟨a,ha,aT,ah,aSteps⟩ := hfirst
  obtain ⟨code,hcode,ct,cs⟩ := RecoveryPCPFormulaResumeSerialize.entry_run p R Q hr hq x
  have hh : ∀ i : Fin 716,a.final.heads (formulaSlots i)=0 := fun i=>ah (formulaSlots i)
  have ht : ∀ i : Fin 716,a.final.tapes (formulaSlots i)=
      RecoveryPCPFormulaResumeSerialize.entryData p R Q (RecoverySourceClauseLoad.uniformBudget Q R) i := by
    intro i
    rw [aT]
    exact scalar_dock p R Q scalars o3 o17 o31 o37 o58 o61 o64 i
  obtain ⟨b,hb,_bc,bs,_bh,bt,_bk⟩ := RecoveryFocus.dock formulaSlots formula_injective
    RecoveryPCPFormulaResumeSerialize.machine _ a.final.heads a.final.tapes _ hh ht code hcode
  have whole:=Composition.run_join first last _ _ _ a b ha hb
  refine ⟨_,whole,?_,?_⟩
  · change b.final.tapes (formulaSlots 714)=_
    rw [bt,ct]
  · change a.steps+1+b.steps≤_
    rw [bs]
    unfold budget
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
