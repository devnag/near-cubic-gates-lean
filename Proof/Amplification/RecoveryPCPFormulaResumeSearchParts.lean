import Proof.Amplification.RecoveryPCPFormulaResumeSearchLayout

/-! The actual original formula and its framed unary proof count are now
produced together from the same five original source fields. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_keeps (ambient : Fin 788→List Bool) (out : Fin 4→List Bool)
    (h0 : out 0=ambient 58) (i : Fin 785) :
    install countSlots ambient out (i.castAdd 3)=ambient (i.castAdd 3) := by
  by_cases hi : i.val=58
  · have he : i=(58 : Fin 785) := Fin.ext hi
    subst i
    exact (install_slot countSlots count_injective ambient out 0).trans h0
  · apply install_other
    intro j hj
    have hv:=congrArg (fun i : Fin 788=>i.val) hj
    have hib:=i.isLt
    fin_cases j
    · exact hi hv.symm
    all_goals dsimp [countSlots] at hv; omega

def budget (R Q count : Nat) (words : List (List Bool)) :=
  RecoveryPCPFormulaResumeColdScalars.budget R.bits Q.bits+1+
    RecoveryPCPFormulaResumeSearchCount.budget (2^R-1)+1+
      RecoveryPCPFormulaResumeSerialize.budget (RecoverySourceClauseLoad.uniformBudget Q R) R Q count words

theorem parts_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ r,
    run machine (budget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (input p R Q)=some r ∧
      r.final.tapes 783=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.final.tapes 787=frame (List.replicate (2^R) true) ∧
      r.steps≤budget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  obtain ⟨scalars,hscalars,o3,o17,o31,o37,o58,o61,o64⟩ :=
    RecoveryPCPFormulaResumeColdScalars.scalars_ready R.bits Q.bits
  simp only [CanonicalPositiveOutput.nat_bits_value] at o3 o17 o31 o37 o58 o61 o64
  let a:=install scalarSlots (input p R Q) scalars
  have ha:=hscalars.focus scalarSlots scalar_injective (input p R Q) (scalar_input p R Q)
  have a58 : a 58=CompareMachine.word (2^R-1) :=
    (install_slot scalarSlots scalar_injective _ scalars 58).trans o58
  obtain ⟨counts,hcounts,c0,c3⟩ := RecoveryPCPFormulaResumeSearchCount.proof_count_ready R
  let b:=install countSlots a counts
  have hb:=hcounts.focus countSlots count_injective a (by
    intro i; fin_cases i
    · exact a58
    · exact scalar_fresh p R Q scalars 0
    · exact scalar_fresh p R Q scalars 1
    · exact scalar_fresh p R Q scalars 2)
  have joined:=ClockJoin.join first countMachine _ _ _ _ _ ha hb
  obtain ⟨aRun,haRun,aT,aH,aSteps⟩ := joined
  obtain ⟨code,hcode,ct,cs⟩ := RecoveryPCPFormulaResumeSerialize.entry_run p R Q hr hq x
  have hkeep : ∀ i : Fin 785,b (i.castAdd 3)=a (i.castAdd 3) :=
    count_keeps a counts (c0.trans a58.symm)
  have ht : ∀ i : Fin 716,aRun.final.tapes (formulaSlots i)=
      RecoveryPCPFormulaResumeSerialize.entryData p R Q (RecoverySourceClauseLoad.uniformBudget Q R) i := by
    intro i
    rw [aT]
    change b ((RecoveryPCPFormulaResumeCold.formulaSlots i).castAdd 3)=_
    rw [hkeep]
    dsimp only [a]
    rw [scalar_old]
    exact RecoveryPCPFormulaResumeCold.scalar_dock p R Q scalars o3 o17 o31 o37 o58 o61 o64 i
  obtain ⟨lastRun,hlast,_lc,lSteps,_lh,lt,lk⟩ := RecoveryFocus.dock formulaSlots formula_injective
    RecoveryPCPFormulaResumeSerialize.machine _ aRun.final.heads aRun.final.tapes _
    (fun i=>aH (formulaSlots i)) ht code hcode
  have whole:=Composition.run_join counted last _ _ _ aRun lastRun haRun hlast
  refine ⟨_,whole,?_,?_,?_⟩
  · change lastRun.final.tapes (formulaSlots 714)=_
    rw [lt,ct]
  · change lastRun.final.tapes 787=_
    rw [(lk 787 (by
      intro i h
      have hv:=congrArg (fun i : Fin 788=>i.val) h
      have hi:=(RecoveryPCPFormulaResumeCold.formulaSlots i).isLt
      change (RecoveryPCPFormulaResumeCold.formulaSlots i).val=787 at hv
      omega)).2,aT]
    exact (install_slot countSlots count_injective a counts 3).trans c3
  · change aRun.steps+1+lastRun.steps≤_
    rw [lSteps]
    unfold budget
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearch
