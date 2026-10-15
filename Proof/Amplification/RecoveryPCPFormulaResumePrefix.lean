import Proof.Amplification.RecoveryPCPFormulaResumePrefixLayout

/-! The real cold variable tautologies followed by every original PCP row.
The one fixed machine emits the exact words of outerProofRecoveryFormula. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open CanonicalRecoveryLanguage CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_words (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) :
    RecoveryFormulaPayload.input (circuitInputTautologies (2^R))++
      FieldList.stream (RecoveryPCPFormulaResume.randomWords (compactProjectionPCP (p.normalized R Q hr hq)) x)=
      FieldList.stream (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  simp only [RecoveryPCPFormulaResume.words,FieldList.stream,List.map_append,List.flatten_append]
  rfl

theorem prefix_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom machine (budget cap R Q (Codec.clauses p).length)
      ⟨machine.start,heads p R Q cap logCap resetCap,input p R Q cap logCap resetCap⟩=some r ∧
      r.final.tapes 276=FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) ∧
      r.final.heads 276=(FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length ∧
      r.steps≤budget cap R Q (Codec.clauses p).length := by
  obtain ⟨cold,hcold,ct,ch,_c241,_h241,_c242,_h242,cs⟩ := RecoveryTseitinTautology.Cold.cold_run (2^R)
  obtain ⟨a,ha,_ac,as_,ah,at_,akeep⟩ := RecoveryFocus.dock prefixSlots prefix_injective
    RecoveryTseitinTautology.Cold.machine _ (heads p R Q cap logCap resetCap) (input p R Q cap logCap resetCap) _
    (prefix_heads p R Q cap logCap resetCap)
    (by intro j; exact install_slot prefixSlots prefix_injective _ _ j) cold hcold
  let out := RecoveryFormulaPayload.input (circuitInputTautologies (2^R))
  obtain ⟨rows,hrows,rf,rs⟩ := RecoveryPCPFormulaResumeRows.rows_run p R Q hr hq x cap logCap resetCap out hc hl hz
  have dh : ∀ j,a.final.heads (rowSlots j)=
      (RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) out).heads j := by
    intro j
    rw [RecoveryPCPFormulaResumeRows.input_heads_output]
    by_cases hj : j.val=276
    · have he : j=276 := Fin.ext hj
      subst j
      change a.final.heads (prefixSlots 239)=out.length
      exact (ah 239).trans ch
    · rw [if_neg hj,(akeep _ (prefix_outside j hj)).1]
      simp only [heads,rowSlots,Fin.addCases_left]
  have dt : ∀ j,a.final.tapes (rowSlots j)=
      (RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) out).tapes j := by
    intro j
    rw [RecoveryPCPFormulaResumeRows.input_tapes_output]
    by_cases hj : j.val=276
    · have he : j=276 := Fin.ext hj
      subst j
      change a.final.tapes (prefixSlots 239)=out
      exact (at_ 239).trans ct
    · rw [if_neg hj,(akeep _ (prefix_outside j hj)).2]
      exact input_rows p R Q cap logCap resetCap j
  obtain ⟨b,hb,_bc,bs,bh,bt,_bkeep⟩ := RecoveryFocus.dock rowSlots row_injective
    RecoveryPCPFormulaResumeRows.machine _ a.final.heads a.final.tapes _ dh dt rows hrows
  have hall := Composition.run_join prefixMachine rowsMachine _ _ _ a b ha hb
  have final_word : out++FieldList.stream (RecoveryPCPFormulaResume.randomWords
      (compactProjectionPCP (p.normalized R Q hr hq)) x)=
      FieldList.stream (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) :=
    prefix_words p R Q hr hq x
  refine ⟨_,hall,?_,?_,?_⟩
  · change b.final.tapes (rowSlots 276)=_
    rw [bt,rf]
    change ZeroPadding.pad 0 (RecoveryPCPFormulaResumeRow.initialTapes cap (DedupBytes.fields p)
      (out++FieldList.stream (RecoveryPCPFormulaResume.randomWords (compactProjectionPCP (p.normalized R Q hr hq)) x))
      0 (Codec.clauses p).length p R Q (bitInputOfCode R (2^R-1)) logCap 276)=_
    rw [RecoveryPCPFormulaResumeRows.initial_tapes_output,if_pos (by decide : (276 : Fin 317).val=276),
      ZeroPadding.pad_zero,final_word]
  · change b.final.heads (rowSlots 276)=_
    rw [bh,rf]
    change (out++FieldList.stream (RecoveryPCPFormulaResume.randomWords
      (compactProjectionPCP (p.normalized R Q hr hq)) x)).length=_
    rw [final_word]
  · change a.steps+1+b.steps≤_
    rw [as_,bs]
    unfold budget
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
