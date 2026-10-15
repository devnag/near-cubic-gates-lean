import Proof.Hierarchy.HierarchyStreams

/-! Physical retained scalar ABI for the serializer following the full
hierarchy/source/normalization execution. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem dimension_injective (k : ℕ) : Function.Injective (dimension source k) :=
  (HierarchySourceInput.slots_injective source k).comp
    ((HierarchySelectedSource.old_injective source k).comp
      (HierarchyPrefix.dimension_injective k source.degrees.proofLog source.degrees.queries))

theorem bit_values (p q : ℕ) :
    (DimensionsFromInput.bitsR p q).val=55+2*p ∧ (DimensionsFromInput.bitsQ p q).val=68+2*p+2*q := by
  simp [DimensionsFromInput.bitsR,DimensionsFromInput.bitsQ,DimensionsFromInput.dimensionSlots,
    DimensionProducer.bitsR,DimensionProducer.bitsQ,DimensionProducer.old,DimensionProducer.querySlots,
    DimensionWidth.bitsSlot,DimensionWidth.binarySlots,DimensionWidth.fresh,DimensionWidth.base,DimensionWidth.tapes,
    DimensionPolynomial.bitsSlot,DimensionPolynomial.binarySlots,DimensionPolynomial.tapes]
  omega

theorem bit_distinct (k : ℕ) :
    bitsR source k≠rawR source k ∧ bitsR source k≠rawQ source k ∧
    bitsQ source k≠rawR source k ∧ bitsQ source k≠rawQ source k := by
  have hraw := raw_values source.degrees.proofLog source.degrees.queries
  have hbits := bit_values source.degrees.proofLog source.degrees.queries
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro he
  all_goals have hv := congrArg Fin.val (dimension_injective source k he)
  all_goals simp only [hraw.1,hraw.2,hbits.1,hbits.2] at hv
  all_goals omega

theorem slot_positive (k : ℕ) (i : Fin (HierarchySelectedSource.tapes source k)) :
    0 < (HierarchySourceInput.slots source k i).val := by
  dsimp only [HierarchySourceInput.slots]
  split_ifs <;> simp

theorem zero_ne_slot (k : ℕ) (i : Fin (HierarchySelectedSource.tapes source k)) :
    (⟨0,by dsimp [base,HierarchySourceInput.tapes]; omega⟩ : Fin (base source k))≠
      HierarchySourceInput.slots source k i := by
  intro he
  have hv : 0=(HierarchySourceInput.slots source k i).val := congrArg Fin.val he
  have hp := slot_positive source k i
  omega

structure Fields {s : ℕ} (k CH Cpad : ℕ) (code x bound : List Bool)
    (out : Configuration (tapes source k) s) : Prop where
  input : out.tapes (old source k ⟨0,by dsimp [base,HierarchySourceInput.tapes]; omega⟩)=frame x++frame bound
  inputHead : out.heads (old source k ⟨0,by dsimp [base,HierarchySourceInput.tapes]; omega⟩)=0
  width : out.tapes (old source k (bitsR source k))=frame (R source k CH Cpad code x).bits
  widthHead : out.heads (old source k (bitsR source k))=0
  queries : out.tapes (old source k (bitsQ source k))=frame (Q source k CH Cpad code x).bits
  queriesHead : out.heads (old source k (bitsQ source k))=0
  queryStream : out.tapes (slots source k 29)=QueryBytes.framedCodes
    (normalizedRows (source.output (request k CH Cpad code x)) (R source k CH Cpad code x) (Q source k CH Cpad code x)).flatten
  queryStreamHead : out.heads (slots source k 29)=0
  queryCount : out.tapes (slots source k 25)=CompareMachine.word (R source k CH Cpad code x*Q source k CH Cpad code x)
  queryCountHead : out.heads (slots source k 25)=1
  clauseStream : out.tapes (slots source k 38)=DedupBytes.fields (source.output (request k CH Cpad code x))
  clauseStreamHead : out.heads (slots source k 38)=0
  clauseCount : out.tapes (slots source k 46)=CompareMachine.word (Codec.clauses (source.output (request k CH Cpad code x))).length
  clauseCountHead : out.heads (slots source k 46)=1

theorem scalar_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r,run (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (SourceHandoff.sourceTapes (frame x++frame bound))=some r ∧
      r.steps ≤ budget source k CH Cpad code x ∧ Fields source k CH Cpad code x bound r.final := by
  obtain ⟨r,prior,hr,hrs,hfields,_,hinput,hret,hquery,hqc,hclause,hcc,hqueryh,hqch,hclauseh,hcch⟩ :=
    raw_run source k CH Cpad code x bound hpad
  have hzero := hret ⟨0,by dsimp [base,HierarchySourceInput.tapes]; omega⟩
    (zero_ne_slot source k (HierarchySelectedSource.outputTape source k))
    (zero_ne_slot source k (HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries))))
    (zero_ne_slot source k (HierarchySelectedSource.old source k (HierarchySelectedSource.dimension source k
      (DimensionsFromInput.rawQ source.degrees.proofLog source.degrees.queries))))
  have hrbits := hret (bitsR source k) (Ne.symm (source_distinct source k _))
    (bit_distinct source k).1 (bit_distinct source k).2.1
  have hqbits := hret (bitsQ source k) (Ne.symm (source_distinct source k _))
    (bit_distinct source k).2.2.1 (bit_distinct source k).2.2.2
  exact ⟨r,hr,hrs,⟨hzero.1.trans hinput,hzero.2,hrbits.1.trans hfields.bitsR,hrbits.2,
    hqbits.1.trans hfields.bitsQ,hqbits.2,hquery,hqueryh,hqc,hqch,hclause,hclauseh,hcc,hcch⟩⟩

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
