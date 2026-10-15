import Proof.Amplification.CanonicalBalancedRecoveryQueryCharges
import Proof.Circuits.PaddedRunnerBudgetClosure
import Proof.Circuits.StructuralGateBudgetEnvelope

namespace NearCubicWires.R1Leaf56BalancedAtomCodeLedger

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedRecoveryQueryCharges
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedRunnerBudgetClosure
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.R1Leaf56StructuralGateBudgetEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalInverseCanonicalBodySelectorLocalClosure
open NearCubicWires.ValidatorPolynomialDomination

private abbrev Request := LanguageEvaluationRequest

/-! ## §1 The envelope chain is a source polynomial -/

private theorem natBitLength_le_succ (value : ℕ) : natBitLength value ≤ value + 1 := by
  unfold natBitLength
  exact Nat.succ_le_succ (Nat.log_le_self 2 value)

theorem sourcePoly_atomEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => atomEnvelope (width m) (oracleBound m)) := by
  have hsum : SourcePoly (fun m => width m + oracleBound m + 1) :=
    (hwidth.add hbound).add (polyDominated_const 1)
  have hfactor :
      SourcePoly (fun m => 3 * (width m + oracleBound m + 1) + 1 + 1) :=
    ((hsum.const_mul 3).add (polyDominated_const 1)).add (polyDominated_const 1)
  refine PolyDominated.mono ((hsum.mul hfactor).add (polyDominated_const 20))
    fun m => le_of_eq ?_
  simp only [atomEnvelope, boundedCircuitFieldLimit]

theorem sourcePoly_rowEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => rowEnvelope (width m) (oracleBound m)) := by
  refine PolyDominated.mono
    (((sourcePoly_atomEnvelope hwidth hbound).const_mul 16).add
      (polyDominated_const 64)) fun m => le_of_eq ?_
  simp only [rowEnvelope]

theorem sourcePoly_grammarEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => grammarEnvelope (width m) (oracleBound m)) := by
  have hleft : SourcePoly (fun m => oracleBound m + 1) :=
    hbound.add (polyDominated_const 1)
  have hright :
      SourcePoly (fun m => rowEnvelope (width m) (oracleBound m) + 1) :=
    (sourcePoly_rowEnvelope hwidth hbound).add (polyDominated_const 1)
  refine PolyDominated.mono ((hleft.mul hright).add (polyDominated_const 1))
    fun m => le_of_eq ?_
  simp only [grammarEnvelope]

theorem sourcePoly_nodeEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => nodeEnvelope (width m) (oracleBound m)) := by
  have hatom := sourcePoly_atomEnvelope hwidth hbound
  have hshift :
      SourcePoly (fun m => atomEnvelope (width m) (oracleBound m) + 2) :=
    hatom.add (polyDominated_const 2)
  have hblock :
      SourcePoly (fun m =>
        oracleBound m * (atomEnvelope (width m) (oracleBound m) + 2) + 1) :=
    (hbound.mul hshift).add (polyDominated_const 1)
  refine PolyDominated.mono
    ((((hblock.const_mul 2).add (hatom.const_mul 2)).add
      (polyDominated_const 3)).add
      ((hshift.const_mul 5).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [nodeEnvelope]

theorem sourcePoly_outputEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => outputEnvelope (width m) (oracleBound m)) := by
  have hatom := sourcePoly_atomEnvelope hwidth hbound
  have hshift :
      SourcePoly (fun m => atomEnvelope (width m) (oracleBound m) + 2) :=
    hatom.add (polyDominated_const 2)
  refine PolyDominated.mono
    ((hbound.mul (sourcePoly_nodeEnvelope hwidth hbound)).add
      ((hbound.mul hshift).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [outputEnvelope]

theorem sourcePoly_rowBudgetEnvelope {width oracleBound queryCount clauseCount :
      ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount) :
    SourcePoly (fun m =>
      rowBudgetEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  refine PolyDominated.mono
    (((sourcePoly_outputEnvelope hwidth hbound).mul hquery).add
      ((hclause.const_mul 6).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [rowBudgetEnvelope]

theorem sourcePoly_fixedCountEnvelope {width oracleBound queryCount clauseCount :
      ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount)
    (htwo : SourcePoly (fun m => 2 ^ width m)) :
    SourcePoly (fun m =>
      fixedCountEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  have hrow :
      SourcePoly (fun m =>
        rowBudgetEnvelope (width m) (oracleBound m) (queryCount m)
          (clauseCount m) + 1) :=
    (sourcePoly_rowBudgetEnvelope hwidth hbound hquery hclause).add
      (polyDominated_const 1)
  refine PolyDominated.mono
    (((sourcePoly_grammarEnvelope hwidth hbound).add
      ((hrow.mul htwo).add (polyDominated_const 1))).add
      (polyDominated_const 1)) fun m => le_of_eq ?_
  simp only [fixedCountEnvelope]

theorem sourcePoly_structuralGateEnvelope
    {width oracleBound queryCount clauseCount : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount)
    (htwo : SourcePoly (fun m => 2 ^ width m)) :
    SourcePoly (fun m =>
      structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  refine PolyDominated.mono
    ((((sourcePoly_fixedCountEnvelope hwidth hbound hquery hclause htwo).add
      (polyDominated_const 2)).mul hbound).add (polyDominated_const 1))
    fun m => le_of_eq ?_
  simp only [structuralGateEnvelope]

theorem sourcePoly_descriptionWidth {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => descriptionWidth (width m) (oracleBound m)) := by
  have hleft : SourcePoly (fun m => oracleBound m + 1) :=
    hbound.add (polyDominated_const 1)
  have hfield : SourcePoly (fun m => width m + oracleBound m + 1) :=
    (hwidth.add hbound).add (polyDominated_const 1)
  have hright :
      SourcePoly (fun m => 6 + 2 * (width m + oracleBound m + 1)) :=
    (polyDominated_const 6).add (hfield.const_mul 2)
  refine PolyDominated.mono (hleft.mul hright) fun m => le_of_eq ?_
  simp only [descriptionWidth, boundedCircuitDescriptionWidth,
    boundedCircuitFieldLimit]

/-- **The whole balanced atom-code envelope is a source polynomial.** -/
theorem sourcePoly_atomCodeEnvelope
    {width oracleBound queryCount clauseCount : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount)
    (htwo : SourcePoly (fun m => 2 ^ width m)) :
    SourcePoly (fun m =>
      16 *
          (descriptionWidth (width m) (oracleBound m) +
            structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
              (clauseCount m) + 1 + 1) ^ 2 *
        (32 *
          widthUnit (descriptionWidth (width m) (oracleBound m))
            (descriptionWidth (width m) (oracleBound m) +
              structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
                (clauseCount m)))) := by
  have hdescription := sourcePoly_descriptionWidth hwidth hbound
  have hgate :=
    sourcePoly_structuralGateEnvelope hwidth hbound hquery hclause htwo
  have hsum :
      SourcePoly (fun m =>
        descriptionWidth (width m) (oracleBound m) +
          structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
            (clauseCount m)) := hdescription.add hgate
  have hshift :
      SourcePoly (fun m =>
        descriptionWidth (width m) (oracleBound m) +
          structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
            (clauseCount m) + 1 + 1) :=
    (hsum.add (polyDominated_const 1)).add (polyDominated_const 1)
  have hsquare :
      SourcePoly (fun m =>
        16 *
          ((descriptionWidth (width m) (oracleBound m) +
            structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
              (clauseCount m) + 1 + 1) *
            (descriptionWidth (width m) (oracleBound m) +
              structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
                (clauseCount m) + 1 + 1))) :=
    (hshift.mul hshift).const_mul 16
  have hunit :
      SourcePoly (fun m =>
        32 *
          (descriptionWidth (width m) (oracleBound m) +
            (descriptionWidth (width m) (oracleBound m) +
              structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
                (clauseCount m)) + 4 + 1)) :=
    (((hdescription.add hsum).add (polyDominated_const 4)).add
      (polyDominated_const 1)).const_mul 32
  refine PolyDominated.mono (hsquare.mul hunit) fun m => ?_
  refine Nat.mul_le_mul ?_ ?_
  · exact le_of_eq (by ring)
  · exact Nat.mul_le_mul_left 32 (natBitLength_le_succ _)

/-! ## §2 The canonical coordinates -/

/-- The padded decision's clause count is the executable decision runner's own
budget: padding only truncates the randomness word. -/
theorem paddedOuterPCP_decision_clauses_length_le {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) {n : ℕ} (input : BitInput n)
    (randomness : BitInput ((paddedOuterPCP outer).nativeWidth n)) :
    ((paddedOuterPCP outer).decision input randomness).clauses.length ≤
      decisionBudget outer.pcp n :=
  outer.decisionLengthBound n input
    (prefixBits (nativeWidth_le_widthEnvelope outer n) randomness)

/-- `2 ^ widthEnvelope` is a source polynomial — the log route. -/
theorem sourcePoly_two_pow_widthEnvelope {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun m => 2 ^ widthEnvelope outer m) :=
  PolyDominated.mono (sourcePoly_widthBudget outer)
    (two_pow_widthEnvelope_le_budget outer)

/-- The selected oracle size bound, as a function of the source length alone.
`inverseScheduleBound` at one target IS this at that target's schedule
length — the identification below is `rfl`. -/
noncomputable def selectedOracleBound (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) (sourceLen : ℕ) : ℕ :=
  oracleSizeBound
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth) sourceLen)

theorem inverseScheduleBound_eq_selectedOracleBound
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    inverseScheduleBound contracts clockDepth advantageExponent target =
      selectedOracleBound contracts clockDepth advantageExponent
        (inverseScheduleLength contracts clockDepth advantageExponent
          target) := rfl

theorem sourcePoly_selectedOracleBound (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) :
    SourcePoly (selectedOracleBound contracts clockDepth advantageExponent) := by
  refine PolyDominated.mono
    (sourcePoly_pow
      ((sourcePoly_widthEnvelope
        (publishedHierarchyOuterPCP contracts clockDepth)).add
        (polyDominated_const 1))
      (2 ^ oracleDepth
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))) fun m => ?_
  have hclock :=
    pairIter_add_one_le_pow
      (oracleDepth
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent)))
      (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth) m)
  change
    pairIter
        (oracleDepth
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth) m) ≤ _
  omega

/-- The selected balanced atom code's width envelope, at the source length. -/
noncomputable def selectedAtomCodeEnvelope (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) (sourceLen : ℕ) : ℕ :=
  16 *
      (descriptionWidth
          (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
            sourceLen)
          (selectedOracleBound contracts clockDepth advantageExponent
            sourceLen) +
        structuralGateEnvelope
          (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
            sourceLen)
          (selectedOracleBound contracts clockDepth advantageExponent sourceLen)
          ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
            sourceLen)
          (decisionBudget (publishedHierarchyOuterPCP contracts clockDepth).pcp
            sourceLen) + 1 + 1) ^ 2 *
    (32 *
      widthUnit
        (descriptionWidth
          (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
            sourceLen)
          (selectedOracleBound contracts clockDepth advantageExponent
            sourceLen))
        (descriptionWidth
            (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
              sourceLen)
            (selectedOracleBound contracts clockDepth advantageExponent
              sourceLen) +
          structuralGateEnvelope
            (widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth)
              sourceLen)
            (selectedOracleBound contracts clockDepth advantageExponent
              sourceLen)
            ((publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
              sourceLen)
            (decisionBudget
              (publishedHierarchyOuterPCP contracts clockDepth).pcp sourceLen)))

theorem sourcePoly_selectedAtomCodeEnvelope (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) :
    SourcePoly
      (selectedAtomCodeEnvelope contracts clockDepth advantageExponent) :=
  sourcePoly_atomCodeEnvelope
    (sourcePoly_widthEnvelope (publishedHierarchyOuterPCP contracts clockDepth))
    (sourcePoly_selectedOracleBound contracts clockDepth advantageExponent)
    (sourcePoly_queryCount (publishedHierarchyOuterPCP contracts clockDepth))
    (sourcePoly_decisionBudget (publishedHierarchyOuterPCP contracts clockDepth))
    (sourcePoly_two_pow_widthEnvelope
      (publishedHierarchyOuterPCP contracts clockDepth))

theorem natBitLength_canonicalBodyAtomCodeBalanced_le_envelope
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) :
    natBitLength
        (canonicalBodyAtomCodeBalanced contracts clockDepth machine
          advantageExponent request) ≤
      selectedAtomCodeEnvelope contracts clockDepth advantageExponent
        (canonicalPointSourceLength contracts clockDepth advantageExponent
          request) :=
  natBitLength_encodeBalancedList_structuralFormulaAtoms_le
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent
      request.length)
    (decisionBudget (publishedHierarchyOuterPCP contracts clockDepth).pcp
      (canonicalPointSourceLength contracts clockDepth advantageExponent
        request))
    (fun randomness =>
      paddedOuterPCP_decision_clauses_length_le
        (publishedHierarchyOuterPCP contracts clockDepth) _ randomness)

theorem polyDominated_natBitLength_canonicalBodyAtomCodeBalanced
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) :
    PolyDominated
      (fun request : Request =>
        natBitLength
          (canonicalBodyAtomCodeBalanced contracts clockDepth machine
            advantageExponent request))
      (canonicalPointSourceLength contracts clockDepth advantageExponent) := by
  refine PolyDominated.mono
    (sourcePoly_at_length
      (sourcePoly_selectedAtomCodeEnvelope contracts clockDepth
        advantageExponent)
      (fun _ : Request => le_rfl)) fun request => ?_
  exact natBitLength_canonicalBodyAtomCodeBalanced_le_envelope contracts
    clockDepth machine advantageExponent request

end NearCubicWires.R1Leaf56BalancedAtomCodeLedger
