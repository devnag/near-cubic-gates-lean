import Proof.Circuits.PaddedRunnerBudgetDomination

namespace NearCubicWires.PaddedRunnerBudgetClosure

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionDecisionRunner
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionPresentedPCP
open NearCubicWires.PaddedProjectionQueryRunner
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedProjectionShapeRunner
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker
open NearCubicWires.ValidatorPolynomialDomination

/-! ## 1. The degree-free judgement -/

/-- **The walk's judgement, with the degree closed.**  A charge is polynomially
dominated when *some* degree and *some* coefficient make it fit the polynomial
budget at its own measure.  Both witnesses stay existential: the coefficients
mention composed register spans, and the degrees mention the published runner
exponents, and neither should reach a statement the kernel might evaluate. -/
def PolyDominated {Request : Type} (charge measureOf : Request → ℕ) : Prop :=
  ∃ degree, Dominated charge measureOf degree

theorem PolyDominated.mono {Request : Type}
    {charge charge' measureOf : Request → ℕ}
    (h : PolyDominated charge measureOf)
    (hle : ∀ request, charge' request ≤ charge request) :
    PolyDominated charge' measureOf := by
  obtain ⟨degree, hdegree⟩ := h
  exact ⟨degree, hdegree.mono hle⟩

theorem polyDominated_const {Request : Type} {measureOf : Request → ℕ}
    (value : ℕ) : PolyDominated (fun _ : Request => value) measureOf :=
  ⟨0, dominated_const value 0⟩

/-- Two judgements brought to a common degree. -/
theorem PolyDominated.align {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    ∃ degree, Dominated left measureOf degree ∧
      Dominated right measureOf degree := by
  obtain ⟨leftDegree, hleftBound⟩ := hleft
  obtain ⟨rightDegree, hrightBound⟩ := hright
  exact
    ⟨max leftDegree rightDegree,
      hleftBound.degree_mono (Nat.le_max_left _ _),
      hrightBound.degree_mono (Nat.le_max_right _ _)⟩

theorem PolyDominated.add {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated (fun request => left request + right request) measureOf := by
  obtain ⟨degree, hleftBound, hrightBound⟩ := hleft.align hright
  exact ⟨degree, hleftBound.add hrightBound⟩

theorem PolyDominated.max {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated
      (fun request => Max.max (left request) (right request)) measureOf := by
  obtain ⟨degree, hleftBound, hrightBound⟩ := hleft.align hright
  exact ⟨degree, hleftBound.max hrightBound⟩

theorem PolyDominated.mul {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated (fun request => left request * right request) measureOf := by
  obtain ⟨leftDegree, hleftBound⟩ := hleft
  obtain ⟨rightDegree, hrightBound⟩ := hright
  exact ⟨leftDegree + rightDegree, hleftBound.mul hrightBound⟩

theorem PolyDominated.const_mul {Request : Type}
    {charge measureOf : Request → ℕ} (factor : ℕ)
    (h : PolyDominated charge measureOf) :
    PolyDominated (fun request => factor * charge request) measureOf := by
  obtain ⟨degree, hdegree⟩ := h
  exact ⟨degree, hdegree.const_mul factor⟩

theorem PolyDominated.natBitLength {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => natBitLength (value request)) measureOf := by
  obtain ⟨degree, hdegree⟩ := h
  exact ⟨degree + 1, hdegree.natBitLength⟩

theorem PolyDominated.natBitLength_pair {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated
      (fun request => NearCubicWires.natBitLength (left request)) measureOf)
    (hright : PolyDominated
      (fun request => NearCubicWires.natBitLength (right request)) measureOf) :
    PolyDominated
      (fun request =>
        NearCubicWires.natBitLength (Nat.pair (left request) (right request)))
      measureOf := by
  obtain ⟨degree, hleftBound, hrightBound⟩ := hleft.align hright
  exact ⟨degree, hleftBound.natBitLength_pair hrightBound⟩

theorem PolyDominated.natBitLength_max {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated
      (fun request => NearCubicWires.natBitLength (left request)) measureOf)
    (hright : PolyDominated
      (fun request => NearCubicWires.natBitLength (right request)) measureOf) :
    PolyDominated
      (fun request =>
        NearCubicWires.natBitLength (Max.max (left request) (right request)))
      measureOf := by
  obtain ⟨degree, hleftBound, hrightBound⟩ := hleft.align hright
  exact ⟨degree, hleftBound.natBitLength_max hrightBound⟩

/-! ## 2. The published source numerals are polynomials in the public length

Everything in the outer PCP's published surface — its clock, its runner budgets,
its native width and query count — is a polynomial in the public length by
itself.  The whole ledger rests on one inequality about the pairing clock. -/

/-- The ledger judgement: a charge on the public length, dominated by a
polynomial in that length. -/
abbrev SourcePoly (charge : ℕ → ℕ) : Prop :=
  PolyDominated charge (fun n => n)

/-- Enter the ledger from an explicit polynomial bound. -/
theorem sourcePoly_of_le {charge : ℕ → ℕ} (coefficient degree : ℕ)
    (hbound : ∀ n, charge n ≤ coefficient * (n + 1) ^ degree) :
    SourcePoly charge :=
  ⟨degree, ⟨coefficient, fun n => hbound n⟩⟩

theorem sourcePoly_id : SourcePoly (fun n => n) :=
  sourcePoly_of_le 1 1 fun n => by
    rw [Nat.one_mul, Nat.pow_one]
    omega

/-- **The clock is a polynomial.**  This is the ledger's only genuine
arithmetic input. -/
theorem sourcePoly_pairClock (clockDepth : ℕ) :
    SourcePoly (fun n => pairClock clockDepth n) :=
  sourcePoly_of_le 1 (2 ^ clockDepth) fun n => by
    have hclock := pairIter_add_one_le_pow clockDepth n
    rw [Nat.one_mul]
    change pairIter clockDepth n ≤ (n + 1) ^ 2 ^ clockDepth
    omega

theorem sourcePoly_pow {charge : ℕ → ℕ} (h : SourcePoly charge)
    (exponent : ℕ) : SourcePoly (fun n => charge n ^ exponent) := by
  obtain ⟨degree, coefficient, hbound⟩ := h
  refine sourcePoly_of_le (coefficient ^ exponent) (degree * exponent)
    fun n => ?_
  have hvalue : charge n ≤ coefficient * (n + 1) ^ degree := hbound n
  calc
    charge n ^ exponent ≤ (coefficient * (n + 1) ^ degree) ^ exponent :=
      Nat.pow_le_pow_left hvalue exponent
    _ = coefficient ^ exponent * (n + 1) ^ (degree * exponent) := by
      rw [Nat.mul_pow, ← Nat.pow_mul]

/-- The logarithmic scale of a polynomial charge is a polynomial charge. -/
theorem sourcePoly_logScale {charge : ℕ → ℕ} (h : SourcePoly charge) :
    SourcePoly (fun n => logScale (charge n)) :=
  PolyDominated.mono (PolyDominated.add h (polyDominated_const 2))
    fun n => logScale_le_add_two (charge n)

/-- The polynomial budget of a polynomial measure is a polynomial charge. -/
theorem sourcePoly_polynomialBudget {measureCharge : ℕ → ℕ}
    (h : SourcePoly measureCharge) (coefficient exponent : ℕ) :
    SourcePoly
      (fun n => polynomialBudget coefficient exponent (measureCharge n)) :=
  PolyDominated.const_mul coefficient
    (sourcePoly_pow (PolyDominated.add h (polyDominated_const 1)) exponent)

theorem sourcePoly_shapeMeasure (clockDepth : ℕ) :
    SourcePoly (fun n => shapeMeasure clockDepth n) :=
  PolyDominated.mono
    (PolyDominated.add sourcePoly_id
      (sourcePoly_logScale (sourcePoly_pairClock clockDepth)))
    fun _ => Nat.le_refl _

theorem sourcePoly_shapeBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => outer.pcp.shape.budget n) :=
  PolyDominated.mono
    (sourcePoly_polynomialBudget (sourcePoly_shapeMeasure clockDepth)
      outer.pcp.shape.coefficient outer.pcp.shape.degree)
    fun _ => Nat.le_refl _

theorem sourcePoly_widthBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => widthBudget outer n) := by
  have hclock := sourcePoly_pairClock clockDepth
  have hlogarithm :=
    sourcePoly_pow (sourcePoly_logScale hclock) outer.proofExponent
  refine PolyDominated.mono
    (PolyDominated.const_mul outer.pcp.shape.coefficient
      (PolyDominated.mul hclock hlogarithm)) fun n => ?_
  exact le_of_eq (by simp only [widthBudget]; ring)

theorem sourcePoly_widthEnvelope {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => widthEnvelope outer n) :=
  PolyDominated.mono (sourcePoly_widthBudget outer) fun n =>
    Nat.log_le_self 2 (widthBudget outer n)

theorem sourcePoly_nativeWidth {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => outer.pcp.nativeWidth n) :=
  PolyDominated.mono (sourcePoly_widthEnvelope outer)
    (nativeWidth_le_widthEnvelope outer)

theorem sourcePoly_queryCount {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => outer.pcp.queryCount n) :=
  PolyDominated.mono (sourcePoly_shapeBudget outer) outer.queryCountBound

theorem sourcePoly_nativeMeasure {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => nativeMeasure outer.pcp n) :=
  PolyDominated.mono
    (PolyDominated.add
      (PolyDominated.add sourcePoly_id (sourcePoly_nativeWidth outer))
      (sourcePoly_queryCount outer))
    fun _ => Nat.le_refl _

theorem sourcePoly_queryBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => queryBudget outer.pcp n) :=
  PolyDominated.mono
    (sourcePoly_polynomialBudget (sourcePoly_nativeMeasure outer)
      outer.pcp.query.coefficient outer.pcp.query.degree)
    fun _ => Nat.le_refl _

theorem sourcePoly_decisionBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => decisionBudget outer.pcp n) :=
  PolyDominated.mono
    (sourcePoly_polynomialBudget (sourcePoly_nativeMeasure outer)
      outer.pcp.decisionRunner.coefficient outer.pcp.decisionRunner.degree)
    fun _ => Nat.le_refl _

/-- The published shape code's own magnitude is paid for by the shape runner's
declared budget, so it too is a ledger entry. -/
theorem sourcePoly_natBitLength_shapeExecute {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    SourcePoly (fun n => natBitLength (outer.pcp.shape.execute n)) :=
  PolyDominated.mono (sourcePoly_shapeBudget outer)
    (natBitLength_shapeExecute_le_budget outer)

/-! ## 3. Transferring the ledger to the two request measures -/

/-- A ledger entry charged at a request's public length is dominated at any
request measure that dominates that length. -/
theorem sourcePoly_at_length {Request : Type} {charge : ℕ → ℕ}
    {length measureOf : Request → ℕ} (h : SourcePoly charge)
    (hle : ∀ request, length request ≤ measureOf request) :
    PolyDominated (fun request => charge (length request)) measureOf := by
  obtain ⟨degree, coefficient, hbound⟩ := h
  refine ⟨degree, coefficient, fun request => ?_⟩
  have hvalue :
      charge (length request) ≤ coefficient * (length request + 1) ^ degree :=
    hbound (length request)
  have harity := hle request
  refine hvalue.trans (Nat.mul_le_mul_left coefficient ?_)
  exact Nat.pow_le_pow_left (by omega) degree

theorem queryArity_le_measure (request : ProjectionQueryRequest) :
    request.inputArity ≤ ProjectionQueryRequest.measure request := by
  simp only [ProjectionQueryRequest.measure]
  omega

theorem decisionArity_le_measure (request : ProjectionDecisionRequest) :
    request.inputArity ≤ ProjectionDecisionRequest.measure request := by
  simp only [ProjectionDecisionRequest.measure]
  omega

/-- Every ledger entry, read at a query request. -/
theorem sourcePoly_atQuery {charge : ℕ → ℕ} (h : SourcePoly charge) :
    PolyDominated (fun request : ProjectionQueryRequest =>
      charge request.inputArity) ProjectionQueryRequest.measure :=
  sourcePoly_at_length h queryArity_le_measure

/-- Every ledger entry, read at a decision request. -/
theorem sourcePoly_atDecision {charge : ℕ → ℕ} (h : SourcePoly charge) :
    PolyDominated (fun request : ProjectionDecisionRequest =>
      charge request.inputArity) ProjectionDecisionRequest.measure :=
  sourcePoly_at_length h decisionArity_le_measure

private theorem natBitLength_succ_le (value : ℕ) :
    natBitLength (value + 1) ≤ natBitLength value + 1 := by
  have hlt : value < 2 ^ (Nat.log 2 value + 1) :=
    Nat.lt_pow_succ_log_self (by omega) value
  have hlog : Nat.log 2 (value + 1) ≤ Nat.log 2 (2 ^ (Nat.log 2 value + 1)) :=
    Nat.log_mono_right (by omega)
  rw [Nat.log_pow (by omega)] at hlog
  simp only [natBitLength]
  omega

/-- **The prefix value fits the selected width.**  `bitInputPrefix` is the
residue modulo `2 ^ width`, so nothing about the padded random string survives
into its binary width. -/
theorem natBitLength_bitInputPrefix_le (width value : ℕ) :
    natBitLength (bitInputPrefix width value) ≤ width + 1 := by
  have hpositive : 0 < 2 ^ width := Nat.two_pow_pos width
  have hlt : bitInputPrefix width value < 2 ^ width := Nat.mod_lt value hpositive
  have hlog :
      Nat.log 2 (bitInputPrefix width value) ≤ Nat.log 2 (2 ^ width) :=
    Nat.log_mono_right (Nat.le_of_lt hlt)
  rw [Nat.log_pow (by omega)] at hlog
  simp only [natBitLength]
  omega

/-- The prefix reducer's register ledger, as a width of two named numerals. -/
theorem bitInputPrefixBits_le (width value : ℕ) :
    bitInputPrefixBits width value ≤
      natBitLength (Max.max (Nat.pair width value) (2 ^ width)) + 1 := by
  simp only [bitInputPrefixBits, registerBound, bitInputPrefixInput]
  exact natBitLength_succ_le _

/-- The padded random string's own width, at a decision request. -/
theorem polyDominated_decisionRandomnessBits :
    PolyDominated
      (fun request : ProjectionDecisionRequest =>
        natBitLength (encodeBitInput request.randomness))
      ProjectionDecisionRequest.measure :=
  ⟨1, 1, fun request => by
    have hwidth :
        request.width ≤ ProjectionDecisionRequest.measure request := by
      simp only [ProjectionDecisionRequest.measure]
      omega
    have hcode := natBitLength_encodeBitInput_le request.randomness
    change natBitLength (encodeBitInput request.randomness) ≤
      1 * (ProjectionDecisionRequest.measure request + 1) ^ 1
    rw [Nat.one_mul, Nat.pow_one]
    omega⟩

/-- The published proof-size bound turns the prefix reducer's exponential
register into a ledger entry. -/
theorem polyDominated_decisionWidthPowerBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated
      (fun request : ProjectionDecisionRequest =>
        natBitLength (2 ^ outer.pcp.nativeWidth request.inputArity))
      ProjectionDecisionRequest.measure :=
  PolyDominated.mono
    (PolyDominated.natBitLength
      (sourcePoly_atDecision (sourcePoly_widthBudget outer)))
    fun request => natBitLength_mono (outer.proofSizeBound request.inputArity)

/-- **The prefix reducer's register ledger, dominated.** -/
theorem polyDominated_decisionPrefixBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated
      (fun request : ProjectionDecisionRequest =>
        bitInputPrefixBits
          (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1
          (encodeBitInput request.randomness))
      ProjectionDecisionRequest.measure := by
  have hwidth :
      PolyDominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (outer.pcp.nativeWidth request.inputArity))
        ProjectionDecisionRequest.measure :=
    PolyDominated.natBitLength
      (sourcePoly_atDecision (sourcePoly_nativeWidth outer))
  have hpair :=
    PolyDominated.natBitLength_pair hwidth polyDominated_decisionRandomnessBits
  have hmax :=
    PolyDominated.natBitLength_max hpair
      (polyDominated_decisionWidthPowerBits outer)
  refine PolyDominated.mono (PolyDominated.add hmax (polyDominated_const 1))
    fun _ => ?_
  exact bitInputPrefixBits_le _ _

/-- **The prefix reducer's emitted width, dominated.** -/
theorem polyDominated_decisionPrefixValue {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated
      (fun request : ProjectionDecisionRequest =>
        natBitLength
          (bitInputPrefix
            (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1
            (encodeBitInput request.randomness)))
      ProjectionDecisionRequest.measure :=
  PolyDominated.mono
    (PolyDominated.add
      (sourcePoly_atDecision (sourcePoly_nativeWidth outer))
      (polyDominated_const 1))
    fun _ => natBitLength_bitInputPrefix_le _ _

/-- **The prefix reducer's clock, dominated.**  `dominated_prefixFuel` converts
the exponential charge through `proofSizeBound`; both of its premises are ledger
entries. -/
theorem polyDominated_decisionPrefixFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated
      (fun request : ProjectionDecisionRequest =>
        bitInputPrefixFuel (outer.pcp.nativeWidth request.inputArity)
          (encodeBitInput request.randomness))
      ProjectionDecisionRequest.measure := by
  obtain ⟨degree, henvelope, hbudget⟩ :=
    PolyDominated.align (sourcePoly_atDecision (sourcePoly_widthEnvelope outer))
      (sourcePoly_atDecision (sourcePoly_widthBudget outer))
  exact ⟨degree + degree, dominated_prefixFuel outer degree henvelope hbudget⟩

/-- **Row 7, closed.** -/
theorem polyDominated_publishedPaddedDecisionBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated (fun request => publishedPaddedDecisionBits outer request)
      ProjectionDecisionRequest.measure := by
  obtain ⟨shapeDegree, hshape⟩ :=
    sourcePoly_atDecision (sourcePoly_shapeBudget outer)
  obtain ⟨decisionDegree, hdecision⟩ :=
    sourcePoly_atDecision (sourcePoly_decisionBudget outer)
  obtain ⟨prefixBitsDegree, hprefixBits⟩ := polyDominated_decisionPrefixBits outer
  obtain ⟨prefixValueDegree, hprefixValue⟩ :=
    polyDominated_decisionPrefixValue outer
  refine
    ⟨max 1 (max (max shapeDegree decisionDegree)
      (max prefixBitsDegree prefixValueDegree)), ?_⟩
  exact dominated_publishedPaddedDecisionBits outer _ (by omega)
    (hshape.degree_mono (by omega)) (hdecision.degree_mono (by omega))
    (hprefixBits.degree_mono (by omega)) (hprefixValue.degree_mono (by omega))

/-- **Row 8, closed.** -/
theorem polyDominated_publishedPaddedDecisionFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated (fun request => publishedPaddedDecisionFuel outer request)
      ProjectionDecisionRequest.measure := by
  obtain ⟨shapeDegree, hshape⟩ :=
    sourcePoly_atDecision (sourcePoly_shapeBudget outer)
  obtain ⟨decisionDegree, hdecision⟩ :=
    sourcePoly_atDecision (sourcePoly_decisionBudget outer)
  obtain ⟨prefixDegree, hprefix⟩ := polyDominated_decisionPrefixFuel outer
  refine ⟨max shapeDegree (max decisionDegree prefixDegree), ?_⟩
  exact dominated_publishedPaddedDecisionFuel outer _
    (hshape.degree_mono (by omega)) (hdecision.degree_mono (by omega))
    (hprefix.degree_mono (by omega))

/-- A ledger entry read at the shape runner's own measure. -/
theorem sourcePoly_atShape {charge : ℕ → ℕ} (h : SourcePoly charge)
    (clockDepth : ℕ) : PolyDominated charge (shapeMeasure clockDepth) :=
  sourcePoly_at_length (length := fun n => n) h fun n => by
    simp only [shapeMeasure]
    omega

theorem widthValue_eq_widthEnvelope {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) :
    widthValue clockDepth outer.pcp.shape.coefficient outer.proofExponent n =
      widthEnvelope outer n := rfl

/-- The scheduled width numeral's own binary width, dominated. -/
theorem polyDominated_widthValueBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated
      (fun n =>
        natBitLength
          (widthValue clockDepth outer.pcp.shape.coefficient
            outer.proofExponent n))
      (shapeMeasure clockDepth) :=
  PolyDominated.mono
    (PolyDominated.natBitLength
      (sourcePoly_atShape (sourcePoly_widthEnvelope outer) clockDepth))
    fun n => le_of_eq (congrArg natBitLength
      (widthValue_eq_widthEnvelope outer n))

def WidthEnvelopeCharged {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : Prop :=
  PolyDominated
      (fun n =>
        widthEnvelopeBits n clockDepth outer.pcp.shape.coefficient
          outer.proofExponent n)
      (shapeMeasure clockDepth) ∧
    PolyDominated
      (fun n =>
        widthEnvelopeFuel clockDepth outer.pcp.shape.coefficient
          outer.proofExponent n)
      (shapeMeasure clockDepth)

/-- **Row 1, reduced to the bank.** -/
theorem polyDominated_publishedPaddedShapeBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (hbank : WidthEnvelopeCharged outer) :
    PolyDominated (fun n => publishedPaddedShapeBits outer n)
      (shapeMeasure clockDepth) := by
  obtain ⟨bankDegree, hbankBits⟩ := hbank.1
  obtain ⟨valueDegree, hvalue⟩ := polyDominated_widthValueBits outer
  refine
    ⟨max 1 (max (max outer.pcp.shape.degree bankDegree) valueDegree), ?_⟩
  exact dominated_publishedPaddedShapeBits outer _ (by omega)
    ((dominated_shapeBudget outer).degree_mono (by omega))
    (hbankBits.degree_mono (by omega)) (hvalue.degree_mono (by omega))

/-- **Row 2, reduced to the bank.** -/
theorem polyDominated_publishedPaddedShapeFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (hbank : WidthEnvelopeCharged outer) :
    PolyDominated (fun n => publishedPaddedShapeFuel outer n)
      (shapeMeasure clockDepth) := by
  obtain ⟨bankDegree, hbankFuel⟩ := hbank.2
  refine ⟨max outer.pcp.shape.degree bankDegree, ?_⟩
  exact dominated_publishedPaddedShapeFuel outer _
    ((dominated_shapeBudget outer).degree_mono (by omega))
    (hbankFuel.degree_mono (by omega))

/-! ## 7. The two width combinators, with the degree closed -/

theorem PolyDominated.occurrenceStageBits {Request : Type}
    {inputLength headBits tailBits measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => NearCubicWires.natBitLength (inputLength request))
      measureOf)
    (hhead : PolyDominated headBits measureOf)
    (htail : PolyDominated tailBits measureOf) :
    PolyDominated
      (fun request =>
        CaseTwoOccurrenceProgram.occurrenceStageBits (inputLength request)
          (headBits request) (tailBits request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.max hlength (PolyDominated.max hhead htail))
    fun _ =>
      le_of_eq (by simp only [CaseTwoOccurrenceProgram.occurrenceStageBits])

theorem PolyDominated.preserveRightBits {Request : Type}
    {sourceBits left right output measureOf : Request → ℕ}
    (hsource : PolyDominated sourceBits measureOf)
    (hentry : PolyDominated
      (fun request =>
        NearCubicWires.natBitLength (Nat.pair (left request) (right request)))
      measureOf)
    (hexit : PolyDominated
      (fun request =>
        NearCubicWires.natBitLength (Nat.pair (output request) (right request)))
      measureOf) :
    PolyDominated
      (fun request =>
        PreserveRightProgram.preserveRightBits (sourceBits request)
          (left request) (right request) (output request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.max hsource (PolyDominated.max hentry hexit))
    fun _ => le_of_eq (by simp only [PreserveRightProgram.preserveRightBits])

/-! ## 8. The in-range chain's register ledger

`inRangeProgram` is seven linked stages, and every one of them is a maximum of
binary widths of codes assembled from five numerals: the public length, the
native width, the retained request tail, the source query runner's declared
width and the source answer.  Nothing here charges an answer *magnitude*: that
is the whole difference between row 4 and row 5. -/

private theorem natBitLength_double_le (value : ℕ) :
    natBitLength (2 * value) ≤ natBitLength value + 1 := by
  rcases Nat.eq_zero_or_pos value with hzero | hpositive
  · subst hzero
    simp [natBitLength]
  · have hlt : value < 2 ^ (Nat.log 2 value + 1) :=
      Nat.lt_pow_succ_log_self (by omega) value
    have hdouble : 2 * value < 2 ^ (Nat.log 2 value + 2) := by
      have hpower : 2 ^ (Nat.log 2 value + 2) =
          2 * 2 ^ (Nat.log 2 value + 1) := by
        rw [Nat.pow_succ]
        omega
      omega
    have hlog : Nat.log 2 (2 * value) < Nat.log 2 value + 2 :=
      Nat.log_lt_of_lt_pow (by omega) hdouble
    simp only [natBitLength]
    omega

/-- **The bit-serial remainder's register ledger, as a width.**  This is what
replaces the native remainder's magnitude charge: the bit-serial stage's own
register bound is twice its paired request, so its width is the request's width
plus a constant. -/
private theorem bitSerialModBits_le_pair (numerator denominator : ℕ) :
    CanonicalBitSerialModProgram.bitSerialModBits numerator denominator ≤
      natBitLength (Nat.pair numerator denominator) + 2 := by
  have hinput :
      CanonicalBitSerialModProgram.bitSerialModInput numerator denominator =
        Nat.pair numerator denominator := rfl
  have hbound :=
    CanonicalBitSerialModProgram.bitSerialModBits_le numerator denominator
  rw [hinput] at hbound
  have hdouble := natBitLength_double_le (Nat.pair numerator denominator + 1)
  have hsucc := natBitLength_succ_le (Nat.pair numerator denominator)
  omega

private theorem polyDominated_inRangeBits {Request : Type}
    {inputLength width tail outerQueryBits queryOutput measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hwidth : PolyDominated
      (fun request => natBitLength (width request)) measureOf)
    (htail : PolyDominated
      (fun request => natBitLength (tail request)) measureOf)
    (hsource : PolyDominated outerQueryBits measureOf)
    (houtput : PolyDominated
      (fun request => natBitLength (queryOutput request)) measureOf) :
    PolyDominated
      (fun request =>
        PaddedProjectionQueryRunner.inRangeBits (inputLength request)
          (width request) (tail request) (outerQueryBits request)
          (queryOutput request))
      measureOf := by
  have htwo : PolyDominated (fun _ : Request => natBitLength 2) measureOf :=
    polyDominated_const (natBitLength 2)
  have hthree : PolyDominated (fun _ : Request => natBitLength 3) measureOf :=
    polyDominated_const (natBitLength 3)
  have hleft :
      PolyDominated
        (fun request => natBitLength (Nat.unpair (queryOutput request)).1)
        measureOf :=
    PolyDominated.mono houtput fun request =>
      natBitLength_mono (Nat.unpair_left_le (queryOutput request))
  have hright :
      PolyDominated
        (fun request => natBitLength (Nat.unpair (queryOutput request)).2)
        measureOf :=
    PolyDominated.mono houtput fun request =>
      natBitLength_mono (Nat.unpair_right_le (queryOutput request))
  have htag :
      PolyDominated
        (fun request =>
          natBitLength ((Nat.unpair (queryOutput request)).1 % 3)) measureOf :=
    PolyDominated.mono htwo fun _ => natBitLength_mono (by omega)
  have hgap :
      PolyDominated
        (fun request =>
          natBitLength (2 - (Nat.unpair (queryOutput request)).1 % 3))
        measureOf :=
    PolyDominated.mono htwo fun _ => natBitLength_mono (by omega)
  have hmodulus :
      PolyDominated
        (fun request =>
          natBitLength
            (PaddedProjectionQueryRunner.selectedModulus
              ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf := by
    refine PolyDominated.mono
      (PolyDominated.natBitLength_max (left := fun _ => 2) (right := width)
        htwo hwidth) fun _ => natBitLength_mono ?_
    simp only [PaddedProjectionQueryRunner.selectedModulus]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  have hresidue :
      PolyDominated
        (fun request =>
          natBitLength
            ((Nat.unpair (queryOutput request)).2 %
              PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf :=
    PolyDominated.mono hright fun _ => natBitLength_mono (Nat.mod_le _ _)
  have hpayload :=
    PolyDominated.natBitLength_pair hright hwidth
  have hentryCode := PolyDominated.natBitLength_pair hlength htail
  have hmodEntry := PolyDominated.natBitLength_pair hleft hthree
  have hcallFrame :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.callFrameBits (inputLength request)
            (width request) (tail request)) measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max
        (PolyDominated.natBitLength_pair hwidth htail)
        (PolyDominated.natBitLength_pair hentryCode hwidth))
      fun _ => le_of_eq rfl
  have hstageOne :
      PolyDominated
        (fun request =>
          PreserveRightProgram.preserveRightBits (outerQueryBits request)
            (Nat.pair (inputLength request) (tail request)) (width request)
            (queryOutput request)) measureOf :=
    PolyDominated.preserveRightBits hsource
      (PolyDominated.natBitLength_pair hentryCode hwidth)
      (PolyDominated.natBitLength_pair houtput hwidth)
  have htagFrame :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.tagFrameBits (queryOutput request)
            (width request)) measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max
        (PolyDominated.natBitLength_pair houtput hwidth)
        (PolyDominated.natBitLength_pair hmodEntry hpayload))
      fun _ => le_of_eq rfl
  have hmodBits :
      PolyDominated
        (fun request =>
          CanonicalBitSerialModProgram.bitSerialModBits
            (Nat.unpair (queryOutput request)).1 3) measureOf :=
    PolyDominated.mono (PolyDominated.add hmodEntry (polyDominated_const 2))
      fun _ => bitSerialModBits_le_pair _ _
  have hstageTwo :
      PolyDominated
        (fun request =>
          PreserveRightProgram.preserveRightBits
            (CanonicalBitSerialModProgram.bitSerialModBits
              (Nat.unpair (queryOutput request)).1 3)
            (CanonicalNativeModProgram.nativeModInput
              (Nat.unpair (queryOutput request)).1 3)
            (Nat.pair (Nat.unpair (queryOutput request)).2 (width request))
            ((Nat.unpair (queryOutput request)).1 % 3)) measureOf :=
    PolyDominated.preserveRightBits hmodBits
      (PolyDominated.natBitLength_pair hmodEntry hpayload)
      (PolyDominated.natBitLength_pair htag hpayload)
  have hmodulusTag :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.modulusTagBits
            ((Nat.unpair (queryOutput request)).1 % 3)
            (Nat.pair (Nat.unpair (queryOutput request)).2 (width request)))
        measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max (left := fun _ => 2) htwo
        (PolyDominated.natBitLength_max
          (PolyDominated.natBitLength_pair htag hpayload)
          (PolyDominated.natBitLength_pair hgap
            (PolyDominated.natBitLength_pair htag hpayload))))
      fun _ => le_of_eq rfl
  have hmodBranch :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.modBranchBits
            ((Nat.unpair (queryOutput request)).1 % 3)
            (Nat.unpair (queryOutput request)).2 (width request)
            (PaddedProjectionQueryRunner.selectedModulus
              ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max
        (PolyDominated.natBitLength_pair htag hpayload)
        (PolyDominated.natBitLength_pair
          (PolyDominated.natBitLength_pair hright hmodulus) htag))
      fun _ => le_of_eq rfl
  have hmodulusChoice :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.modulusChoiceBits (inputLength request)
            (width request) (queryOutput request)) measureOf :=
    PolyDominated.mono
      (PolyDominated.max
        (PolyDominated.natBitLength_pair hlength
          (PolyDominated.natBitLength_pair hgap
            (PolyDominated.natBitLength_pair htag hpayload)))
        (PolyDominated.max hmodBranch
          (PolyDominated.natBitLength_pair
            (PolyDominated.natBitLength_pair hright hmodulus) htag)))
      fun _ => le_of_eq rfl
  have hresidueBits :
      PolyDominated
        (fun request =>
          CanonicalBitSerialModProgram.bitSerialModBits
            (Nat.unpair (queryOutput request)).2
            (PaddedProjectionQueryRunner.selectedModulus
              ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf :=
    PolyDominated.mono
      (PolyDominated.add (PolyDominated.natBitLength_pair hright hmodulus)
        (polyDominated_const 2))
      fun _ => bitSerialModBits_le_pair _ _
  have hstageThree :
      PolyDominated
        (fun request =>
          PreserveRightProgram.preserveRightBits
            (CanonicalBitSerialModProgram.bitSerialModBits
              (Nat.unpair (queryOutput request)).2
              (PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
            (CanonicalNativeModProgram.nativeModInput
              (Nat.unpair (queryOutput request)).2
              (PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
            ((Nat.unpair (queryOutput request)).1 % 3)
            ((Nat.unpair (queryOutput request)).2 %
              PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf :=
    PolyDominated.preserveRightBits hresidueBits
      (PolyDominated.natBitLength_pair
        (PolyDominated.natBitLength_pair hright hmodulus) htag)
      (PolyDominated.natBitLength_pair hresidue htag)
  have hswapFrame :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.swapFrameBits
            ((Nat.unpair (queryOutput request)).2 %
              PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3) (width request))
            ((Nat.unpair (queryOutput request)).1 % 3)) measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max
        (PolyDominated.natBitLength_pair hresidue htag)
        (PolyDominated.natBitLength_pair htag hresidue))
      fun _ => le_of_eq rfl
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength hcallFrame
      (PolyDominated.occurrenceStageBits hlength hstageOne
        (PolyDominated.occurrenceStageBits hlength htagFrame
          (PolyDominated.occurrenceStageBits hlength hstageTwo
            (PolyDominated.occurrenceStageBits hlength hmodulusTag
              (PolyDominated.occurrenceStageBits hlength hmodulusChoice
                (PolyDominated.occurrenceStageBits hlength hstageThree
                  hswapFrame)))))))
    fun _ => le_of_eq rfl

/-! ## 9. Row 4, closed outright

The padded query stream's register ledger charges the guard's saturating
factors, the source shape and query runners' declared widths, and the source
answer's *width*.  Every one of those is a published numeral or a halt check, so
row 4 needs nothing the interface does not already carry. -/

private theorem polyDominated_paddedQueryBits {Request : Type}
    {inputLength shapeCode encodedInput queryIndex bitIndex outerShapeBits
      outerQueryBits queryOutput measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hshapeCode : PolyDominated
      (fun request => natBitLength (shapeCode request)) measureOf)
    (hinput : PolyDominated
      (fun request => natBitLength (encodedInput request)) measureOf)
    (hqueryIndex : PolyDominated
      (fun request => natBitLength (queryIndex request)) measureOf)
    (hbitIndex : PolyDominated
      (fun request => natBitLength (bitIndex request)) measureOf)
    (hshapeBits : PolyDominated outerShapeBits measureOf)
    (hqueryBits : PolyDominated outerQueryBits measureOf)
    (houtput : PolyDominated
      (fun request => natBitLength (queryOutput request)) measureOf)
    (hcountValue : PolyDominated
      (fun request => (Nat.unpair (shapeCode request)).2) measureOf)
    (hwidthValue : PolyDominated
      (fun request => (Nat.unpair (shapeCode request)).1) measureOf) :
    PolyDominated
      (fun request =>
        paddedQueryBits (inputLength request) (shapeCode request)
          (encodedInput request) (queryIndex request) (bitIndex request)
          (outerShapeBits request) (outerQueryBits request)
          (queryOutput request))
      measureOf := by
  have hwidthBits := PolyDominated.natBitLength hwidthValue
  have htail :
      PolyDominated
        (fun request =>
          natBitLength
            (PaddedProjectionQueryRunner.queryTail (encodedInput request)
              (queryIndex request) (bitIndex request))) measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_pair hinput
        (PolyDominated.natBitLength_pair hqueryIndex hbitIndex))
      fun _ => le_of_eq rfl
  have hgl :
      PolyDominated
        (fun request =>
          (Nat.unpair (shapeCode request)).2 - queryIndex request) measureOf :=
    PolyDominated.mono hcountValue fun _ => by omega
  have hgr :
      PolyDominated
        (fun request =>
          (Nat.unpair (shapeCode request)).1 - bitIndex request) measureOf :=
    PolyDominated.mono hwidthValue fun _ => by omega
  have hguard :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.queryGuard (shapeCode request)
            (queryIndex request) (bitIndex request)) measureOf :=
    PolyDominated.mono (PolyDominated.mul hgl hgr) fun _ => le_of_eq rfl
  have hproduct :=
    PolyDominated.mul hgl (PolyDominated.add hgr (polyDominated_const 1))
  have hpairGuard :=
    PolyDominated.natBitLength_pair (PolyDominated.natBitLength hgl)
      (PolyDominated.natBitLength hgr)
  have hframeTail := PolyDominated.natBitLength_pair hwidthBits htail
  have hbitSerialBits :
      PolyDominated
        (fun request =>
          CanonicalBitSerialMulProgram.bitSerialMulBits (inputLength request)
            ((Nat.unpair (shapeCode request)).2 - queryIndex request)
            ((Nat.unpair (shapeCode request)).1 - bitIndex request)) measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max (left := fun _ => 1)
        (polyDominated_const (natBitLength 1))
        (PolyDominated.natBitLength_max hlength
          (PolyDominated.natBitLength_max hpairGuard
            (PolyDominated.natBitLength hproduct))))
      fun _ => le_of_eq rfl
  have hguardFrame :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.guardFrameBits (shapeCode request)
            (encodedInput request) (queryIndex request) (bitIndex request))
        measureOf :=
    PolyDominated.mono
      (PolyDominated.natBitLength_max
        (PolyDominated.natBitLength_pair hshapeCode htail)
        (PolyDominated.natBitLength_pair hpairGuard hframeTail))
      fun _ => le_of_eq rfl
  have hstageShape :
      PolyDominated
        (fun request =>
          PreserveRightProgram.preserveRightBits (outerShapeBits request)
            (inputLength request)
            (PaddedProjectionQueryRunner.queryTail (encodedInput request)
              (queryIndex request) (bitIndex request)) (shapeCode request))
        measureOf :=
    PolyDominated.preserveRightBits hshapeBits
      (PolyDominated.natBitLength_pair hlength htail)
      (PolyDominated.natBitLength_pair hshapeCode htail)
  have hstageGuard :
      PolyDominated
        (fun request =>
          PreserveRightProgram.preserveRightBits
            (CanonicalBitSerialMulProgram.bitSerialMulBits
              (inputLength request)
              ((Nat.unpair (shapeCode request)).2 - queryIndex request)
              ((Nat.unpair (shapeCode request)).1 - bitIndex request))
            (CanonicalBitSerialMulProgram.bitSerialMulInput
              ((Nat.unpair (shapeCode request)).2 - queryIndex request)
              ((Nat.unpair (shapeCode request)).1 - bitIndex request))
            (Nat.pair (Nat.unpair (shapeCode request)).1
              (PaddedProjectionQueryRunner.queryTail (encodedInput request)
                (queryIndex request) (bitIndex request)))
            (PaddedProjectionQueryRunner.queryGuard (shapeCode request)
              (queryIndex request) (bitIndex request))) measureOf :=
    PolyDominated.preserveRightBits hbitSerialBits
      (PolyDominated.natBitLength_pair hpairGuard hframeTail)
      (PolyDominated.natBitLength_pair (PolyDominated.natBitLength hguard)
        hframeTail)
  have hinRange :=
    polyDominated_inRangeBits (inputLength := inputLength)
      (width := fun request => (Nat.unpair (shapeCode request)).1)
      (tail := fun request =>
        PaddedProjectionQueryRunner.queryTail (encodedInput request)
          (queryIndex request) (bitIndex request))
      (outerQueryBits := outerQueryBits) (queryOutput := queryOutput)
      hlength hwidthBits htail hqueryBits houtput
  have htag :
      PolyDominated
        (fun request =>
          natBitLength ((Nat.unpair (queryOutput request)).1 % 3)) measureOf :=
    PolyDominated.mono (polyDominated_const (natBitLength 2)) fun _ =>
      natBitLength_mono (by omega)
  have hrightOut :
      PolyDominated
        (fun request =>
          natBitLength (Nat.unpair (queryOutput request)).2) measureOf :=
    PolyDominated.mono houtput fun request =>
      natBitLength_mono (Nat.unpair_right_le (queryOutput request))
  have hresidue :
      PolyDominated
        (fun request =>
          natBitLength
            ((Nat.unpair (queryOutput request)).2 %
              PaddedProjectionQueryRunner.selectedModulus
                ((Nat.unpair (queryOutput request)).1 % 3)
                (Nat.unpair (shapeCode request)).1)) measureOf :=
    PolyDominated.mono hrightOut fun _ => natBitLength_mono (Nat.mod_le _ _)
  have hemitted :
      PolyDominated
        (fun request =>
          natBitLength
            (PaddedProjectionQueryRunner.emittedValue
              (Nat.unpair (shapeCode request)).1 (queryOutput request)))
        measureOf :=
    PolyDominated.mono (PolyDominated.natBitLength_pair htag hresidue)
      fun _ => le_of_eq rfl
  have hqueryValue :
      PolyDominated
        (fun request =>
          natBitLength
            (PaddedProjectionQueryRunner.paddedQueryValue (shapeCode request)
              (queryIndex request) (bitIndex request) (queryOutput request)))
        measureOf := by
    refine PolyDominated.mono
      (PolyDominated.natBitLength_max (left := fun _ => Nat.pair 2 0)
        (right := fun request =>
          PaddedProjectionQueryRunner.emittedValue
            (Nat.unpair (shapeCode request)).1 (queryOutput request))
        (polyDominated_const (natBitLength (Nat.pair 2 0))) hemitted)
      fun _ => natBitLength_mono ?_
    simp only [PaddedProjectionQueryRunner.paddedQueryValue]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  have hchoice :
      PolyDominated
        (fun request =>
          PaddedProjectionQueryRunner.queryChoiceBits (inputLength request)
            (shapeCode request) (encodedInput request) (queryIndex request)
            (bitIndex request) (outerQueryBits request) (queryOutput request))
        measureOf :=
    PolyDominated.mono
      (PolyDominated.max
        (PolyDominated.natBitLength_pair hlength
          (PolyDominated.natBitLength_pair (PolyDominated.natBitLength hguard)
            hframeTail))
        (PolyDominated.max
          (PolyDominated.max
            (polyDominated_const PaddedProjectionQueryRunner.constantFalseBits)
            hinRange)
          hqueryValue))
      fun _ => le_of_eq rfl
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength hstageShape
      (PolyDominated.occurrenceStageBits hlength hguardFrame
        (PolyDominated.occurrenceStageBits hlength hstageGuard hchoice)))
    fun _ => le_of_eq rfl

private theorem one_le_queryBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) :
    1 ≤ queryBudget outer.pcp n := by
  have hcoefficient := outer.pcp.query.coefficientPositive
  have hpower :
      0 < (nativeMeasure outer.pcp n + 1) ^ outer.pcp.query.degree :=
    pow_pos (by omega) _
  simp only [queryBudget, polynomialBudget]
  exact Nat.mul_pos hcoefficient hpower

/-- **The source answer's width is the source runner's own halt check.** -/
theorem natBitLength_queryExecuteAt_le {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (n encodedInput queryIndex bitIndex : ℕ) :
    natBitLength
        (queryExecuteAt outer.pcp n encodedInput queryIndex bitIndex) ≤
      queryBudget outer.pcp n := by
  simp only [queryExecuteAt]
  cases hrun :
      runNPOracleProgram outer.pcp.query.program (queryBudget outer.pcp n)
        (queryBudget outer.pcp n)
        (initialNPOracleState n
          (queryCode n encodedInput queryIndex bitIndex)) with
  | none =>
      have hzero : natBitLength ((none : Option ℕ).getD 0) = 1 := by
        simp [natBitLength]
      rw [hzero]
      exact one_le_queryBudget outer n
  | some output => exact run_output_bounded hrun

/-- **Row 4, closed.**  The padded query stream's register ledger needs no
premise beyond the published interface. -/
theorem polyDominated_publishedPaddedQueryBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated (fun request => publishedPaddedQueryBits outer request)
      ProjectionQueryRequest.measure := by
  have hlength :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength request.inputArity) ProjectionQueryRequest.measure :=
    ⟨1, dominated_natBitLength_of_le_measure queryArity_le_measure⟩
  have hinput :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength (encodeBitInput request.input))
        ProjectionQueryRequest.measure :=
    ⟨1, 1, fun request => by
      have hcode := natBitLength_encodeBitInput_le request.input
      have harity := queryArity_le_measure request
      change natBitLength (encodeBitInput request.input) ≤
        1 * (ProjectionQueryRequest.measure request + 1) ^ 1
      rw [Nat.one_mul, Nat.pow_one]
      omega⟩
  have hqueryIndex :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength request.query.val) ProjectionQueryRequest.measure :=
    ⟨1, dominated_natBitLength_of_le_measure fun request => by
      have hlt := request.query.isLt
      simp only [ProjectionQueryRequest.measure]
      omega⟩
  have hbitIndex :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength request.bit.val) ProjectionQueryRequest.measure :=
    ⟨1, dominated_natBitLength_of_le_measure fun request => by
      have hlt := request.bit.isLt
      simp only [ProjectionQueryRequest.measure]
      omega⟩
  have houtput :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength
            (queryExecuteAt outer.pcp request.inputArity
              (encodeBitInput request.input) request.query.val
              request.bit.val)) ProjectionQueryRequest.measure :=
    PolyDominated.mono (sourcePoly_atQuery (sourcePoly_queryBudget outer))
      fun _ => natBitLength_queryExecuteAt_le outer _ _ _ _
  have hshapeCode :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          natBitLength (outer.pcp.shape.execute request.inputArity))
        ProjectionQueryRequest.measure :=
    sourcePoly_atQuery (sourcePoly_natBitLength_shapeExecute outer)
  have hcountValue :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          (Nat.unpair (outer.pcp.shape.execute request.inputArity)).2)
        ProjectionQueryRequest.measure :=
    sourcePoly_atQuery (sourcePoly_queryCount outer)
  have hwidthValue :
      PolyDominated
        (fun request : ProjectionQueryRequest =>
          (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1)
        ProjectionQueryRequest.measure :=
    sourcePoly_atQuery (sourcePoly_nativeWidth outer)
  refine PolyDominated.mono
    (polyDominated_paddedQueryBits
      (inputLength := fun request : ProjectionQueryRequest =>
        request.inputArity)
      (shapeCode := fun request : ProjectionQueryRequest =>
        outer.pcp.shape.execute request.inputArity)
      (encodedInput := fun request : ProjectionQueryRequest =>
        encodeBitInput request.input)
      (queryIndex := fun request : ProjectionQueryRequest => request.query.val)
      (bitIndex := fun request : ProjectionQueryRequest => request.bit.val)
      (outerShapeBits := fun request : ProjectionQueryRequest =>
        outer.pcp.shape.budget request.inputArity)
      (outerQueryBits := fun request : ProjectionQueryRequest =>
        queryBudget outer.pcp request.inputArity)
      (queryOutput := fun request : ProjectionQueryRequest =>
        queryExecuteAt outer.pcp request.inputArity
          (encodeBitInput request.input) request.query.val request.bit.val)
      hlength hshapeCode hinput hqueryIndex hbitIndex
      (sourcePoly_atQuery (sourcePoly_shapeBudget outer))
      (sourcePoly_atQuery (sourcePoly_queryBudget outer)) houtput hcountValue
      hwidthValue)
    fun _ => le_of_eq rfl

/-! ## 11. Row 5, closed outright

`inRangeFuel` charges the modular reduction twice at the two halves of the
source answer.  With `CanonicalBitSerialModProgram` on that stage the charge is
`13 * natBitLength numerator + 10` — linear in the answer's *width*, which §10's
halt check already dominates — rather than linear in its magnitude.  Row 5
therefore needs no source-side normalization at all. -/

private theorem bitsLength_le_succ (value : ℕ) :
    value.bits.length ≤ value + 1 := by
  have hsize : value.bits.length ≤ natBitLength value := by
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le).2
    simpa [natBitLength, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)
  have hwidth := ValidatorCompositeLeafBounds.natBitLength_le_succ value
  omega

private theorem bitSerialMulFuel_le_linear (value : ℕ) :
    CanonicalBitSerialMulProgram.bitSerialMulFuel value ≤ 13 + 8 * value := by
  have hbound := CanonicalBitSerialMulProgram.bitSerialMulFuel_le value
  have hlength := bitsLength_le_succ value
  omega

private theorem polyDominated_inRangeFuel {Request : Type}
    {outerQuery : NPOracleProgram}
    {outerQueryFuel width queryOutput measureOf : Request → ℕ}
    (hfuel : PolyDominated outerQueryFuel measureOf)
    (houtput : PolyDominated
      (fun request => natBitLength (queryOutput request)) measureOf) :
    PolyDominated
      (fun request =>
        PaddedProjectionQueryRunner.inRangeFuel outerQuery
          (outerQueryFuel request) (width request) (queryOutput request))
      measureOf := by
  obtain ⟨degree, hfuelBound, houtputBound⟩ := PolyDominated.align hfuel houtput
  refine ⟨degree, ?_⟩
  have hleft :
      Dominated
        (fun request => natBitLength (Nat.unpair (queryOutput request)).1)
        measureOf degree :=
    houtputBound.mono fun request =>
      natBitLength_mono (Nat.unpair_left_le (queryOutput request))
  have hright :
      Dominated
        (fun request => natBitLength (Nat.unpair (queryOutput request)).2)
        measureOf degree :=
    houtputBound.mono fun request =>
      natBitLength_mono (Nat.unpair_right_le (queryOutput request))
  have hmodLeft :
      Dominated
        (fun request =>
          CanonicalBitSerialModProgram.bitSerialModFuel
            (Nat.unpair (queryOutput request)).1 3) measureOf degree :=
    ((hleft.const_mul 13).add (dominated_const 10 degree)).mono fun _ =>
      CanonicalBitSerialModProgram.bitSerialModFuel_le_natBitLength _ 3
  have hmodRight :
      Dominated
        (fun request =>
          CanonicalBitSerialModProgram.bitSerialModFuel
            (Nat.unpair (queryOutput request)).2
            (PaddedProjectionQueryRunner.selectedModulus
              ((Nat.unpair (queryOutput request)).1 % 3) (width request)))
        measureOf degree :=
    ((hright.const_mul 13).add (dominated_const 10 degree)).mono fun _ =>
      CanonicalBitSerialModProgram.bitSerialModFuel_le_natBitLength _ _
  simp only [PaddedProjectionQueryRunner.inRangeFuel]
  exact Dominated.linkFuel (dominated_const 6 degree)
    (Dominated.linkFuel hfuelBound.preserveRightFuel
      (Dominated.linkFuel (dominated_const 9 degree)
        (Dominated.linkFuel hmodLeft.preserveRightFuel
          (Dominated.linkFuel (dominated_const 5 degree)
            (Dominated.linkFuel
              (dominated_const
                (TaggedProgramChoice.taggedProgramChoiceFuel 7) degree)
              (Dominated.linkFuel hmodRight.preserveRightFuel
                (dominated_const 4 degree)))))))

private theorem polyDominated_paddedQueryFuel {Request : Type}
    {outerQuery : NPOracleProgram}
    {outerShapeFuel outerQueryFuel shapeCode bitIndex queryOutput measureOf :
      Request → ℕ}
    (hshapeFuel : PolyDominated outerShapeFuel measureOf)
    (hqueryFuel : PolyDominated outerQueryFuel measureOf)
    (hwidthValue : PolyDominated
      (fun request => (Nat.unpair (shapeCode request)).1) measureOf)
    (houtput : PolyDominated
      (fun request => natBitLength (queryOutput request)) measureOf) :
    PolyDominated
      (fun request =>
        paddedQueryFuel outerQuery (outerShapeFuel request)
          (outerQueryFuel request) (shapeCode request) (bitIndex request)
          (queryOutput request)) measureOf := by
  have hmul :
      PolyDominated
        (fun request =>
          CanonicalBitSerialMulProgram.bitSerialMulFuel
            ((Nat.unpair (shapeCode request)).1 - bitIndex request)) measureOf :=
    PolyDominated.mono
      (PolyDominated.add (polyDominated_const 13)
        (PolyDominated.const_mul 8
          (PolyDominated.mono hwidthValue fun _ => by omega)))
      fun _ => bitSerialMulFuel_le_linear _
  obtain ⟨shapeDegree, hshapeBound⟩ := hshapeFuel
  obtain ⟨rangeDegree, hrangeBound⟩ :=
    polyDominated_inRangeFuel (outerQuery := outerQuery)
      (outerQueryFuel := outerQueryFuel)
      (width := fun request => (Nat.unpair (shapeCode request)).1)
      (queryOutput := queryOutput) hqueryFuel houtput
  obtain ⟨mulDegree, hmulBound⟩ := hmul
  refine ⟨max shapeDegree (max rangeDegree mulDegree), ?_⟩
  simp only [paddedQueryFuel]
  exact Dominated.linkFuel
    (hshapeBound.degree_mono (by omega)).preserveRightFuel
    (Dominated.linkFuel (dominated_const 13 _)
      (Dominated.linkFuel (hmulBound.degree_mono (by omega)).preserveRightFuel
        (Dominated.taggedProgramChoiceFuel
          ((dominated_const 4 _).max (hrangeBound.degree_mono (by omega))))))

/-- **Row 5, closed.**  The padded query stream's clock is now charged against
the source answer's *width*, which is the source runner's own halt check. -/
theorem polyDominated_publishedPaddedQueryFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    PolyDominated (fun request => publishedPaddedQueryFuel outer request)
      ProjectionQueryRequest.measure :=
  PolyDominated.mono
    (polyDominated_paddedQueryFuel (outerQuery := outer.pcp.query.program)
      (outerShapeFuel := fun request : ProjectionQueryRequest =>
        outer.pcp.shape.budget request.inputArity)
      (outerQueryFuel := fun request : ProjectionQueryRequest =>
        queryBudget outer.pcp request.inputArity)
      (shapeCode := fun request : ProjectionQueryRequest =>
        outer.pcp.shape.execute request.inputArity)
      (bitIndex := fun request : ProjectionQueryRequest => request.bit.val)
      (queryOutput := fun request : ProjectionQueryRequest =>
        queryExecuteAt outer.pcp request.inputArity
          (encodeBitInput request.input) request.query.val request.bit.val)
      (sourcePoly_atQuery (sourcePoly_shapeBudget outer))
      (sourcePoly_atQuery (sourcePoly_queryBudget outer))
      (sourcePoly_atQuery (sourcePoly_nativeWidth outer))
      (PolyDominated.mono (sourcePoly_atQuery (sourcePoly_queryBudget outer))
        fun _ => natBitLength_queryExecuteAt_le outer _ _ _ _))
    fun _ => le_of_eq rfl

/-! ## 12. The capstone, modulo the numeral bank

Four of the six runner charges are theorems of the published interface outright;
the padded shape stream's two reduce to the numeral bank's own charges for the
program that computes the width envelope.  Nothing source-side survives: the
padded query stream is charged against the source answer's *width*, which is the
source runner's own halt check, and the padded decision stream against the
published width budget through `proofSizeBound`.  §13 and §14 discharge the two
bank charges, and §15 removes the last premise. -/

/-- **The padded presentation, from the numeral bank alone.** -/
theorem exists_presentsPaddedOuterPCP_of_leaves {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (hbank : WidthEnvelopeCharged outer) :
    ∃ pcp :
        ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth),
      PresentsPaddedOuterPCP outer pcp := by
  obtain ⟨shapeBitsDegree, hshapeBits⟩ :=
    polyDominated_publishedPaddedShapeBits outer hbank
  obtain ⟨shapeFuelDegree, hshapeFuel⟩ :=
    polyDominated_publishedPaddedShapeFuel outer hbank
  obtain ⟨queryBitsDegree, hqueryBits⟩ :=
    polyDominated_publishedPaddedQueryBits outer
  obtain ⟨queryFuelDegree, hqueryFuel⟩ :=
    polyDominated_publishedPaddedQueryFuel outer
  obtain ⟨decisionBitsDegree, hdecisionBits⟩ :=
    polyDominated_publishedPaddedDecisionBits outer
  obtain ⟨decisionFuelDegree, hdecisionFuel⟩ :=
    polyDominated_publishedPaddedDecisionFuel outer
  exact exists_presentsPaddedOuterPCP_of_dominated outer
    (max (max shapeBitsDegree shapeFuelDegree)
      (max (max queryBitsDegree queryFuelDegree)
        (max decisionBitsDegree decisionFuelDegree)))
    (hshapeBits.degree_mono (by omega)) (hshapeFuel.degree_mono (by omega))
    (hqueryBits.degree_mono (by omega)) (hqueryFuel.degree_mono (by omega))
    (hdecisionBits.degree_mono (by omega))
    (hdecisionFuel.degree_mono (by omega))

/-- **`bodyRun` at the published instance.**  The padded-PCP presentation
premise of `PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` is a
consequence of the published contracts together with the numeral bank's own two
width-envelope charges. -/
theorem inverse_bodyRun_of_publishedLeaves (contracts : PublishedContracts)
    (clockDepth : ℕ)
    (hbank :
      WidthEnvelopeCharged (publishedHierarchyOuterPCP contracts clockDepth)) :
    ∃ pcp :
        ExecutableProjectionPCP
          (publishedRefuterSource contracts clockDepth).hierarchyMachine
          (pairClock clockDepth),
      PresentsPaddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)
        pcp :=
  exists_presentsPaddedOuterPCP_of_leaves
    (publishedHierarchyOuterPCP contracts clockDepth) hbank

private theorem clog_le_self (value : ℕ) : Nat.clog 2 value ≤ value :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt value.lt_two_pow_self)

private theorem polyDominated_pow {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    ∀ exponent : ℕ,
      PolyDominated (fun request => value request ^ exponent) measureOf
  | 0 => PolyDominated.mono (polyDominated_const 1) fun _ => le_of_eq rfl
  | exponent + 1 =>
      PolyDominated.mono (PolyDominated.mul (polyDominated_pow h exponent) h)
        fun _ => le_of_eq (pow_succ _ _)

private theorem polyDominated_logScale {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => logScale (value request)) measureOf :=
  PolyDominated.mono (PolyDominated.add h (polyDominated_const 2))
    fun request => logScale_le_add_two (value request)

private theorem polyDominated_bitSerialMulFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated
      (fun request =>
        CanonicalBitSerialMulProgram.bitSerialMulFuel (value request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.add (polyDominated_const 13) (PolyDominated.const_mul 8 h))
    fun _ => bitSerialMulFuel_le_linear _

private theorem polyDominated_binaryNatCeilLogFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated
      (fun request =>
        CanonicalNatCeilLogProgram.binaryNatCeilLogFuel (value request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.add
      (PolyDominated.const_mul 4
        (PolyDominated.mono h fun request => clog_le_self (value request)))
      (polyDominated_const 6))
    fun _ => le_of_eq rfl

private theorem polyDominated_logScaleFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => logScaleFuel (value request)) measureOf := by
  obtain ⟨degree, hceil⟩ :=
    polyDominated_binaryNatCeilLogFuel (PolyDominated.add h
      (polyDominated_const 2))
  refine ⟨degree, ?_⟩
  simp only [logScaleFuel]
  exact Dominated.linkFuel (dominated_const 3 degree) hceil

private theorem polyDominated_powStepFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => powStepFuel (value request)) measureOf := by
  obtain ⟨degree, hmul⟩ := polyDominated_bitSerialMulFuel h
  refine ⟨degree, ?_⟩
  simp only [powStepFuel]
  exact Dominated.linkFuel (dominated_const 3 degree) hmul.preserveRightFuel

private theorem polyDominated_powLoopFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf)
    (exponent : ℕ) :
    PolyDominated (fun request => powLoopFuel exponent (value request))
      measureOf := by
  induction exponent with
  | zero =>
      exact PolyDominated.mono (polyDominated_const 1) fun _ => le_of_eq rfl
  | succ exponent ih =>
      obtain ⟨degree, hstep, hrest⟩ :=
        PolyDominated.align (polyDominated_powStepFuel h) ih
      refine ⟨degree, ?_⟩
      simp only [powLoopFuel]
      exact Dominated.linkFuel hstep hrest

private theorem polyDominated_powFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf)
    (exponent : ℕ) :
    PolyDominated (fun request => powFuel exponent (value request))
      measureOf := by
  obtain ⟨degree, hloop⟩ := polyDominated_powLoopFuel h exponent
  refine ⟨degree, ?_⟩
  simp only [powFuel]
  exact Dominated.linkFuel (dominated_const 3 degree)
    (Dominated.linkFuel hloop (dominated_const 2 degree))

private theorem polyDominated_logPowFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf)
    (exponent : ℕ) :
    PolyDominated (fun request => logPowFuel exponent (value request))
      measureOf := by
  obtain ⟨degree, hscale, hpow⟩ :=
    PolyDominated.align (polyDominated_logScaleFuel h)
      (polyDominated_powFuel (polyDominated_logScale h) exponent)
  refine ⟨degree, ?_⟩
  simp only [logPowFuel]
  exact Dominated.linkFuel hscale hpow

private theorem polyDominated_immediateMulFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => immediateMulFuel (value request))
      measureOf := by
  obtain ⟨degree, hmul⟩ := polyDominated_bitSerialMulFuel h
  refine ⟨degree, ?_⟩
  simp only [immediateMulFuel]
  exact Dominated.linkFuel (dominated_const 3 degree) hmul

private theorem polyDominated_widthBudgetCoreFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf)
    (coefficient exponent : ℕ) :
    PolyDominated
      (fun request => widthBudgetCoreFuel coefficient exponent (value request))
      measureOf := by
  have hproduct :=
    PolyDominated.mul (polyDominated_pow (polyDominated_logScale h) exponent) h
  obtain ⟨logDegree, hlogPow⟩ := polyDominated_logPowFuel h exponent
  obtain ⟨mulDegree, hmul⟩ := polyDominated_bitSerialMulFuel h
  obtain ⟨immediateDegree, himmediate⟩ :=
    polyDominated_immediateMulFuel hproduct
  refine ⟨max logDegree (max mulDegree immediateDegree), ?_⟩
  simp only [widthBudgetCoreFuel]
  exact Dominated.linkFuel (dominated_const 2 _)
    (Dominated.linkFuel (hlogPow.degree_mono (by omega)).preserveRightFuel
      (Dominated.linkFuel (hmul.degree_mono (by omega))
        (himmediate.degree_mono (by omega))))

private theorem polyDominated_floorLogFuel {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated (fun request => floorLogFuel (value request)) measureOf := by
  obtain ⟨degree, hceil⟩ :=
    polyDominated_binaryNatCeilLogFuel (PolyDominated.add h
      (polyDominated_const 1))
  refine ⟨degree, ?_⟩
  simp only [floorLogFuel]
  exact Dominated.linkFuel (dominated_const 2 degree)
    (Dominated.linkFuel hceil (dominated_const 2 degree))

theorem sourcePoly_widthBudgetValue (clockDepth coefficient exponent : ℕ) :
    SourcePoly
      (fun n => widthBudgetValue clockDepth coefficient exponent n) := by
  have hclock := sourcePoly_pairClock clockDepth
  refine PolyDominated.mono
    (PolyDominated.const_mul coefficient
      (PolyDominated.mul hclock
        (polyDominated_pow (polyDominated_logScale hclock) exponent)))
    fun _ => ?_
  exact le_of_eq (by simp only [widthBudgetValue]; ring)

/-- **The width-envelope clock, dominated.** -/
theorem sourcePoly_widthEnvelopeFuel (clockDepth coefficient exponent : ℕ) :
    SourcePoly
      (fun n => widthEnvelopeFuel clockDepth coefficient exponent n) := by
  obtain ⟨degree, hcore, hfloor⟩ :=
    PolyDominated.align
      (polyDominated_widthBudgetCoreFuel (sourcePoly_pairClock clockDepth)
        coefficient exponent)
      (polyDominated_floorLogFuel
        (sourcePoly_widthBudgetValue clockDepth coefficient exponent))
  refine ⟨degree, ?_⟩
  simp only [widthEnvelopeFuel]
  exact Dominated.linkFuel
    (dominated_const (pairIterFuel clockDepth) degree)
    (Dominated.linkFuel hcore hfloor)

/-! ## 14. The numeral bank's width-envelope register ledger

The bits spine is a nine-stage maximum with two recursions — one over the clock
depth, one over the frozen power exponent.  Neither needs a numeric envelope:
both recurse on a *charge* that is itself dominated at every step, so the
induction runs entirely inside `PolyDominated`. -/

private theorem binaryNatCeilLogBits_le (value : ℕ) :
    CanonicalNatCeilLogProgram.binaryNatCeilLogBits value ≤ value + 1 := by
  have hclog := clog_le_self value
  simp only [CanonicalNatCeilLogProgram.binaryNatCeilLogBits,
    CanonicalNatCeilLogProgram.binaryNatCeilLogRegisterBound, natBitLength]
  rw [Nat.log_pow (by omega)]
  omega

private theorem polyDominated_binaryNatCeilLogBits {Request : Type}
    {value measureOf : Request → ℕ} (h : PolyDominated value measureOf) :
    PolyDominated
      (fun request =>
        CanonicalNatCeilLogProgram.binaryNatCeilLogBits (value request))
      measureOf :=
  PolyDominated.mono (PolyDominated.add h (polyDominated_const 1))
    fun _ => binaryNatCeilLogBits_le _

private theorem polyDominated_bitSerialMulBits {Request : Type}
    {inputLength left right measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated
      (fun request =>
        CanonicalBitSerialMulProgram.bitSerialMulBits (inputLength request)
          (left request) (right request)) measureOf :=
  PolyDominated.mono
    (PolyDominated.natBitLength_max (left := fun _ => 1)
      (polyDominated_const (natBitLength 1))
      (PolyDominated.natBitLength_max hlength
        (PolyDominated.natBitLength_max
          (PolyDominated.natBitLength_pair (PolyDominated.natBitLength hleft)
            (PolyDominated.natBitLength hright))
          (PolyDominated.natBitLength
            (PolyDominated.mul hleft
              (PolyDominated.add hright (polyDominated_const 1)))))))
    fun _ => le_of_eq rfl

private theorem polyDominated_pairIterBits {Request : Type}
    {inputLength measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf) :
    ∀ (depth : ℕ) (value : Request → ℕ),
      PolyDominated (fun request => natBitLength (value request)) measureOf →
      PolyDominated
        (fun request => pairIterBits (inputLength request) depth (value request))
        measureOf
  | 0, _, hvalue => PolyDominated.mono hvalue fun _ => le_of_eq rfl
  | depth + 1, value, hvalue =>
      PolyDominated.mono
        (PolyDominated.occurrenceStageBits hlength
          (PolyDominated.natBitLength_pair hvalue hvalue)
          (polyDominated_pairIterBits hlength depth
            (fun request => Nat.pair (value request) (value request))
            (PolyDominated.natBitLength_pair hvalue hvalue)))
        fun _ => le_of_eq rfl

private theorem polyDominated_logScaleBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (h : PolyDominated value measureOf) :
    PolyDominated
      (fun request => logScaleBits (inputLength request) (value request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (PolyDominated.natBitLength
        (PolyDominated.add h (polyDominated_const 2)))
      (polyDominated_binaryNatCeilLogBits
        (PolyDominated.add h (polyDominated_const 2))))
    fun _ => le_of_eq rfl

private theorem polyDominated_floorLogBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (h : PolyDominated value measureOf) :
    PolyDominated
      (fun request => floorLogBits (inputLength request) (value request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (PolyDominated.natBitLength
        (PolyDominated.add h (polyDominated_const 1)))
      (PolyDominated.occurrenceStageBits hlength
        (polyDominated_binaryNatCeilLogBits
          (PolyDominated.add h (polyDominated_const 1)))
        (PolyDominated.natBitLength
          (PolyDominated.mono
            (PolyDominated.add h (polyDominated_const 1))
            fun request => clog_le_self (value request + 1)))))
    fun _ => le_of_eq rfl

private theorem polyDominated_powStepBits {Request : Type}
    {inputLength accumulator value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (haccumulator : PolyDominated accumulator measureOf)
    (hvalue : PolyDominated value measureOf) :
    PolyDominated
      (fun request =>
        powStepBits (inputLength request) (accumulator request) (value request))
      measureOf := by
  have haccumulatorBits := PolyDominated.natBitLength haccumulator
  have hvalueBits := PolyDominated.natBitLength hvalue
  have hproduct := PolyDominated.mul haccumulator hvalue
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (PolyDominated.natBitLength_pair
        (PolyDominated.natBitLength_pair haccumulatorBits hvalueBits)
        hvalueBits)
      (PolyDominated.preserveRightBits
        (polyDominated_bitSerialMulBits hlength haccumulator hvalue)
        (PolyDominated.natBitLength_pair
          (PolyDominated.natBitLength_pair haccumulatorBits hvalueBits)
          hvalueBits)
        (PolyDominated.natBitLength_pair
          (PolyDominated.natBitLength hproduct) hvalueBits)))
    fun _ => le_of_eq rfl

private theorem polyDominated_powLoopBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hvalue : PolyDominated value measureOf) :
    ∀ (exponent : ℕ) (accumulator : Request → ℕ),
      PolyDominated accumulator measureOf →
      PolyDominated
        (fun request =>
          powLoopBits (inputLength request) exponent (accumulator request)
            (value request)) measureOf
  | 0, _, haccumulator =>
      PolyDominated.mono
        (PolyDominated.natBitLength_pair
          (PolyDominated.natBitLength haccumulator)
          (PolyDominated.natBitLength hvalue))
        fun _ => le_of_eq rfl
  | exponent + 1, accumulator, haccumulator =>
      PolyDominated.mono
        (PolyDominated.occurrenceStageBits hlength
          (polyDominated_powStepBits hlength haccumulator hvalue)
          (polyDominated_powLoopBits hlength hvalue exponent
            (fun request => accumulator request * value request)
            (PolyDominated.mul haccumulator hvalue)))
        fun _ => le_of_eq rfl

private theorem polyDominated_powBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hvalue : PolyDominated value measureOf) (exponent : ℕ) :
    PolyDominated
      (fun request =>
        powBits (inputLength request) exponent (value request)) measureOf := by
  have hvalueBits := PolyDominated.natBitLength hvalue
  have hone : PolyDominated (fun _ : Request => (1 : ℕ)) measureOf :=
    polyDominated_const 1
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (PolyDominated.natBitLength_pair
        (PolyDominated.natBitLength hone) hvalueBits)
      (PolyDominated.occurrenceStageBits hlength
        (polyDominated_powLoopBits hlength hvalue exponent
          (fun _ => 1) hone)
        (PolyDominated.natBitLength_pair
          (PolyDominated.natBitLength
            (PolyDominated.mul hone (polyDominated_pow hvalue exponent)))
          hvalueBits)))
    fun _ => le_of_eq rfl

private theorem polyDominated_logPowBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hvalue : PolyDominated value measureOf) (exponent : ℕ) :
    PolyDominated
      (fun request =>
        logPowBits (inputLength request) exponent (value request)) measureOf :=
  PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (polyDominated_logScaleBits hlength hvalue)
      (polyDominated_powBits hlength (polyDominated_logScale hvalue) exponent))
    fun _ => le_of_eq rfl

private theorem polyDominated_immediateMulBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hvalue : PolyDominated value measureOf) (factor : ℕ) :
    PolyDominated
      (fun request =>
        immediateMulBits (inputLength request) factor (value request))
      measureOf :=
  PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (PolyDominated.natBitLength_pair (left := fun _ => factor)
        (polyDominated_const (natBitLength factor))
        (PolyDominated.natBitLength hvalue))
      (polyDominated_bitSerialMulBits hlength (polyDominated_const factor)
        hvalue))
    fun _ => le_of_eq rfl

private theorem polyDominated_widthBudgetCoreBits {Request : Type}
    {inputLength value measureOf : Request → ℕ}
    (hlength : PolyDominated
      (fun request => natBitLength (inputLength request)) measureOf)
    (hvalue : PolyDominated value measureOf) (coefficient exponent : ℕ) :
    PolyDominated
      (fun request =>
        widthBudgetCoreBits (inputLength request) coefficient exponent
          (value request)) measureOf := by
  have hvalueBits := PolyDominated.natBitLength hvalue
  have hpower := polyDominated_pow (polyDominated_logScale hvalue) exponent
  have hduplicate := PolyDominated.natBitLength_pair hvalueBits hvalueBits
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength hduplicate
      (PolyDominated.occurrenceStageBits hlength
        (PolyDominated.preserveRightBits
          (polyDominated_logPowBits hlength hvalue exponent) hduplicate
          (PolyDominated.natBitLength_pair
            (PolyDominated.natBitLength hpower) hvalueBits))
        (PolyDominated.occurrenceStageBits hlength
          (polyDominated_bitSerialMulBits hlength hpower hvalue)
          (polyDominated_immediateMulBits hlength
            (PolyDominated.mul hpower hvalue) coefficient))))
    fun _ => le_of_eq rfl

/-- **The width-envelope register ledger, dominated.** -/
theorem sourcePoly_widthEnvelopeBits (clockDepth coefficient exponent : ℕ) :
    SourcePoly
      (fun n => widthEnvelopeBits n clockDepth coefficient exponent n) := by
  have hlength : SourcePoly (fun n => natBitLength n) :=
    PolyDominated.natBitLength sourcePoly_id
  refine PolyDominated.mono
    (PolyDominated.occurrenceStageBits hlength
      (polyDominated_pairIterBits hlength clockDepth (fun n => n) hlength)
      (PolyDominated.occurrenceStageBits hlength
        (polyDominated_widthBudgetCoreBits hlength
          (sourcePoly_pairClock clockDepth) coefficient exponent)
        (polyDominated_floorLogBits hlength
          (sourcePoly_widthBudgetValue clockDepth coefficient exponent))))
    fun _ => le_of_eq rfl

theorem widthEnvelopeCharged_published {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) : WidthEnvelopeCharged outer :=
  ⟨sourcePoly_atShape
      (sourcePoly_widthEnvelopeBits clockDepth outer.pcp.shape.coefficient
        outer.proofExponent) clockDepth,
    sourcePoly_atShape
      (sourcePoly_widthEnvelopeFuel clockDepth outer.pcp.shape.coefficient
        outer.proofExponent) clockDepth⟩

/-- **The padded presentation, premise-free.** -/
theorem exists_presentsPaddedOuterPCP_published {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    ∃ pcp :
        ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth),
      PresentsPaddedOuterPCP outer pcp :=
  exists_presentsPaddedOuterPCP_of_leaves outer
    (widthEnvelopeCharged_published outer)

/-- **`bodyRun` from the published contracts alone.**  This eliminates the
padded-PCP presentation premise of
`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` outright: the
padded projection PCP over the published outer PCP exists, and it presents. -/
theorem inverse_bodyRun_of_publishedContracts (contracts : PublishedContracts)
    (clockDepth : ℕ) :
    ∃ pcp :
        ExecutableProjectionPCP
          (publishedRefuterSource contracts clockDepth).hierarchyMachine
          (pairClock clockDepth),
      PresentsPaddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)
        pcp :=
  exists_presentsPaddedOuterPCP_published
    (publishedHierarchyOuterPCP contracts clockDepth)

end NearCubicWires.PaddedRunnerBudgetClosure
