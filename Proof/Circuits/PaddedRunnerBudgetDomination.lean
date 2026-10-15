import Proof.PCP.PaddedProjectionPresentedPCP
import Proof.Circuits.ValidatorCompositeLeafBounds
import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.PaddedRunnerBudgetDomination

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionDecisionRunner
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionPresentedPCP
open NearCubicWires.PaddedProjectionQueryRunner
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedProjectionShapeRunner
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## 1. The coefficient-free domination judgement -/

/-- **The walk's judgement.**  A charge is *dominated* at a degree when some
uniform coefficient makes it fit the polynomial budget at its own measure.  The
coefficient is quantified away because every linker in the cone contributes a
closed `programRegisterSpan` of a composed instruction stream: those numerals
must never enter a statement the kernel might try to evaluate. -/
def Dominated {Request : Type} (charge measureOf : Request → ℕ)
    (degree : ℕ) : Prop :=
  ∃ coefficient, ∀ request : Request,
    PolyBounded (charge request) (measureOf request) coefficient degree

theorem Dominated.of_polyBounded {Request : Type}
    {charge measureOf : Request → ℕ} {coefficient degree : ℕ}
    (h : ∀ request, PolyBounded (charge request) (measureOf request)
      coefficient degree) :
    Dominated charge measureOf degree := ⟨coefficient, h⟩

/-! ## 2. One closure lemma per cost shape -/

theorem Dominated.mono {Request : Type} {charge charge' measureOf :
    Request → ℕ} {degree : ℕ} (h : Dominated charge measureOf degree)
    (hle : ∀ request, charge' request ≤ charge request) :
    Dominated charge' measureOf degree := by
  obtain ⟨coefficient, hcoefficient⟩ := h
  exact ⟨coefficient, fun request => (hcoefficient request).mono (hle request)⟩

theorem Dominated.degree_mono {Request : Type} {charge measureOf : Request → ℕ}
    {degree degree' : ℕ} (h : Dominated charge measureOf degree)
    (hle : degree ≤ degree') : Dominated charge measureOf degree' := by
  obtain ⟨coefficient, hcoefficient⟩ := h
  exact ⟨coefficient, fun request => (hcoefficient request).degree_mono hle⟩

/-- A charge that does not move with the request. -/
theorem dominated_const {Request : Type} {measureOf : Request → ℕ}
    (value degree : ℕ) :
    Dominated (fun _ : Request => value) measureOf degree :=
  ⟨value, fun request => polyBounded_const value (measureOf request) degree⟩

theorem Dominated.add {Request : Type} {left right measureOf : Request → ℕ}
    {degree : ℕ} (hleft : Dominated left measureOf degree)
    (hright : Dominated right measureOf degree) :
    Dominated (fun request => left request + right request) measureOf degree := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  exact ⟨leftCoefficient + rightCoefficient,
    fun request => (hleftBound request).add (hrightBound request)⟩

theorem Dominated.max {Request : Type} {left right measureOf : Request → ℕ}
    {degree : ℕ} (hleft : Dominated left measureOf degree)
    (hright : Dominated right measureOf degree) :
    Dominated (fun request => Max.max (left request) (right request)) measureOf
      degree := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  exact ⟨Max.max leftCoefficient rightCoefficient,
    fun request => (hleftBound request).max (hrightBound request)⟩

/-- The only degree-raising rule: a counted repetition. -/
theorem Dominated.mul {Request : Type} {left right measureOf : Request → ℕ}
    {leftDegree rightDegree : ℕ}
    (hleft : Dominated left measureOf leftDegree)
    (hright : Dominated right measureOf rightDegree) :
    Dominated (fun request => left request * right request) measureOf
      (leftDegree + rightDegree) := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  exact ⟨leftCoefficient * rightCoefficient,
    fun request => (hleftBound request).mul (hrightBound request)⟩

/-- Sequential composition.  The linked program stays implicit, so no composed
register span is ever named. -/
theorem Dominated.linkFuel {Request : Type} {second : NPOracleProgram}
    {first secondCharge measureOf : Request → ℕ} {degree : ℕ}
    (hfirst : Dominated first measureOf degree)
    (hsecond : Dominated secondCharge measureOf degree) :
    Dominated
      (fun request =>
        VerifiedLinker.linkFuel second (first request) (secondCharge request))
      measureOf degree := by
  obtain ⟨firstCoefficient, hfirstBound⟩ := hfirst
  obtain ⟨secondCoefficient, hsecondBound⟩ := hsecond
  exact ⟨programRegisterSpan second + 5 + firstCoefficient + secondCoefficient,
    fun request => linkFuel_polyBounded (hfirstBound request)
      (hsecondBound request)⟩

theorem Dominated.preserveRightFuel {Request : Type}
    {source measureOf : Request → ℕ} {degree : ℕ}
    (hsource : Dominated source measureOf degree) :
    Dominated
      (fun request => PreserveRightProgram.preserveRightFuel (source request))
      measureOf degree := by
  obtain ⟨coefficient, hbound⟩ := hsource
  exact ⟨coefficient + 4,
    fun request => preserveRightFuel_polyBounded (hbound request)⟩

theorem Dominated.taggedProgramChoiceFuel {Request : Type}
    {source measureOf : Request → ℕ} {degree : ℕ}
    (hsource : Dominated source measureOf degree) :
    Dominated
      (fun request =>
        TaggedProgramChoice.taggedProgramChoiceFuel (source request))
      measureOf degree := by
  obtain ⟨coefficient, hbound⟩ := hsource
  exact ⟨coefficient + 5,
    fun request => taggedProgramChoiceFuel_polyBounded (hbound request)⟩

/-! ### The width shapes -/

private theorem natBitLength_max_le (left right : ℕ) :
    natBitLength (max left right) ≤
      max (natBitLength left) (natBitLength right) := by
  rcases Nat.le_total left right with hle | hle
  · have hvalue : natBitLength (max left right) = natBitLength right := by
      congr 1
      omega
    omega
  · have hvalue : natBitLength (max left right) = natBitLength left := by
      congr 1
      omega
    omega

theorem Dominated.natBitLength_max {Request : Type}
    {left right measureOf : Request → ℕ} {degree : ℕ}
    (hleft : Dominated (fun request => natBitLength (left request)) measureOf
      degree)
    (hright : Dominated (fun request => natBitLength (right request)) measureOf
      degree) :
    Dominated
      (fun request => natBitLength (Max.max (left request) (right request)))
      measureOf degree :=
  (hleft.max hright).mono fun _ => natBitLength_max_le _ _

theorem Dominated.natBitLength_pair {Request : Type}
    {left right measureOf : Request → ℕ} {degree : ℕ}
    (hleft : Dominated (fun request => natBitLength (left request)) measureOf
      degree)
    (hright : Dominated (fun request => natBitLength (right request)) measureOf
      degree) :
    Dominated
      (fun request => natBitLength (Nat.pair (left request) (right request)))
      measureOf degree := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  refine ⟨2 * Max.max leftCoefficient rightCoefficient, fun request => ?_⟩
  have hmax := (hleftBound request).max (hrightBound request)
  exact (hmax.const_mul 2).mono (pairCodeBits_le _ _)

/-- Width of one linked stage. -/
theorem Dominated.occurrenceStageBits {Request : Type}
    {inputLength headBits tailBits measureOf : Request → ℕ} {degree : ℕ}
    (hlength : Dominated (fun request => natBitLength (inputLength request))
      measureOf degree)
    (hhead : Dominated headBits measureOf degree)
    (htail : Dominated tailBits measureOf degree) :
    Dominated
      (fun request =>
        CaseTwoOccurrenceProgram.occurrenceStageBits (inputLength request)
          (headBits request) (tailBits request))
      measureOf degree :=
  (hlength.max (hhead.max htail)).mono fun _ =>
    le_of_eq (by simp only [CaseTwoOccurrenceProgram.occurrenceStageBits])

/-- Width of one retained-context call. -/
theorem Dominated.preserveRightBits {Request : Type}
    {sourceBits left right output measureOf : Request → ℕ} {degree : ℕ}
    (hsource : Dominated sourceBits measureOf degree)
    (hentry : Dominated
      (fun request => natBitLength (Nat.pair (left request) (right request)))
      measureOf degree)
    (hexit : Dominated
      (fun request => natBitLength (Nat.pair (output request) (right request)))
      measureOf degree) :
    Dominated
      (fun request =>
        PreserveRightProgram.preserveRightBits (sourceBits request)
          (left request) (right request) (output request))
      measureOf degree :=
  (hsource.max (hentry.max hexit)).mono fun _ =>
    le_of_eq (by simp only [PreserveRightProgram.preserveRightBits])

/-! ### Entering the judgement from a magnitude bound -/

theorem polyBounded_succ_of_le {value measure : ℕ} (hle : value ≤ measure) :
    PolyBounded (value + 1) measure 1 1 := by
  unfold PolyBounded
  simp only [pow_one, Nat.one_mul]
  omega

/-- A charge below the measure is dominated at degree one. -/
theorem dominated_of_le_measure {Request : Type} {charge measureOf :
    Request → ℕ} (hle : ∀ request, charge request ≤ measureOf request) :
    Dominated charge measureOf 1 :=
  ⟨1, fun request =>
    (polyBounded_succ_of_le (hle request)).mono (by omega)⟩

/-- Binary width of a charge below the measure. -/
theorem dominated_natBitLength_of_le_measure {Request : Type}
    {value measureOf : Request → ℕ}
    (hle : ∀ request, value request ≤ measureOf request) :
    Dominated (fun request => natBitLength (value request)) measureOf 1 :=
  ⟨1, fun request =>
    (polyBounded_succ_of_le (hle request)).mono
      (ValidatorCompositeLeafBounds.natBitLength_le_succ (value request))⟩

/-- Binary width of an arbitrary dominated charge. -/
theorem Dominated.natBitLength {Request : Type} {value measureOf : Request → ℕ}
    {degree : ℕ} (h : Dominated value measureOf degree) :
    Dominated (fun request => natBitLength (value request)) measureOf
      (degree + 1) := by
  obtain ⟨coefficient, hbound⟩ := h
  refine ⟨coefficient + 1, fun request => ?_⟩
  refine ((hbound request).degree_mono (Nat.le_succ degree)).add
    (polyBounded_const 1 (measureOf request) (degree + 1)) |>.mono ?_
  exact ValidatorCompositeLeafBounds.natBitLength_le_succ (value request)

/-! ## 3. The three initial-width rows, closed outright

Rows 3, 6 and 9 of `PaddedRunnerBudget` are the presentation's own
`initialBitsFit` obligations.  They mention no runner at all: each is the binary
width of the request code, and every component of a request code is bounded by
the request's own measure. -/

theorem dominated_shapeInitialBits (clockDepth : ℕ) :
    Dominated (fun n : ℕ => natBitLength n) (shapeMeasure clockDepth) 1 :=
  dominated_natBitLength_of_le_measure fun n => by
    simp only [shapeMeasure]
    omega

theorem dominated_queryInitialBits :
    Dominated
      (fun request : ProjectionQueryRequest =>
        natBitLength
          (max (ProjectionQueryRequest.length request)
            (ProjectionQueryRequest.code request)))
      ProjectionQueryRequest.measure 1 := by
  have hlength :
      Dominated
        (fun request : ProjectionQueryRequest =>
          natBitLength (ProjectionQueryRequest.length request))
        ProjectionQueryRequest.measure 1 :=
    dominated_natBitLength_of_le_measure fun request => by
      simp only [ProjectionQueryRequest.length, ProjectionQueryRequest.measure]
      omega
  have hinput :
      Dominated
        (fun request : ProjectionQueryRequest =>
          natBitLength (encodeBitInput request.input))
        ProjectionQueryRequest.measure 1 :=
    ⟨1, fun request => by
      refine (polyBounded_succ_of_le (show request.inputArity ≤
        ProjectionQueryRequest.measure request by
          simp only [ProjectionQueryRequest.measure]; omega)).mono ?_
      exact natBitLength_encodeBitInput_le request.input⟩
  have hquery :
      Dominated
        (fun request : ProjectionQueryRequest =>
          natBitLength request.query.val)
        ProjectionQueryRequest.measure 1 :=
    dominated_natBitLength_of_le_measure fun request => by
      have hlt := request.query.isLt
      simp only [ProjectionQueryRequest.measure]
      omega
  have hbit :
      Dominated
        (fun request : ProjectionQueryRequest => natBitLength request.bit.val)
        ProjectionQueryRequest.measure 1 :=
    dominated_natBitLength_of_le_measure fun request => by
      have hlt := request.bit.isLt
      simp only [ProjectionQueryRequest.measure]
      omega
  have hcode :
      Dominated
        (fun request : ProjectionQueryRequest =>
          natBitLength (ProjectionQueryRequest.code request))
        ProjectionQueryRequest.measure 1 := by
    have hinner := hquery.natBitLength_pair hbit
    have hmiddle := hinput.natBitLength_pair hinner
    have houter := hlength.natBitLength_pair hmiddle
    exact houter
  exact hlength.natBitLength_max hcode

theorem dominated_decisionInitialBits :
    Dominated
      (fun request : ProjectionDecisionRequest =>
        natBitLength
          (max (ProjectionDecisionRequest.length request)
            (ProjectionDecisionRequest.code request)))
      ProjectionDecisionRequest.measure 1 := by
  have hlength :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (ProjectionDecisionRequest.length request))
        ProjectionDecisionRequest.measure 1 :=
    dominated_natBitLength_of_le_measure fun request => by
      simp only [ProjectionDecisionRequest.length,
        ProjectionDecisionRequest.measure]
      omega
  have hinput :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (encodeBitInput request.input))
        ProjectionDecisionRequest.measure 1 :=
    ⟨1, fun request => by
      refine (polyBounded_succ_of_le (show request.inputArity ≤
        ProjectionDecisionRequest.measure request by
          simp only [ProjectionDecisionRequest.measure]; omega)).mono ?_
      exact natBitLength_encodeBitInput_le request.input⟩
  have hrandomness :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (encodeBitInput request.randomness))
        ProjectionDecisionRequest.measure 1 :=
    ⟨1, fun request => by
      refine (polyBounded_succ_of_le (show request.width ≤
        ProjectionDecisionRequest.measure request by
          simp only [ProjectionDecisionRequest.measure]; omega)).mono ?_
      exact natBitLength_encodeBitInput_le request.randomness⟩
  have hcode :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (ProjectionDecisionRequest.code request))
        ProjectionDecisionRequest.measure 1 :=
    hlength.natBitLength_pair (hinput.natBitLength_pair hrandomness)
  exact hlength.natBitLength_max hcode

/-- **The source shape budget is its own envelope.**  `shape.budget` is
`polynomialBudget` at `shapeMeasure` by construction, so the domination
judgement holds at the runner's own published coefficient and degree. -/
theorem dominated_shapeBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) :
    Dominated (fun n => outer.pcp.shape.budget n) (shapeMeasure clockDepth)
      outer.pcp.shape.degree :=
  ⟨outer.pcp.shape.coefficient, fun _ => Nat.le_refl _⟩

/-- Scaling a dominated charge by a closed factor keeps the degree. -/
theorem Dominated.const_mul {Request : Type} {charge measureOf : Request → ℕ}
    {degree : ℕ} (factor : ℕ) (h : Dominated charge measureOf degree) :
    Dominated (fun request => factor * charge request) measureOf degree := by
  obtain ⟨coefficient, hbound⟩ := h
  exact ⟨factor * coefficient, fun request => (hbound request).const_mul factor⟩

/-! ## 5. The shape runner's fuel spine

`paddedShapeFuel` links three stages over two moving charges: the source shape
runner's own budget and the numeral bank's width-envelope charge.  Everything
else is a closed framing constant. -/

/-- **Row 2, reduced.**  The padded shape stream's clock is dominated as soon as
the numeral bank's width-envelope clock is: the only other moving charge is the
source shape runner's own budget, which §4 discharges. -/
theorem dominated_publishedPaddedShapeFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ)
    (hshapeBudget :
      Dominated (fun n => outer.pcp.shape.budget n) (shapeMeasure clockDepth)
        degree)
    (hwidthEnvelope :
      Dominated
        (fun n =>
          widthEnvelopeFuel clockDepth outer.pcp.shape.coefficient
            outer.proofExponent n)
        (shapeMeasure clockDepth) degree) :
    Dominated (fun n => publishedPaddedShapeFuel outer n)
      (shapeMeasure clockDepth) degree := by
  simp only [publishedPaddedShapeFuel, paddedShapeFuel]
  exact Dominated.linkFuel (dominated_const 2 degree)
    (Dominated.linkFuel hshapeBudget.preserveRightFuel
      (Dominated.linkFuel (dominated_const 5 degree)
        hwidthEnvelope.preserveRightFuel))

/-! ## 6. The decision runner's fuel spine

The padded decision stream is the source decision runner called on the *native
prefix* of the padded random string.  Its only non-obvious charge is the prefix
reducer's: `bitInputPrefixFuel` is exponential in the selected width.  The outer
PCP's published `proofSizeBound` is exactly the fact that converts it, since
`2 ^ nativeWidth n ≤ widthBudget outer n` and `widthBudget` is a published
source numeral. -/

/-- **The exponential prefix charge, converted.**  `bitInputPrefixFuel` is
exponential in the native width; `proofSizeBound` turns `2 ^ nativeWidth` into
the published width budget, so the charge is dominated as soon as the width
envelope and the width budget are. -/
theorem dominated_prefixFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ)
    (hwidthEnvelope :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          widthEnvelope outer request.inputArity)
        ProjectionDecisionRequest.measure degree)
    (hwidthBudget :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          widthBudget outer request.inputArity)
        ProjectionDecisionRequest.measure degree) :
    Dominated
      (fun request : ProjectionDecisionRequest =>
        bitInputPrefixFuel (outer.pcp.nativeWidth request.inputArity)
          (encodeBitInput request.randomness))
      ProjectionDecisionRequest.measure (degree + degree) := by
  have hfactor :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          7 + 3 * widthBudget outer request.inputArity)
        ProjectionDecisionRequest.measure degree :=
    (dominated_const 7 degree).add (hwidthBudget.const_mul 3)
  have hproduct := hwidthEnvelope.mul hfactor
  refine ((dominated_const 6 (degree + degree)).add hproduct).mono ?_
  intro request
  have hcharge :=
    bitInputPrefixFuel_le (outer.pcp.nativeWidth request.inputArity)
      (encodeBitInput request.randomness)
  have hwidth :=
    nativeWidth_le_widthEnvelope outer request.inputArity
  have hpower :
      2 ^ outer.pcp.nativeWidth request.inputArity ≤
        widthBudget outer request.inputArity :=
    outer.proofSizeBound request.inputArity
  have hinner :
      7 + 3 * 2 ^ outer.pcp.nativeWidth request.inputArity ≤
        7 + 3 * widthBudget outer request.inputArity := by omega
  have hscaled :
      outer.pcp.nativeWidth request.inputArity *
          (7 + 3 * 2 ^ outer.pcp.nativeWidth request.inputArity) ≤
        widthEnvelope outer request.inputArity *
          (7 + 3 * widthBudget outer request.inputArity) :=
    Nat.mul_le_mul hwidth hinner
  omega

/-- **Row 8, reduced.**  The padded decision stream's clock is dominated by the
source shape budget, the source decision budget and the converted prefix
charge. -/
theorem dominated_publishedPaddedDecisionFuel {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ)
    (hshapeBudget :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          outer.pcp.shape.budget request.inputArity)
        ProjectionDecisionRequest.measure degree)
    (hdecisionBudget :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          decisionBudget outer.pcp request.inputArity)
        ProjectionDecisionRequest.measure degree)
    (hprefix :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          bitInputPrefixFuel (outer.pcp.nativeWidth request.inputArity)
            (encodeBitInput request.randomness))
        ProjectionDecisionRequest.measure degree) :
    Dominated (fun request => publishedPaddedDecisionFuel outer request)
      ProjectionDecisionRequest.measure degree := by
  simp only [publishedPaddedDecisionFuel, paddedDecisionFuel]
  exact Dominated.linkFuel hshapeBudget.preserveRightFuel
    (Dominated.linkFuel (dominated_const 8 degree)
      (Dominated.linkFuel hprefix.preserveRightFuel
        (Dominated.linkFuel (dominated_const 6 degree) hdecisionBudget)))

/-! ## 7. The ten rows

Six moving charges and the three initial-width rows of §3 close
`PaddedRunnerBudget`.  The coefficient is produced rather than declared: it is
the sum of the nine witnesses, and it mentions the composed register spans the
linkers contribute, so it must never be written into a statement. -/

/-- **The padded runners' budget, assembled.**  The six runner charges are the
whole residue: the three `initialBitsFit` rows are closed in §3, and the
coefficient is produced by the walk.  `§5` and `§6` reduce the shape-fuel and
decision-fuel premises further, to published source numerals. -/
theorem exists_paddedRunnerBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ)
    (hshapeBits :
      Dominated (fun n => publishedPaddedShapeBits outer n)
        (shapeMeasure clockDepth) degree)
    (hshapeFuel :
      Dominated (fun n => publishedPaddedShapeFuel outer n)
        (shapeMeasure clockDepth) degree)
    (hqueryBits :
      Dominated (fun request => publishedPaddedQueryBits outer request)
        ProjectionQueryRequest.measure degree)
    (hqueryFuel :
      Dominated (fun request => publishedPaddedQueryFuel outer request)
        ProjectionQueryRequest.measure degree)
    (hdecisionBits :
      Dominated (fun request => publishedPaddedDecisionBits outer request)
        ProjectionDecisionRequest.measure degree)
    (hdecisionFuel :
      Dominated (fun request => publishedPaddedDecisionFuel outer request)
        ProjectionDecisionRequest.measure degree) :
    ∃ coefficient, 0 < coefficient ∧
      PaddedRunnerBudget outer coefficient (degree + 1) := by
  have hstep : degree ≤ degree + 1 := Nat.le_succ degree
  have hinitial : 1 ≤ degree + 1 := by omega
  obtain ⟨shapeBitsCoefficient, hshapeBitsBound⟩ := hshapeBits.degree_mono hstep
  obtain ⟨shapeFuelCoefficient, hshapeFuelBound⟩ := hshapeFuel.degree_mono hstep
  obtain ⟨queryBitsCoefficient, hqueryBitsBound⟩ := hqueryBits.degree_mono hstep
  obtain ⟨queryFuelCoefficient, hqueryFuelBound⟩ := hqueryFuel.degree_mono hstep
  obtain ⟨decisionBitsCoefficient, hdecisionBitsBound⟩ :=
    hdecisionBits.degree_mono hstep
  obtain ⟨decisionFuelCoefficient, hdecisionFuelBound⟩ :=
    hdecisionFuel.degree_mono hstep
  obtain ⟨shapeInitialCoefficient, hshapeInitialBound⟩ :=
    (dominated_shapeInitialBits clockDepth).degree_mono hinitial
  obtain ⟨queryInitialCoefficient, hqueryInitialBound⟩ :=
    dominated_queryInitialBits.degree_mono hinitial
  obtain ⟨decisionInitialCoefficient, hdecisionInitialBound⟩ :=
    dominated_decisionInitialBits.degree_mono hinitial
  refine
    ⟨shapeBitsCoefficient + shapeFuelCoefficient + queryBitsCoefficient +
      queryFuelCoefficient + decisionBitsCoefficient + decisionFuelCoefficient +
      shapeInitialCoefficient + queryInitialCoefficient +
      decisionInitialCoefficient + 1, by omega, ?_⟩
  refine ⟨by omega, fun n => ?_, fun n => ?_, fun n => ?_, fun request => ?_,
    fun request => ?_, fun request => ?_, fun request => ?_, fun request => ?_,
    fun request => ?_⟩
  · exact ((hshapeBitsBound n).coefficient_mono (by omega)).le_polynomialBudget
  · exact ((hshapeFuelBound n).coefficient_mono (by omega)).le_polynomialBudget
  · exact
      ((hshapeInitialBound n).coefficient_mono (by omega)).le_polynomialBudget
  · exact
      ((hqueryBitsBound request).coefficient_mono (by omega)).le_polynomialBudget
  · exact
      ((hqueryFuelBound request).coefficient_mono (by omega)).le_polynomialBudget
  · exact
      ((hqueryInitialBound request).coefficient_mono
        (by omega)).le_polynomialBudget
  · exact
      ((hdecisionBitsBound request).coefficient_mono
        (by omega)).le_polynomialBudget
  · exact
      ((hdecisionFuelBound request).coefficient_mono
        (by omega)).le_polynomialBudget
  · exact
      ((hdecisionInitialBound request).coefficient_mono
        (by omega)).le_polynomialBudget

/-! ## 8. The capstone

With the budget produced, the padded projection PCP is *fully* discharged:
existence, presentation and budget.  This eliminates the
`PaddedProjectionPresentation.PresentsPaddedOuterPCP` premise of
`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` outright. -/

/-- **The padded presentation, from six runner charges.**  No budget numeral is
declared: the six domination judgements produce it. -/
theorem exists_presentsPaddedOuterPCP_of_dominated {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ)
    (hshapeBits :
      Dominated (fun n => publishedPaddedShapeBits outer n)
        (shapeMeasure clockDepth) degree)
    (hshapeFuel :
      Dominated (fun n => publishedPaddedShapeFuel outer n)
        (shapeMeasure clockDepth) degree)
    (hqueryBits :
      Dominated (fun request => publishedPaddedQueryBits outer request)
        ProjectionQueryRequest.measure degree)
    (hqueryFuel :
      Dominated (fun request => publishedPaddedQueryFuel outer request)
        ProjectionQueryRequest.measure degree)
    (hdecisionBits :
      Dominated (fun request => publishedPaddedDecisionBits outer request)
        ProjectionDecisionRequest.measure degree)
    (hdecisionFuel :
      Dominated (fun request => publishedPaddedDecisionFuel outer request)
        ProjectionDecisionRequest.measure degree) :
    ∃ pcp :
        ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth),
      PresentsPaddedOuterPCP outer pcp := by
  obtain ⟨coefficient, hpositive, hbudget⟩ :=
    exists_paddedRunnerBudget outer degree hshapeBits hshapeFuel hqueryBits
      hqueryFuel hdecisionBits hdecisionFuel
  exact exists_presentsPaddedOuterPCP outer coefficient (degree + 1) hbudget

/-- **`bodyRun` from the padded runners' charges.**  The presentation premise of
`inverse_bodyRun_ofPresentation` is now a consequence of six domination
judgements about closed cost functions: no existential, no callback and no
declared budget numeral survives on the padded-PCP side. -/
theorem inverse_bodyRun_of_publishedDomination (contracts : PublishedContracts)
    (clockDepth degree : ℕ)
    (hshapeBits :
      Dominated
        (fun n =>
          publishedPaddedShapeBits (publishedHierarchyOuterPCP contracts
            clockDepth) n)
        (shapeMeasure clockDepth) degree)
    (hshapeFuel :
      Dominated
        (fun n =>
          publishedPaddedShapeFuel (publishedHierarchyOuterPCP contracts
            clockDepth) n)
        (shapeMeasure clockDepth) degree)
    (hqueryBits :
      Dominated
        (fun request =>
          publishedPaddedQueryBits (publishedHierarchyOuterPCP contracts
            clockDepth) request)
        ProjectionQueryRequest.measure degree)
    (hqueryFuel :
      Dominated
        (fun request =>
          publishedPaddedQueryFuel (publishedHierarchyOuterPCP contracts
            clockDepth) request)
        ProjectionQueryRequest.measure degree)
    (hdecisionBits :
      Dominated
        (fun request =>
          publishedPaddedDecisionBits (publishedHierarchyOuterPCP contracts
            clockDepth) request)
        ProjectionDecisionRequest.measure degree)
    (hdecisionFuel :
      Dominated
        (fun request =>
          publishedPaddedDecisionFuel (publishedHierarchyOuterPCP contracts
            clockDepth) request)
        ProjectionDecisionRequest.measure degree) :
    ∃ pcp :
        ExecutableProjectionPCP
          (publishedRefuterSource contracts clockDepth).hierarchyMachine
          (pairClock clockDepth),
      PresentsPaddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)
        pcp :=
  exists_presentsPaddedOuterPCP_of_dominated
    (publishedHierarchyOuterPCP contracts clockDepth) degree hshapeBits
    hshapeFuel hqueryBits hqueryFuel hdecisionBits hdecisionFuel

/-! ## 9. The two width spines

The width ledgers are pure maxima: no linker widens a register beyond the widest
stage it joins.  Both walks therefore run on `Dominated.occurrenceStageBits` and
`Dominated.preserveRightBits`, and both bottom out in the *published* runner
budgets plus one bank charge each. -/

/-- The published shape code's own width is paid for by the source shape
runner's declared budget: a halting bounded run never writes a register wider
than the run's own charge. -/
theorem natBitLength_shapeExecute_le_budget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) :
    natBitLength (outer.pcp.shape.execute n) ≤ outer.pcp.shape.budget n :=
  run_output_bounded (outer.pcp.shape.run_eq_execute n)

/-- **Row 7, reduced.**  The padded decision stream's register width is
dominated by the two source runner budgets and the prefix reducer's own two
charges. -/
theorem dominated_publishedPaddedDecisionBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ) (hdegree : 1 ≤ degree)
    (hshapeBudget :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          outer.pcp.shape.budget request.inputArity)
        ProjectionDecisionRequest.measure degree)
    (hdecisionBudget :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          decisionBudget outer.pcp request.inputArity)
        ProjectionDecisionRequest.measure degree)
    (hprefixBits :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          bitInputPrefixBits
            (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1
            (encodeBitInput request.randomness))
        ProjectionDecisionRequest.measure degree)
    (hprefixValue :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength
            (bitInputPrefix
              (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1
              (encodeBitInput request.randomness)))
        ProjectionDecisionRequest.measure degree) :
    Dominated (fun request => publishedPaddedDecisionBits outer request)
      ProjectionDecisionRequest.measure degree := by
  have hlength :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength request.inputArity)
        ProjectionDecisionRequest.measure degree :=
    (dominated_natBitLength_of_le_measure
      (fun request : ProjectionDecisionRequest => by
        simp only [ProjectionDecisionRequest.measure]
        omega)).degree_mono hdegree
  have hinput :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (encodeBitInput request.input))
        ProjectionDecisionRequest.measure degree :=
    Dominated.degree_mono
      ⟨1, fun request => by
        refine (polyBounded_succ_of_le (show request.inputArity ≤
          ProjectionDecisionRequest.measure request by
            simp only [ProjectionDecisionRequest.measure]; omega)).mono ?_
        exact natBitLength_encodeBitInput_le request.input⟩ hdegree
  have hrandomness :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (encodeBitInput request.randomness))
        ProjectionDecisionRequest.measure degree :=
    Dominated.degree_mono
      ⟨1, fun request => by
        refine (polyBounded_succ_of_le (show request.width ≤
          ProjectionDecisionRequest.measure request by
            simp only [ProjectionDecisionRequest.measure]; omega)).mono ?_
        exact natBitLength_encodeBitInput_le request.randomness⟩ hdegree
  have hshapeCode :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength (outer.pcp.shape.execute request.inputArity))
        ProjectionDecisionRequest.measure degree :=
    hshapeBudget.mono fun request =>
      natBitLength_shapeExecute_le_budget outer request.inputArity
  have hwidth :
      Dominated
        (fun request : ProjectionDecisionRequest =>
          natBitLength
            (Nat.unpair (outer.pcp.shape.execute request.inputArity)).1)
        ProjectionDecisionRequest.measure degree :=
    hshapeCode.mono fun request =>
      natBitLength_mono
        (Nat.unpair_left_le (outer.pcp.shape.execute request.inputArity))
  have hretained := hinput.natBitLength_pair hrandomness
  have hentry := hlength.natBitLength_pair hretained
  have hexit := hshapeCode.natBitLength_pair hretained
  have hcall := hwidth.natBitLength_pair hrandomness
  have hprefixEntry := hcall.natBitLength_pair hinput
  have hprefixExit := hprefixValue.natBitLength_pair hinput
  have hframe := hexit.natBitLength_max hprefixEntry
  have hcallEntry := hprefixValue.natBitLength_pair hinput
  have hcallExit :=
    hlength.natBitLength_pair (hinput.natBitLength_pair hprefixValue)
  have hcallFrame := hcallEntry.natBitLength_max hcallExit
  simp only [publishedPaddedDecisionBits, paddedDecisionBits, prefixFrameBits,
    PaddedProjectionDecisionRunner.callFrameBits, decisionCode,
    bitInputPrefixInput]
  exact Dominated.occurrenceStageBits hlength
    (Dominated.preserveRightBits hshapeBudget hentry hexit)
    (Dominated.occurrenceStageBits hlength hframe
      (Dominated.occurrenceStageBits hlength
        (Dominated.preserveRightBits hprefixBits hprefixEntry hprefixExit)
        (Dominated.occurrenceStageBits hlength hcallFrame hdecisionBudget)))

/-- **Row 1, reduced.**  The padded shape stream's register width is dominated
by the source shape budget and the numeral bank's two width-envelope charges. -/
theorem dominated_publishedPaddedShapeBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (degree : ℕ) (hdegree : 1 ≤ degree)
    (hshapeBudget :
      Dominated (fun n => outer.pcp.shape.budget n) (shapeMeasure clockDepth)
        degree)
    (hwidthEnvelopeBits :
      Dominated
        (fun n =>
          widthEnvelopeBits n clockDepth outer.pcp.shape.coefficient
            outer.proofExponent n)
        (shapeMeasure clockDepth) degree)
    (hwidthValue :
      Dominated
        (fun n =>
          natBitLength
            (widthValue clockDepth outer.pcp.shape.coefficient
              outer.proofExponent n))
        (shapeMeasure clockDepth) degree) :
    Dominated (fun n => publishedPaddedShapeBits outer n)
      (shapeMeasure clockDepth) degree := by
  have hlength :
      Dominated (fun n : ℕ => natBitLength n) (shapeMeasure clockDepth)
        degree :=
    (dominated_shapeInitialBits clockDepth).degree_mono hdegree
  have hshapeCode :
      Dominated (fun n : ℕ => natBitLength (outer.pcp.shape.execute n))
        (shapeMeasure clockDepth) degree :=
    hshapeBudget.mono fun n => natBitLength_shapeExecute_le_budget outer n
  have hcount :
      Dominated
        (fun n : ℕ =>
          natBitLength (Nat.unpair (outer.pcp.shape.execute n)).2)
        (shapeMeasure clockDepth) degree :=
    hshapeCode.mono fun n =>
      natBitLength_mono (Nat.unpair_right_le (outer.pcp.shape.execute n))
  have hduplicate := hlength.natBitLength_pair hlength
  have hshapeExit := hshapeCode.natBitLength_pair hlength
  have hreframeExit := hlength.natBitLength_pair hcount
  have hreframe := hshapeExit.natBitLength_max hreframeExit
  have hwidthEntry := hlength.natBitLength_pair hcount
  have hwidthExit := hwidthValue.natBitLength_pair hcount
  simp only [publishedPaddedShapeBits, paddedShapeBits, reframeBits]
  exact Dominated.occurrenceStageBits hlength hduplicate
    (Dominated.occurrenceStageBits hlength
      (Dominated.preserveRightBits hshapeBudget hduplicate hshapeExit)
      (Dominated.occurrenceStageBits hlength hreframe
        (Dominated.preserveRightBits hwidthEnvelopeBits hwidthEntry
          hwidthExit)))

def SourceQueryAnswerBounded {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (bound : ℕ → ℕ) : Prop :=
  ∀ n encodedInput queryIndex bitIndex,
    queryExecuteAt outer.pcp n encodedInput queryIndex bitIndex ≤ bound n

end NearCubicWires.PaddedRunnerBudgetDomination
