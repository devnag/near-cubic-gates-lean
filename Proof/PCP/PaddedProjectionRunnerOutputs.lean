import Proof.MachineModel.BitInputPrefixProgram
import Proof.PCP.PaddedProjectionPresentation

namespace NearCubicWires.PaddedProjectionRunnerOutputs

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The charged budgets and request codes, on raw numerals -/

/-- The measure both request-level runners are charged at.  It depends on the
public length alone, so a caller can compute the callee's budget without
rebuilding the callee's request record. -/
def nativeMeasure {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) : ℕ :=
  n + pcp.nativeWidth n + pcp.queryCount n

/-- The query runner's own budget at one public length. -/
def queryBudget {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) : ℕ :=
  polynomialBudget pcp.query.coefficient pcp.query.degree (nativeMeasure pcp n)

/-- The decision runner's own budget at one public length. -/
def decisionBudget {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) : ℕ :=
  polynomialBudget pcp.decisionRunner.coefficient pcp.decisionRunner.degree
    (nativeMeasure pcp n)

/-- The query runner's request code, assembled from raw numerals. -/
def queryCode (n encodedInput queryIndex bitIndex : ℕ) : ℕ :=
  Nat.pair n (Nat.pair encodedInput (Nat.pair queryIndex bitIndex))

/-- The decision runner's request code, assembled from raw numerals. -/
def decisionCode (n encodedInput encodedRandomness : ℕ) : ℕ :=
  Nat.pair n (Nat.pair encodedInput encodedRandomness)

/-- The query runner, executed at its own budget on a raw request code. -/
def queryExecuteAt {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (n encodedInput queryIndex bitIndex : ℕ) : ℕ :=
  (runNPOracleProgram pcp.query.program (queryBudget pcp n) (queryBudget pcp n)
      (initialNPOracleState n
        (queryCode n encodedInput queryIndex bitIndex))).getD 0

/-- The decision runner, executed at its own budget on a raw request code. -/
def decisionExecuteAt {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (n encodedInput encodedRandomness : ℕ) : ℕ :=
  (runNPOracleProgram pcp.decisionRunner.program (decisionBudget pcp n)
      (decisionBudget pcp n)
      (initialNPOracleState n
        (decisionCode n encodedInput encodedRandomness))).getD 0

/-- The raw query execution is the published runner's own `execute`. -/
theorem queryExecuteAt_eq {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    queryExecuteAt pcp n (encodeBitInput input) query.val bit.val =
      pcp.query.execute (pcp.queryRequest input query bit) := rfl

/-- The raw decision execution is the published runner's own `execute`. -/
theorem decisionExecuteAt_eq {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    {n : ℕ} (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    decisionExecuteAt pcp n (encodeBitInput input) (encodeBitInput randomness) =
      pcp.decisionRunner.execute (pcp.decisionRequest input randomness) := rfl

/-! ## 2. The three padded outputs -/

/-- The padded shape output: the source-only width envelope beside the
published query count. -/
def paddedShapeOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n : ℕ) : ℕ :=
  Nat.pair (widthEnvelope outer n) (outer.pcp.queryCount n)

def paddedQueryModulus {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (n tag : ℕ) : ℕ :=
  if tag % 3 = 2 then 2 else outer.pcp.nativeWidth n

/-- The padded query output.  The guard is the saturating product
`(queryCount - query) * (nativeWidth - bit)`: it vanishes exactly on the
requests the source query runner is not obliged to answer — every padding
address, and every query index beyond the published count — and those are
emitted as the canonical false constant. -/
def paddedQueryOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (n encodedInput queryIndex bitIndex : ℕ) : ℕ :=
  if (outer.pcp.queryCount n - queryIndex) *
      (outer.pcp.nativeWidth n - bitIndex) = 0 then
    Nat.pair 2 0
  else
    Nat.pair
      ((Nat.unpair
        (queryExecuteAt outer.pcp n encodedInput queryIndex bitIndex)).1 % 3)
      ((Nat.unpair
          (queryExecuteAt outer.pcp n encodedInput queryIndex bitIndex)).2 %
        paddedQueryModulus outer n
          (Nat.unpair
            (queryExecuteAt outer.pcp n encodedInput queryIndex bitIndex)).1)

/-- The padded decision output: the native decision runner on the native prefix
of the padded random string. -/
def paddedDecisionOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (n encodedInput encodedRandomness : ℕ) : ℕ :=
  decisionExecuteAt outer.pcp n encodedInput
    (bitInputPrefix (outer.pcp.nativeWidth n) encodedRandomness)

/-! ## 3. The two decode identities -/

private theorem decodeProjectedRandomBit_of_pos {width : ℕ} (code : ℕ)
    (hwidth : 0 < width) :
    decodeProjectedRandomBit width code =
      if (Nat.unpair code).1 % 3 = 0 then
        .bit ⟨(Nat.unpair code).2 % width, Nat.mod_lt _ hwidth⟩
      else if (Nat.unpair code).1 % 3 = 1 then
        .negatedBit ⟨(Nat.unpair code).2 % width, Nat.mod_lt _ hwidth⟩
      else
        .constant ((Nat.unpair code).2.testBit 0) := by
  unfold decodeProjectedRandomBit
  rw [dif_neg (by omega : ¬width = 0)]

private theorem decodeProjectedRandomBit_pair_two_zero (width : ℕ) :
    decodeProjectedRandomBit width (Nat.pair 2 0) =
      ProjectedRandomBit.constant false := by
  unfold decodeProjectedRandomBit
  by_cases hwidth : width = 0
  · rw [dif_pos hwidth]
    simp
  · rw [dif_neg hwidth]
    simp

/-- **The re-tagging is correct.**  Reducing the decoded index modulo the
native width — and passing a constant tag's index through — is exactly what the
padded decode needs in order to reproduce the lifted native projection. -/
private theorem decode_retagged (native padded code : ℕ)
    (hpositive : 0 < native) (hle : native ≤ padded) :
    decodeProjectedRandomBit padded
        (Nat.pair ((Nat.unpair code).1 % 3)
          ((Nat.unpair code).2 %
            (if (Nat.unpair code).1 % 3 = 2 then 2 else native))) =
      liftProjectedRandomBit hle (decodeProjectedRandomBit native code) := by
  have hpadded : 0 < padded := lt_of_lt_of_le hpositive hle
  have hindex : (Nat.unpair code).2 % native < padded :=
    lt_of_lt_of_le (Nat.mod_lt _ hpositive) hle
  have hstable : (Nat.unpair code).2 % native % padded =
      (Nat.unpair code).2 % native := Nat.mod_eq_of_lt hindex
  rw [decodeProjectedRandomBit_of_pos code hpositive]
  have htag : (Nat.unpair code).1 % 3 = 0 ∨ (Nat.unpair code).1 % 3 = 1 ∨
      (Nat.unpair code).1 % 3 = 2 := by omega
  rcases htag with htag | htag | htag
  · rw [if_neg (by omega), if_pos htag, htag]
    rw [decodeProjectedRandomBit_of_pos _ hpadded]
    simp only [Nat.unpair_pair, hstable]
    rfl
  · rw [if_neg (by omega), if_neg (by omega), if_pos htag, htag]
    rw [decodeProjectedRandomBit_of_pos _ hpadded]
    simp only [Nat.unpair_pair, hstable]
    rfl
  · rw [if_pos htag, if_neg (by omega), if_neg (by omega), htag]
    rw [decodeProjectedRandomBit_of_pos _ hpadded]
    have hmod : (Nat.unpair code).2 % 2 % 2 = (Nat.unpair code).2 % 2 := by
      omega
    have hlow : ((Nat.unpair code).2 % 2).testBit 0 =
        (Nat.unpair code).2.testBit 0 := by
      simp only [Nat.testBit_zero, hmod]
    simp only [Nat.unpair_pair, hlow]
    rfl

/-- The padded PCP's address bits, written as one conditional on the native
width. -/
private theorem paddedOuterPCP_queryAddressBits {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) {n : ℕ} (input : BitInput n)
    (query : Fin (outer.pcp.queryCount n))
    (bit : Fin (widthEnvelope outer n)) :
    (paddedOuterPCP outer).queryAddressBits input query bit =
      if hbit : bit.val < outer.pcp.nativeWidth n then
        liftProjectedRandomBit (nativeWidth_le_widthEnvelope outer n)
          (outer.pcp.queryAddressBits input query ⟨bit.val, hbit⟩)
      else
        ProjectedRandomBit.constant false := rfl

/-- **The padded query output decodes to the padded projection.** -/
theorem decode_paddedQueryOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) {n : ℕ} (input : BitInput n)
    (query : Fin (outer.pcp.queryCount n))
    (bit : Fin (widthEnvelope outer n)) :
    decodeProjectedRandomBit (widthEnvelope outer n)
        (paddedQueryOutput outer n (encodeBitInput input) query.val bit.val) =
      (paddedOuterPCP outer).queryAddressBits input query bit := by
  rw [paddedOuterPCP_queryAddressBits outer input query bit]
  unfold paddedQueryOutput paddedQueryModulus
  have hquery : query.val < outer.pcp.queryCount n := query.isLt
  by_cases hbit : bit.val < outer.pcp.nativeWidth n
  · rw [if_neg (by
      refine Nat.mul_ne_zero ?_ ?_ <;> omega), dif_pos hbit]
    rw [queryExecuteAt_eq outer.pcp input query ⟨bit.val, hbit⟩]
    exact decode_retagged _ _ _ (by omega)
      (nativeWidth_le_widthEnvelope outer n)
  · rw [if_pos (by
      have hzero : outer.pcp.nativeWidth n - bit.val = 0 := by omega
      rw [hzero, Nat.mul_zero]), dif_neg hbit]
    exact decodeProjectedRandomBit_pair_two_zero _

/-- **The padded decision output is the native decision on the native
prefix.**  This is the bit-arithmetic half of the padding: the canonical code
of `prefixBits` is the canonical code of the padded string reduced modulo the
native width. -/
theorem paddedDecisionOutput_eq {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) {n : ℕ} (input : BitInput n)
    (randomness : BitInput (widthEnvelope outer n)) :
    paddedDecisionOutput outer n (encodeBitInput input)
        (encodeBitInput randomness) =
      outer.pcp.decisionRunner.execute
        (outer.pcp.decisionRequest input
          (prefixBits (nativeWidth_le_widthEnvelope outer n) randomness)) := by
  unfold paddedDecisionOutput
  rw [show bitInputPrefix (outer.pcp.nativeWidth n) (encodeBitInput randomness) =
      encodeBitInput
        (prefixBits (nativeWidth_le_widthEnvelope outer n) randomness) from
    bitInputPrefix_encodeBitInput randomness
      (nativeWidth_le_widthEnvelope outer n)]
  exact decisionExecuteAt_eq outer.pcp input _

/-! ## 4. The presentation, from the three outputs -/

private theorem decodeProjectedRandomBit_heq
    {leftWidth rightWidth leftCode rightCode : ℕ}
    (hwidth : leftWidth = rightWidth) (hcode : leftCode = rightCode) :
    HEq (decodeProjectedRandomBit leftWidth leftCode)
      (decodeProjectedRandomBit rightWidth rightCode) := by
  subst hwidth
  subst hcode
  rfl

private theorem decodeThreeCNF_heq
    {leftCount rightCount leftCode rightCode : ℕ}
    (hcount : leftCount = rightCount) (hcode : leftCode = rightCode) :
    HEq (decodeThreeCNF leftCount leftCode)
      (decodeThreeCNF rightCount rightCode) := by
  subst hcount
  subst hcode
  rfl

private theorem encodeBitInput_heq {leftWidth rightWidth : ℕ}
    {left : BitInput leftWidth} {right : BitInput rightWidth}
    (hwidth : leftWidth = rightWidth) (hbits : HEq left right) :
    encodeBitInput left = encodeBitInput right := by
  subst hwidth
  rw [eq_of_heq hbits]

/-- Substitution lemma for the address-bit field.  The pointwise hypothesis
mentions only `Fin.val` equalities, so neither width equation appears inside a
hypothesis that the substitution has to transport. -/
private theorem queryAddressBits_heq
    {leftWidth rightWidth leftCount rightCount : ℕ → ℕ}
    (hwidth : leftWidth = rightWidth) (hcount : leftCount = rightCount)
    (left : {n : ℕ} → BitInput n → Fin (leftCount n) → Fin (leftWidth n) →
      ProjectedRandomBit (leftWidth n))
    (right : {n : ℕ} → BitInput n → Fin (rightCount n) → Fin (rightWidth n) →
      ProjectedRandomBit (rightWidth n))
    (hpointwise : ∀ (n : ℕ) (input : BitInput n)
        (leftQuery : Fin (leftCount n)) (rightQuery : Fin (rightCount n))
        (leftBit : Fin (leftWidth n)) (rightBit : Fin (rightWidth n)),
        leftQuery.val = rightQuery.val → leftBit.val = rightBit.val →
        HEq (left input leftQuery leftBit) (right input rightQuery rightBit)) :
    HEq
      (α := {n : ℕ} → BitInput n → Fin (leftCount n) → Fin (leftWidth n) →
        ProjectedRandomBit (leftWidth n))
      (β := {n : ℕ} → BitInput n → Fin (rightCount n) → Fin (rightWidth n) →
        ProjectedRandomBit (rightWidth n))
      left right := by
  subst hwidth
  subst hcount
  apply heq_of_eq
  funext n input query bit
  exact eq_of_heq (hpointwise n input query query bit bit rfl rfl)

/-- Substitution lemma for the decision field. -/
private theorem decision_heq
    {leftWidth rightWidth leftCount rightCount : ℕ → ℕ}
    (hwidth : leftWidth = rightWidth) (hcount : leftCount = rightCount)
    (left : {n : ℕ} → BitInput n → BitInput (leftWidth n) →
      ThreeCNF (leftCount n))
    (right : {n : ℕ} → BitInput n → BitInput (rightWidth n) →
      ThreeCNF (rightCount n))
    (hpointwise : ∀ (n : ℕ) (input : BitInput n)
        (leftRandomness : BitInput (leftWidth n))
        (rightRandomness : BitInput (rightWidth n)),
        HEq leftRandomness rightRandomness →
        HEq (left input leftRandomness) (right input rightRandomness)) :
    HEq
      (α := {n : ℕ} → BitInput n → BitInput (leftWidth n) →
        ThreeCNF (leftCount n))
      (β := {n : ℕ} → BitInput n → BitInput (rightWidth n) →
        ThreeCNF (rightCount n))
      left right := by
  subst hwidth
  subst hcount
  apply heq_of_eq
  funext n input randomness
  exact eq_of_heq (hpointwise n input randomness randomness HEq.rfl)

theorem presentsPaddedOuterPCP_of_executes {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth))
    (hshape : ∀ n, pcp.shape.execute n = paddedShapeOutput outer n)
    (hquery : ∀ (n : ℕ) (input : BitInput n) (query : Fin (pcp.queryCount n))
        (bit : Fin (pcp.nativeWidth n)),
      pcp.query.execute (pcp.queryRequest input query bit) =
        paddedQueryOutput outer n (encodeBitInput input) query.val bit.val)
    (hdecision : ∀ (n : ℕ) (input : BitInput n)
        (randomness : BitInput (pcp.nativeWidth n)),
      pcp.decisionRunner.execute (pcp.decisionRequest input randomness) =
        paddedDecisionOutput outer n (encodeBitInput input)
          (encodeBitInput randomness)) :
    PresentsPaddedOuterPCP outer pcp := by
  have hwidth : pcp.nativeWidth = widthEnvelope outer := by
    funext n
    have hcode : (Nat.unpair (pcp.shape.execute n)).1 = widthEnvelope outer n := by
      rw [hshape n]
      simp [paddedShapeOutput]
    exact hcode
  have hcount : pcp.queryCount = outer.pcp.queryCount := by
    funext n
    have hcode :
        (Nat.unpair (pcp.shape.execute n)).2 = outer.pcp.queryCount n := by
      rw [hshape n]
      simp [paddedShapeOutput]
    exact hcode
  refine presentsPaddedOuterPCP_of_fields outer pcp hwidth hcount ?_ ?_
  · refine queryAddressBits_heq hwidth hcount _ _ ?_
    intro n input leftQuery rightQuery leftBit rightBit hqueryVal hbitVal
    have hleft :
        pcp.queryAddressBits input leftQuery leftBit =
          decodeProjectedRandomBit (pcp.nativeWidth n)
            (paddedQueryOutput outer n (encodeBitInput input) leftQuery.val
              leftBit.val) :=
      congrArg (decodeProjectedRandomBit (pcp.nativeWidth n))
        (hquery n input leftQuery leftBit)
    have hright :
        (paddedOuterPCP outer).queryAddressBits input rightQuery rightBit =
          decodeProjectedRandomBit (widthEnvelope outer n)
            (paddedQueryOutput outer n (encodeBitInput input) rightQuery.val
              rightBit.val) :=
      (decode_paddedQueryOutput outer input rightQuery rightBit).symm
    refine HEq.trans (heq_of_eq hleft) ?_
    rw [hright]
    exact decodeProjectedRandomBit_heq (congrFun hwidth n)
      (by rw [hqueryVal, hbitVal])
  · refine decision_heq hwidth hcount _ _ ?_
    intro n input leftRandomness rightRandomness hrandomness
    have hleft :
        pcp.decision input leftRandomness =
          decodeThreeCNF (pcp.queryCount n)
            (paddedDecisionOutput outer n (encodeBitInput input)
              (encodeBitInput leftRandomness)) :=
      congrArg (decodeThreeCNF (pcp.queryCount n))
        (hdecision n input leftRandomness)
    have hcode :
        paddedDecisionOutput outer n (encodeBitInput input)
            (encodeBitInput leftRandomness) =
          outer.pcp.decisionRunner.execute
            (outer.pcp.decisionRequest input
              (prefixBits (nativeWidth_le_widthEnvelope outer n)
                rightRandomness)) := by
      rw [encodeBitInput_heq (congrFun hwidth n) hrandomness]
      exact paddedDecisionOutput_eq outer input rightRandomness
    refine HEq.trans (heq_of_eq hleft) ?_
    rw [hcode]
    exact decodeThreeCNF_heq (congrFun hcount n) rfl

end NearCubicWires.PaddedProjectionRunnerOutputs
