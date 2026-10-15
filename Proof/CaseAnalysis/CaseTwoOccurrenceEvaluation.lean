import Proof.MachineModel.CanonicalBitSliceProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceSpecification

/-!
# Natural-number specification of one Case-2 occurrence value

`CaseTwoOccurrenceSpecification.caseTwoSeed_apply_executable` reduces one
scheduled Case-2 seed bit to

```
executableOccurrenceValue (caseTwoFactoryPCPP pcppSource caseTwo)
  (caseTwoOccurrenceCoordinates pcppSource caseTwo point)
```

whose right-hand side is still phrased in the dependent PCPP vocabulary:
`Fin`-indexed shape fields, a `Finset (Fin n)` support, a `TwoLiteralClause`,
and a `Literal`.  A fixed `NPOracleProgram` cannot consume any of those.

This module removes that vocabulary without changing the value.  Everything
below is stated over natural numbers and `Bool`, and every factory access is
one `PolynomialNatProgram.execute` call on an explicitly named request:

* `occurrenceShapeCode` — the single `shapeRunner` call;
* `occurrenceClauseCode` — the single `clauseRunner` call;
* `occurrenceSupportCode` — one `supportRunner` call per systematic index;
* `occurrenceHonestCode` — the single `honestRunner` call.

`executableOccurrenceValue_eq_occurrenceValue` is the resulting exact
specification.  `parityOn_decodeSupport_eq_maskFold` is the one non-mechanical
step: it converts the semantic parity over a decoded `Finset` support into the
masked exclusive-or fold over `List.range n` that the balanced parity
substrate of `CanonicalTaggedParityProgram` actually computes.
-/

namespace NearCubicWires.CaseTwoOccurrenceEvaluation

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The parity bridge

`parityOn` folds exclusive-or over `Finset.toList` of a decoded support, while
every executable parity stage folds over the flat index range `0, …, n - 1`.
The two agree because both count the selected `true` positions modulo two. -/

/-- Exclusive-or folding is counting `true` positions modulo two. -/
private theorem foldl_xor_eq_decide_odd {α : Type} (select : α → Bool)
    (elements : List α) (accumulator : Bool) :
    elements.foldl
        (fun parity element => xor parity (select element)) accumulator =
      xor accumulator (decide (Odd (elements.countP select))) := by
  induction elements generalizing accumulator with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, List.countP_cons]
      by_cases hhead : select head = true
      · rcases Nat.mod_two_eq_zero_or_one (tail.countP select) with
          hparity | hparity
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
      · simp only [Bool.not_eq_true] at hhead
        simp [hhead]

/-- The enumeration of a filtered universe is a permutation of the filtered
index enumeration.  Only the order can differ, and exclusive-or folding is
order independent through the count above. -/
private theorem toList_filter_perm {n : ℕ} (select : Fin n → Bool) :
    ((Finset.univ : Finset (Fin n)).filter
        (fun index => select index)).toList.Perm
      ((List.finRange n).filter select) := by
  rw [← Multiset.coe_eq_coe, Finset.coe_toList, Finset.filter_val]
  change Multiset.filter (fun index => select index = true)
    (↑(List.finRange n)) = _
  rw [Multiset.filter_coe]
  simp

/-- One masked bit of a decoded support: index `position` contributes exactly
when the support code selects it and the input carries a one there. -/
def supportMaskBit {n : ℕ} (code : ℕ) (input : BitInput n) (position : ℕ) :
    Bool :=
  if hposition : position < n then
    code.testBit position && input ⟨position, hposition⟩
  else
    false

/-- The masked bit list folded by the executable parity stage. -/
def supportMaskBits {n : ℕ} (code : ℕ) (input : BitInput n) : List Bool :=
  (List.range n).map (supportMaskBit code input)

/-- **The parity bridge.**  The semantic parity of the decoded support equals
the exclusive-or fold of the masked bit list over the flat index range.  This
is the only step of the Case-2 occurrence evaluator that is not a mechanical
re-association of factory calls. -/
theorem parityOn_decodeSupport_eq_maskFold {n : ℕ} (code : ℕ)
    (input : BitInput n) :
    parityOn (decodeSupport n code) input =
      (supportMaskBits code input).foldl xor false := by
  have hselect :
      ((Finset.univ : Finset (Fin n)).filter
            (fun index => code.testBit index.val)).toList.countP
          (fun index => input index) =
        (List.range n).countP (supportMaskBit code input) := by
    rw [(toList_filter_perm (fun index : Fin n => code.testBit index.val)).countP_eq
      (fun index => input index)]
    rw [List.countP_filter]
    rw [← List.map_coe_finRange_eq_range, List.countP_map]
    apply List.countP_congr
    intro element _
    simp only [Function.comp_apply, supportMaskBit, Fin.eta, Fin.is_lt,
      dite_true, Bool.and_eq_true]
    exact and_comm
  rw [supportMaskBits, List.foldl_map]
  rw [parityOn, decodeSupport]
  rw [foldl_xor_eq_decide_odd (fun index : Fin n => input index)]
  rw [foldl_xor_eq_decide_odd (supportMaskBit code input)]
  rw [hselect]

/-! ## 2. Factory calls in natural-number coordinates

The dependent shape fields of `factory.forCircuit circuit` are kept as the
official spelling of every width, so that no statement below carries two
defeq-but-distinct arities.  Their natural-number readouts from the single
shape-runner call are recorded separately in §3. -/

/-- One support-runner call at a systematic index. -/
def occurrenceSupportCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (index : ℕ) : ℕ :=
  factory.supportRunner.execute
    ⟨n, circuit.size, encodeBooleanCircuit circuit, index⟩

/-- The single honest-runner call supplying the auxiliary block. -/
def occurrenceHonestCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n) : ℕ :=
  factory.honestRunner.execute
    ⟨n, circuit.size, encodeBooleanCircuit circuit, input⟩

/-- The single clause-runner call at one clause address. -/
def occurrenceClauseCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (address : ℕ) : ℕ :=
  factory.clauseRunner.execute
    ⟨n, circuit.size, encodeBooleanCircuit circuit,
      (factory.forCircuit circuit).systematicBits +
        (factory.forCircuit circuit).auxiliaryBits,
      address⟩

/-- One bit of the honest assignment word, selected by a flat index.  A
systematic index costs one `supportRunner` call folded by the parity bridge of
§1; an auxiliary index costs one `honestRunner` call and one digit read. -/
noncomputable def occurrenceAssignmentBit
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n)
    (index : ℕ) : Bool :=
  if index < (factory.forCircuit circuit).systematicBits then
    parityOn (decodeSupport n (occurrenceSupportCode factory circuit index))
      input
  else
    (occurrenceHonestCode factory circuit input).testBit
      (index - (factory.forCircuit circuit).systematicBits)

/-- The literal code selected by one occurrence coordinate: the left field of
the clause code for a left occurrence, the right field otherwise. -/
def occurrenceLiteralCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (address : ℕ) (position : Bool) :
    ℕ :=
  if position then
    (Nat.unpair (occurrenceClauseCode factory circuit address)).2
  else
    (Nat.unpair (occurrenceClauseCode factory circuit address)).1

/-- One honest occurrence bit, entirely in natural-number coordinates: the
selected assignment bit, complemented exactly when the literal code's tag
field is odd. -/
noncomputable def occurrenceValue (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n)
    (address : ℕ) (position : Bool) : Bool :=
  xor
    (occurrenceAssignmentBit factory circuit input
      ((Nat.unpair
          (occurrenceLiteralCode factory circuit address position)).2 %
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)))
    ((Nat.unpair
      (occurrenceLiteralCode factory circuit address position)).1.testBit 0)

/-! ## 3. Widths read out of the single shape call -/

/-- The single shape-runner call of one occurrence evaluation. -/
def occurrenceShapeCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  factory.shapeRunner.execute (factory.shapeRequest circuit)

theorem systematicBits_eq_shapeCode
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) :
    (factory.forCircuit circuit).systematicBits =
      (Nat.unpair (occurrenceShapeCode factory circuit)).1 + 1 :=
  rfl

theorem auxiliaryBits_eq_shapeCode
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) :
    (factory.forCircuit circuit).auxiliaryBits =
      (Nat.unpair (Nat.unpair (occurrenceShapeCode factory circuit)).2).1 :=
  rfl

theorem clauseBits_eq_shapeCode
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) :
    (factory.forCircuit circuit).clauseBits =
      (Nat.unpair (Nat.unpair (occurrenceShapeCode factory circuit)).2).2 :=
  rfl

theorem assignmentBits_positive (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) :
    0 < (factory.forCircuit circuit).systematicBits +
      (factory.forCircuit circuit).auxiliaryBits := by
  rw [systematicBits_eq_shapeCode]
  omega

/-! ## 4. The exact specification -/

private theorem literal_eval_decodeLiteral {arity : ℕ} (harity : 0 < arity)
    (code : ℕ) (assignment : BitInput arity) :
    (decodeLiteral harity code).eval assignment =
      xor (assignment ⟨(Nat.unpair code).2 % arity, Nat.mod_lt _ harity⟩)
        ((Nat.unpair code).1.testBit 0) := by
  by_cases htag : (Nat.unpair code).1 % 2 = 0
  · have hbit : (Nat.unpair code).1.testBit 0 = false :=
      Nat.mod_two_eq_zero_iff_testBit_zero.mp htag
    simp [decodeLiteral, Literal.eval, htag, hbit]
  · have hmod : (Nat.unpair code).1 % 2 = 1 := by
      have hlt := Nat.mod_lt (Nat.unpair code).1 (by omega : 0 < 2)
      omega
    have hbit : (Nat.unpair code).1.testBit 0 = true :=
      Nat.mod_two_eq_one_iff_testBit_zero.mp hmod
    simp [decodeLiteral, Literal.eval, htag, hbit]

private theorem addCases_apply {left right : ℕ} {motive : Sort _}
    (onLeft : Fin left → motive) (onRight : Fin right → motive)
    (index : Fin (left + right)) :
    Fin.addCases onLeft onRight index =
      if hindex : index.val < left then onLeft ⟨index.val, hindex⟩
      else onRight ⟨index.val - left, by omega⟩ := by
  by_cases hindex : index.val < left
  · rw [dif_pos hindex]
    have hcast : index = Fin.castAdd right ⟨index.val, hindex⟩ := by
      apply Fin.ext
      rfl
    conv_lhs => rw [hcast]
    rw [Fin.addCases_left]
  · rw [dif_neg hindex]
    have hbound : index.val - left < right := by omega
    have hcast : index = Fin.natAdd left ⟨index.val - left, hbound⟩ := by
      apply Fin.ext
      change index.val = left + (index.val - left)
      omega
    conv_lhs => rw [hcast]
    rw [Fin.addCases_right]

/-- The honest assignment of the instantiated factory, read at a flat index. -/
theorem executableOccurrenceAssignment_apply
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n)
    (index : Fin ((factory.forCircuit circuit).systematicBits +
      (factory.forCircuit circuit).auxiliaryBits)) :
    executableOccurrenceAssignment (factory.forCircuit circuit) input index =
      occurrenceAssignmentBit factory circuit input index.val := by
  rw [executableOccurrenceAssignment, addCases_apply, occurrenceAssignmentBit]
  by_cases hindex :
      index.val < (factory.forCircuit circuit).systematicBits
  · rw [dif_pos hindex, if_pos hindex]
    rfl
  · rw [dif_neg hindex, if_neg hindex]
    rfl

private theorem clause_left_eq (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n)
    (address : Fin (2 ^ (factory.forCircuit circuit).clauseBits)) :
    ((factory.forCircuit circuit).clause address).left =
      decodeLiteral (assignmentBits_positive factory circuit)
        (Nat.unpair (occurrenceClauseCode factory circuit address.val)).1 :=
  rfl

private theorem clause_right_eq (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n)
    (address : Fin (2 ^ (factory.forCircuit circuit).clauseBits)) :
    ((factory.forCircuit circuit).clause address).right =
      decodeLiteral (assignmentBits_positive factory circuit)
        (Nat.unpair (occurrenceClauseCode factory circuit address.val)).2 :=
  rfl

/-- The occurrence literal is the decoded field of the single clause call. -/
theorem executableOccurrenceLiteral_eq
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n)
    (encoded :
      BitInput (n + (factory.forCircuit circuit).clauseBits + 1)) :
    executableOccurrenceLiteral (factory.forCircuit circuit) encoded =
      decodeLiteral (assignmentBits_positive factory circuit)
        (occurrenceLiteralCode factory circuit
          (binaryAddress (occurrenceClauseAddress encoded)).val
          (occurrencePosition encoded)) := by
  unfold executableOccurrenceLiteral occurrenceLiteralCode
  cases occurrencePosition encoded
  · exact clause_left_eq factory circuit
      (binaryAddress (occurrenceClauseAddress encoded))
  · exact clause_right_eq factory circuit
      (binaryAddress (occurrenceClauseAddress encoded))

/-- **Exact natural-number specification of one occurrence value.**  Every
factory access on the right-hand side is one `PolynomialNatProgram.execute`
call on a request built from `n`, `circuit.size`,
`encodeBooleanCircuit circuit` and one natural index. -/
theorem executableOccurrenceValue_eq_occurrenceValue
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n)
    (encoded :
      BitInput (n + (factory.forCircuit circuit).clauseBits + 1)) :
    executableOccurrenceValue (factory.forCircuit circuit) encoded =
      occurrenceValue factory circuit (occurrenceInput encoded)
        (binaryAddress (occurrenceClauseAddress encoded)).val
        (occurrencePosition encoded) := by
  rw [executableOccurrenceValue, executableOccurrenceLiteral_eq,
    literal_eval_decodeLiteral, executableOccurrenceAssignment_apply,
    occurrenceValue]

/-- The systematic half of the assignment, already in the masked-fold shape
consumed by the balanced parity substrate. -/
theorem occurrenceAssignmentBit_systematic
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n)
    {index : ℕ}
    (hindex : index < (factory.forCircuit circuit).systematicBits) :
    occurrenceAssignmentBit factory circuit input index =
      (supportMaskBits (occurrenceSupportCode factory circuit index)
        input).foldl xor false := by
  rw [occurrenceAssignmentBit, if_pos hindex,
    parityOn_decodeSupport_eq_maskFold]

/-- The auxiliary half of the assignment: one digit of the single honest
call. -/
theorem occurrenceAssignmentBit_auxiliary
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (input : BitInput n)
    {index : ℕ}
    (hindex : ¬ index < (factory.forCircuit circuit).systematicBits) :
    occurrenceAssignmentBit factory circuit input index =
      (occurrenceHonestCode factory circuit input).testBit
        (index - (factory.forCircuit circuit).systematicBits) := by
  rw [occurrenceAssignmentBit, if_neg hindex]

/-! ## 5. Occurrence coordinates of one public input code

The evaluator receives the requested occurrence point as a single natural
code.  These three identities are the whole coordinate ABI: the PCPP input is
the low digit window, the clause address is the interior window computed by
`CanonicalBitSliceProgram`, and the occurrence position is one digit read. -/

theorem occurrenceInput_prefixView (inputArity clauseBits inputCode : ℕ) :
    occurrenceInput
        (bitInputPrefixView (inputArity + clauseBits + 1) inputCode) =
      bitInputPrefixView inputArity inputCode :=
  rfl

theorem occurrencePosition_prefixView (inputArity clauseBits inputCode : ℕ) :
    occurrencePosition
        (bitInputPrefixView (inputArity + clauseBits + 1) inputCode) =
      inputCode.testBit (inputArity + clauseBits) :=
  rfl

/-- The clause address of one occurrence point is exactly the interior digit
window scanned by `bitSliceProgram`. -/
theorem binaryAddress_occurrenceClauseAddress_prefixView
    (inputArity clauseBits inputCode : ℕ) :
    (binaryAddress
        (occurrenceClauseAddress
          (bitInputPrefixView (inputArity + clauseBits + 1) inputCode))).val =
      bitSlice inputArity clauseBits inputCode := by
  have hbits :
      occurrenceClauseAddress
          (bitInputPrefixView (inputArity + clauseBits + 1) inputCode) =
        fun index : Fin clauseBits =>
          (Nat.shiftRight inputCode inputArity).testBit index.val := by
    funext index
    change inputCode.testBit (inputArity + index.val) = _
    exact (Nat.testBit_shiftRight inputCode).symm
  have hvalue :
      (binaryAddress
          (occurrenceClauseAddress
            (bitInputPrefixView (inputArity + clauseBits + 1)
              inputCode))).val =
        encodeBitInput
            (occurrenceClauseAddress
              (bitInputPrefixView (inputArity + clauseBits + 1) inputCode)) %
          2 ^ clauseBits :=
    rfl
  rw [hvalue, hbits, encodeBitInput_eq_ofBits, Nat.ofBits_testBit, bitSlice]
  exact Nat.mod_mod_of_dvd _ dvd_rfl

/-- One masked support digit of a public input code: two digit reads and one
range test, with no `Fin` coordinate crossing the executable boundary. -/
theorem supportMaskBit_prefixView
    (code inputArity inputCode position : ℕ) :
    supportMaskBit code (bitInputPrefixView inputArity inputCode) position =
      (decide (position < inputArity) &&
        (code.testBit position && inputCode.testBit position)) := by
  unfold supportMaskBit
  by_cases hposition : position < inputArity
  · rw [dif_pos hposition]
    simp [hposition, bitInputPrefixView]
  · rw [dif_neg hposition]
    simp [hposition]

/-- One honest occurrence bit of the instantiated factory as a function of the
single public occurrence code.  Nothing on the right-hand side is dependently
typed: `bitSlice` is the interior digit window of `CanonicalBitSliceProgram`,
`bitInputPrefixView` is the low window read by the honest runner, and the
position is one digit. -/
noncomputable def occurrenceCodeValue
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : Bool :=
  occurrenceValue factory circuit (bitInputPrefixView n inputCode)
    (bitSlice n (factory.forCircuit circuit).clauseBits inputCode)
    (inputCode.testBit (n + (factory.forCircuit circuit).clauseBits))

/-- **The executable Case-2 occurrence target.**  Reading the requested
occurrence point as one natural code, the honest occurrence value of the
published factory is exactly `occurrenceCodeValue`: four runner executions,
one interior digit window, one masked parity fold, and one digit read. -/
theorem executableOccurrenceValue_prefixView
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) :
    executableOccurrenceValue (factory.forCircuit circuit)
        (bitInputPrefixView
          (n + (factory.forCircuit circuit).clauseBits + 1) inputCode) =
      occurrenceCodeValue factory circuit inputCode := by
  rw [executableOccurrenceValue_eq_occurrenceValue,
    occurrenceInput_prefixView, occurrencePosition_prefixView,
    binaryAddress_occurrenceClauseAddress_prefixView, occurrenceCodeValue]

end NearCubicWires.CaseTwoOccurrenceEvaluation
