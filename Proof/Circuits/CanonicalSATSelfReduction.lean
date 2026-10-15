import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.TseitinCNF

/-!
# Canonical SAT prefix self-reduction

This module implements the one reusable search primitive required by the
C.12 recovery layer.  Starting from one canonical CNF, it asks whether the
current prefix can be extended with zero; only when that query is
unsatisfiable does it commit one.  The result is the reversed bit list of the
lexicographically first model prefix.  Formula construction and every SAT
query occur inside one fixed `NPOracleProgram`.
-/

namespace NearCubicWires.CanonicalSATSelfReduction

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TseitinCNF

def prefixUnitClause (value : Bool) (index : ℕ) : EncodedClause :=
  if value then positiveUnit index else negativeUnit index

def constrainPrefixBit
    (value : Bool) (index : ℕ) (formula : EncodedCNF) : EncodedCNF :=
  prefixUnitClause value index :: formula

def canonicalSatBit (formula : EncodedCNF) : Bool :=
  encodedSat (Encodable.encode formula)

structure PrefixSATResult where
  constrainedFormula : EncodedCNF
  reverseBits : List Bool

def prefixSATScan :
    ℕ → ℕ → EncodedCNF → List Bool → PrefixSATResult
  | 0, _index, formula, reverseBits =>
      ⟨formula, reverseBits⟩
  | count + 1, index, formula, reverseBits =>
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        prefixSATScan count (index + 1) zeroFormula
          (false :: reverseBits)
      else
        let oneFormula := constrainPrefixBit true index formula
        prefixSATScan count (index + 1) oneFormula
          (true :: reverseBits)

def recoveredPrefixReverse
    (count : ℕ) (formula : EncodedCNF) : List Bool :=
  (prefixSATScan count 0 formula []).reverseBits

/-- The executable self-reduction exposes only the latest decision.  Earlier
decisions remain committed in the evolving CNF, so materializing an assignment
list would add runtime state without changing the queried target bit. -/
def latestPrefixBitCode : List Bool → ℕ
  | [] => 0
  | value :: _ => value.toNat

@[simp] theorem latestPrefixBitCode_nil :
    latestPrefixBitCode [] = 0 := rfl

@[simp] theorem latestPrefixBitCode_cons
    (value : Bool) (rest : List Bool) :
    latestPrefixBitCode (value :: rest) = value.toNat := rfl

def prefixSATChoices : ℕ → ℕ → EncodedCNF → List Bool
  | 0, _index, _formula => []
  | count + 1, index, formula =>
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        false :: prefixSATChoices count (index + 1) zeroFormula
      else
        true :: prefixSATChoices count (index + 1)
          (constrainPrefixBit true index formula)

def recoveredPrefix (count : ℕ) (formula : EncodedCNF) : List Bool :=
  prefixSATChoices count 0 formula

def constrainPrefixChoices :
    ℕ → EncodedCNF → List Bool → EncodedCNF
  | _index, formula, [] => formula
  | index, formula, value :: rest =>
      constrainPrefixChoices (index + 1)
        (constrainPrefixBit value index formula) rest

@[simp] theorem prefixSATChoices_length
    (count index : ℕ) (formula : EncodedCNF) :
    (prefixSATChoices count index formula).length = count := by
  induction count generalizing index formula with
  | zero =>
      rfl
  | succ count ih =>
      unfold prefixSATChoices
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        simp only [List.length_cons, ih]
      · rw [if_neg hzero]
        simp only [List.length_cons, ih]

theorem prefixSATScan_reverseBits_eq
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    (prefixSATScan count index formula reverseBits).reverseBits =
      (prefixSATChoices count index formula).reverse ++ reverseBits := by
  induction count generalizing index formula reverseBits with
  | zero =>
      rfl
  | succ count ih =>
      unfold prefixSATScan prefixSATChoices
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        rw [ih]
        simp only [hzero, if_pos, List.reverse_cons, List.append_assoc,
          List.singleton_append]
      · rw [if_neg hzero]
        rw [ih]
        simp only [hzero, Bool.false_eq_true, if_false,
          List.reverse_cons, List.append_assoc, List.singleton_append]

theorem prefixSATScan_constrainedFormula_eq
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    (prefixSATScan count index formula reverseBits).constrainedFormula =
      constrainPrefixChoices index formula
        (prefixSATChoices count index formula) := by
  induction count generalizing index formula reverseBits with
  | zero =>
      rfl
  | succ count ih =>
      unfold prefixSATScan prefixSATChoices
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        simpa only [hzero, if_pos, constrainPrefixChoices] using
          ih (index + 1) (constrainPrefixBit false index formula)
            (false :: reverseBits)
      · rw [if_neg hzero]
        simpa only [hzero, Bool.false_eq_true, if_false,
          constrainPrefixChoices] using
          ih (index + 1) (constrainPrefixBit true index formula)
            (true :: reverseBits)

@[simp] theorem recoveredPrefixReverse_eq
    (count : ℕ) (formula : EncodedCNF) :
    recoveredPrefixReverse count formula =
      (recoveredPrefix count formula).reverse := by
  rw [recoveredPrefixReverse, recoveredPrefix,
    prefixSATScan_reverseBits_eq]
  simp only [List.append_nil]

@[simp] theorem recoveredPrefix_length
    (count : ℕ) (formula : EncodedCNF) :
    (recoveredPrefix count formula).length = count :=
  prefixSATChoices_length count 0 formula

@[simp] theorem prefixSATScan_reverseBits_length
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    (prefixSATScan count index formula reverseBits).reverseBits.length =
      count + reverseBits.length := by
  induction count generalizing index formula reverseBits with
  | zero =>
      simp only [prefixSATScan, Nat.zero_add]
  | succ count ih =>
      unfold prefixSATScan
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
          ih (index + 1) (constrainPrefixBit false index formula)
            (false :: reverseBits)
      · rw [if_neg hzero]
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
          ih (index + 1) (constrainPrefixBit true index formula)
            (true :: reverseBits)

@[simp] theorem recoveredPrefixReverse_length
    (count : ℕ) (formula : EncodedCNF) :
    (recoveredPrefixReverse count formula).length = count := by
  simp [recoveredPrefixReverse]

/-- The exact oracle decisions made by the search.  This theorem is the
semantic contract later used to prove lexicographic minimality: a zero is
chosen iff the zero-extended canonical formula is satisfiable. -/
theorem prefixSATScan_step
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    prefixSATScan (count + 1) index formula reverseBits =
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        prefixSATScan count (index + 1) zeroFormula
          (false :: reverseBits)
      else
        prefixSATScan count (index + 1)
          (constrainPrefixBit true index formula)
          (true :: reverseBits) := by
  rfl

/-! ## Fixed interpreter -/

/-- Input is `pair (encode formula) (encodeUnary count)`.

Registers:
* `r2`: the formula containing the committed prefix;
* `r3`: unary loop cursor;
* `r4`: current variable index;
* `r5`: recovered bits in reverse order;
* `r6`: permanent zero;
* `r7`--`r10`: literal, clause/payload, query, and SAT result;
* `r11`: permanent one.
-/
def prefixSATProgram : NPOracleProgram :=
  [ .unpairRight 0 3 1
  , .unpairLeft 0 2 2
  , .set 4 0 3
  , .set 5 0 4
  , .set 11 1 5
  , .branchZero 3 39 6
  , .unpairRight 3 3 7
  , .pair 6 4 7 8
  , .set 8 0 9
  , .pair 7 8 8 10
  , .increment 8 11
  , .pair 7 8 8 12
  , .increment 8 13
  , .pair 7 8 8 14
  , .increment 8 15
  , .pair 8 2 9 16
  , .increment 9 17
  , .sat 9 10 18
  , .branchZero 10 24 19
  -- Zero is extendible: commit the queried formula and latest recovered bit.
  , .copy 6 8 20
  , .copy 6 5 21
  , .copy 9 2 22
  , .increment 4 23
  , .branchZero 6 5 5
  -- Zero is not extendible: build and commit the positive unit clause.
  , .pair 11 4 7 25
  , .set 8 0 26
  , .pair 7 8 8 27
  , .increment 8 28
  , .pair 7 8 8 29
  , .increment 8 30
  , .pair 7 8 8 31
  , .increment 8 32
  , .pair 8 2 9 33
  , .increment 9 34
  , .copy 11 8 35
  , .copy 11 5 36
  , .copy 9 2 37
  , .increment 4 38
  , .branchZero 6 5 5
  , .halt 5
  ]

def prefixSATInput (count : ℕ) (formula : EncodedCNF) : ℕ :=
  Nat.pair (Encodable.encode formula) (encodeUnary count)

def prefixSATOutput (count : ℕ) (formula : EncodedCNF) : ℕ :=
  latestPrefixBitCode (recoveredPrefixReverse count formula)

private def prefixSATCurrentBound
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) : ℕ :=
  max 1 <|
      max (encodeUnary count) <|
        max index <|
        max (Encodable.encode formula) (latestPrefixBitCode reverseBits)

/-- Exact trace-dependent register envelope.  It includes the speculative
zero query even on the one branch, because that query is issued before the
branch is known. -/
def prefixSATRegisterBound :
    ℕ → ℕ → EncodedCNF → List Bool → ℕ
  | 0, index, formula, reverseBits =>
      prefixSATCurrentBound 0 index formula reverseBits
  | count + 1, index, formula, reverseBits =>
      let zeroFormula := constrainPrefixBit false index formula
      let recursiveBound :=
        if canonicalSatBit zeroFormula then
          prefixSATRegisterBound count (index + 1) zeroFormula
            (false :: reverseBits)
        else
          prefixSATRegisterBound count (index + 1)
            (constrainPrefixBit true index formula)
            (true :: reverseBits)
      max (prefixSATCurrentBound (count + 1) index formula reverseBits)
        (max (Encodable.encode zeroFormula) recursiveBound)

def prefixSATMaximumBits
    (count : ℕ) (formula : EncodedCNF) : ℕ :=
  natBitLength <|
    max (prefixSATInput count formula)
      (prefixSATRegisterBound count 0 formula [])

def prefixSATLoopFuel :
    ℕ → ℕ → EncodedCNF → List Bool → ℕ
  | 0, _index, _formula, _reverseBits => 2
  | count + 1, index, formula, reverseBits =>
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        19 + prefixSATLoopFuel count (index + 1) zeroFormula
          (false :: reverseBits)
      else
        29 + prefixSATLoopFuel count (index + 1)
          (constrainPrefixBit true index formula)
          (true :: reverseBits)

def prefixSATFuel (count : ℕ) (formula : EncodedCNF) : ℕ :=
  5 + prefixSATLoopFuel count 0 formula []

theorem prefixSATLoopFuel_le
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    prefixSATLoopFuel count index formula reverseBits ≤
      30 * count + 2 := by
  induction count generalizing index formula reverseBits with
  | zero => rfl
  | succ count ih =>
      unfold prefixSATLoopFuel
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        have hrec :=
          ih (index + 1) (constrainPrefixBit false index formula)
            (false :: reverseBits)
        omega
      · rw [if_neg hzero]
        have hrec :=
          ih (index + 1) (constrainPrefixBit true index formula)
            (true :: reverseBits)
        omega

theorem prefixSATFuel_le (count : ℕ) (formula : EncodedCNF) :
    prefixSATFuel count formula ≤ 30 * count + 7 := by
  unfold prefixSATFuel
  have hloop := prefixSATLoopFuel_le count 0 formula []
  omega

private theorem encodeUnary_double_le_succ (count : ℕ) (hcount : 0 < count) :
    2 * encodeUnary count ≤ encodeUnary (count + 1) := by
  have hpositive : 1 ≤ encodeUnary count := by
    cases count with
    | zero =>
        omega
    | succ count =>
        simp only [encodeUnary]
        exact Nat.left_le_pair 1 (encodeUnary count)
  simp only [encodeUnary, Nat.pair]
  split_ifs with horder
  · nlinarith
  · have hle : encodeUnary count ≤ 1 := Nat.le_of_not_gt horder
    nlinarith

theorem count_le_natBitLength_encodeUnary (count : ℕ) :
    count ≤ natBitLength (encodeUnary count) := by
  induction count with
  | zero =>
      unfold natBitLength
      omega
  | succ count ih =>
      cases count with
      | zero =>
          norm_num [encodeUnary, natBitLength, Nat.pair]
      | succ count =>
          have hnonzero : encodeUnary (count + 1) ≠ 0 := by
            have hpositive : 1 ≤ encodeUnary (count + 1) := by
              simp only [encodeUnary]
              exact Nat.left_le_pair 1 (encodeUnary count)
            omega
          have hdouble :=
            encodeUnary_double_le_succ (count + 1) (by omega)
          have hlog :
              Nat.log 2 (encodeUnary (count + 1)) + 1 ≤
                Nat.log 2 (encodeUnary ((count + 1) + 1)) := by
            rw [← Nat.log_mul_base (b := 2)
              (n := encodeUnary (count + 1)) (by omega) hnonzero]
            exact Nat.log_mono_right (by
              simpa only [Nat.mul_comm] using hdouble)
          unfold natBitLength at ih ⊢
          omega

@[simp] theorem prefixSATProgram_hasSat :
    prefixSATProgram.any (fun instruction =>
      match instruction with
      | .sat _ _ _ => true
      | _ => false) = true := by
  rfl

private theorem valueBits
    {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound)
    (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem prefixSATCurrentBound_one
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    1 ≤ prefixSATCurrentBound count index formula reverseBits := by
  unfold prefixSATCurrentBound
  omega

private theorem prefixSATCurrentBound_cursor
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    encodeUnary count ≤
      prefixSATCurrentBound count index formula reverseBits := by
  unfold prefixSATCurrentBound
  omega

private theorem prefixSATCurrentBound_index
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    index ≤ prefixSATCurrentBound count index formula reverseBits := by
  unfold prefixSATCurrentBound
  omega

private theorem prefixSATCurrentBound_formula
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    Encodable.encode formula ≤
      prefixSATCurrentBound count index formula reverseBits := by
  unfold prefixSATCurrentBound
  omega

private theorem prefixSATCurrentBound_latestBit
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    latestPrefixBitCode reverseBits ≤
      prefixSATCurrentBound count index formula reverseBits := by
  unfold prefixSATCurrentBound
  omega

private theorem prefixSATCurrentBound_le_registerBound
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    prefixSATCurrentBound count index formula reverseBits ≤
      prefixSATRegisterBound count index formula reverseBits := by
  cases count with
  | zero => rfl
  | succ count =>
      unfold prefixSATRegisterBound
      exact le_max_left _ _

private theorem prefixSATZeroQuery_le_registerBound
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    Encodable.encode (constrainPrefixBit false index formula) ≤
      prefixSATRegisterBound (count + 1) index formula reverseBits := by
  unfold prefixSATRegisterBound
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem prefixSATRecursiveBound_le
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    let zeroFormula := constrainPrefixBit false index formula
    let nextBound :=
      if canonicalSatBit zeroFormula then
        prefixSATRegisterBound count (index + 1) zeroFormula
          (false :: reverseBits)
      else
        prefixSATRegisterBound count (index + 1)
          (constrainPrefixBit true index formula)
          (true :: reverseBits)
    nextBound ≤
      prefixSATRegisterBound (count + 1) index formula reverseBits := by
  change
    (if canonicalSatBit (constrainPrefixBit false index formula) then
        prefixSATRegisterBound count (index + 1)
          (constrainPrefixBit false index formula) (false :: reverseBits)
      else
        prefixSATRegisterBound count (index + 1)
          (constrainPrefixBit true index formula) (true :: reverseBits)) ≤
      max (prefixSATCurrentBound (count + 1) index formula reverseBits)
        (max (Encodable.encode (constrainPrefixBit false index formula))
          (if canonicalSatBit (constrainPrefixBit false index formula) then
            prefixSATRegisterBound count (index + 1)
              (constrainPrefixBit false index formula)
              (false :: reverseBits)
          else
            prefixSATRegisterBound count (index + 1)
              (constrainPrefixBit true index formula)
              (true :: reverseBits)))
  exact (le_max_right _ _).trans (le_max_right _ _)

private theorem encodeUnary_tail_le (count : ℕ) :
    encodeUnary count ≤ encodeUnary (count + 1) := by
  simp only [encodeUnary]
  exact Nat.right_le_pair 1 (encodeUnary count)

private theorem encode_list_tail_le
    {α : Type} [Encodable α] (head : α) (tail : List α) :
    Encodable.encode tail ≤ Encodable.encode (head :: tail) := by
  rw [Encodable.encode_list_cons]
  have hpair :=
    Nat.right_le_pair (Encodable.encode head) (Encodable.encode tail)
  omega

private def unitLiteralCode (value : Bool) (index : ℕ) : ℕ :=
  Nat.pair value.toNat index

private def unitCellOne (value : Bool) (index : ℕ) : ℕ :=
  Nat.pair (unitLiteralCode value index) 0

private def unitCodeOne (value : Bool) (index : ℕ) : ℕ :=
  unitCellOne value index + 1

private def unitCellTwo (value : Bool) (index : ℕ) : ℕ :=
  Nat.pair (unitLiteralCode value index) (unitCodeOne value index)

private def unitCodeTwo (value : Bool) (index : ℕ) : ℕ :=
  unitCellTwo value index + 1

private def unitCellThree (value : Bool) (index : ℕ) : ℕ :=
  Nat.pair (unitLiteralCode value index) (unitCodeTwo value index)

private def unitCodeThree (value : Bool) (index : ℕ) : ℕ :=
  unitCellThree value index + 1

private def constrainedCell
    (value : Bool) (index : ℕ) (formula : EncodedCNF) : ℕ :=
  Nat.pair (unitCodeThree value index) (Encodable.encode formula)

private def constrainedCode
    (value : Bool) (index : ℕ) (formula : EncodedCNF) : ℕ :=
  constrainedCell value index formula + 1

@[simp] private theorem unitLiteralCode_eq
    (value : Bool) (index : ℕ) :
    unitLiteralCode value index = Encodable.encode (value, index) := by
  cases value <;> rfl

@[simp] private theorem unitCodeThree_eq
    (value : Bool) (index : ℕ) :
    unitCodeThree value index =
      Encodable.encode (prefixUnitClause value index) := by
  cases value <;>
    simp [unitCodeThree, unitCellThree, unitCodeTwo, unitCellTwo,
      unitCodeOne, unitCellOne, unitLiteralCode, prefixUnitClause,
      positiveUnit, negativeUnit, triple, positive, negative,
      Encodable.encode_list_cons]

@[simp] private theorem constrainedCode_eq
    (value : Bool) (index : ℕ) (formula : EncodedCNF) :
    constrainedCode value index formula =
      Encodable.encode (constrainPrefixBit value index formula) := by
  simp [constrainedCode, constrainedCell, constrainPrefixBit,
    Encodable.encode_list_cons]

private theorem unitConstruction_le
    (value : Bool) (index : ℕ) (formula : EncodedCNF) :
    unitLiteralCode value index ≤ constrainedCode value index formula ∧
      unitCellOne value index ≤ constrainedCode value index formula ∧
      unitCodeOne value index ≤ constrainedCode value index formula ∧
      unitCellTwo value index ≤ constrainedCode value index formula ∧
      unitCodeTwo value index ≤ constrainedCode value index formula ∧
      unitCellThree value index ≤ constrainedCode value index formula ∧
      unitCodeThree value index ≤ constrainedCode value index formula ∧
      constrainedCell value index formula ≤
        constrainedCode value index formula := by
  have h01 :
      unitLiteralCode value index ≤ unitCellOne value index :=
    Nat.left_le_pair _ _
  have h12 :
      unitCellOne value index ≤ unitCodeOne value index := by
    unfold unitCodeOne
    omega
  have h23 :
      unitCodeOne value index ≤ unitCellTwo value index :=
    Nat.right_le_pair _ _
  have h34 :
      unitCellTwo value index ≤ unitCodeTwo value index := by
    unfold unitCodeTwo
    omega
  have h45 :
      unitCodeTwo value index ≤ unitCellThree value index :=
    Nat.right_le_pair _ _
  have h56 :
      unitCellThree value index ≤ unitCodeThree value index := by
    unfold unitCodeThree
    omega
  have h67 :
      unitCodeThree value index ≤ constrainedCell value index formula :=
    Nat.left_le_pair _ _
  have h78 :
      constrainedCell value index formula ≤
        constrainedCode value index formula := by
    unfold constrainedCode
    omega
  constructor
  · exact h01.trans <| h12.trans <| h23.trans <| h34.trans <|
      h45.trans <| h56.trans <| h67.trans h78
  constructor
  · exact h12.trans <| h23.trans <| h34.trans <| h45.trans <|
      h56.trans <| h67.trans h78
  constructor
  · exact h23.trans <| h34.trans <| h45.trans <| h56.trans <|
      h67.trans h78
  constructor
  · exact h34.trans <| h45.trans <| h56.trans <| h67.trans h78
  constructor
  · exact h45.trans <| h56.trans <| h67.trans h78
  constructor
  · exact h56.trans <| h67.trans h78
  constructor
  · exact h67.trans h78
  · exact h78

private def negativeQueryState
    (state : NPOracleState) (index : ℕ) (formula : EncodedCNF) :
    NPOracleState :=
  let state8 :=
    (state.write 7 (unitLiteralCode false index)).jump 8
  let state9 := (state8.write 8 0).jump 9
  let state10 := (state9.write 8 (unitCellOne false index)).jump 10
  let state11 := (state10.write 8 (unitCodeOne false index)).jump 11
  let state12 := (state11.write 8 (unitCellTwo false index)).jump 12
  let state13 := (state12.write 8 (unitCodeTwo false index)).jump 13
  let state14 := (state13.write 8 (unitCellThree false index)).jump 14
  let state15 := (state14.write 8 (unitCodeThree false index)).jump 15
  let state16 :=
    (state15.write 9 (constrainedCell false index formula)).jump 16
  (state16.write 9 (constrainedCode false index formula)).jump 17

private theorem run_negativeQuery
    (fuel maximumBits index : ℕ) (formula : EncodedCNF)
    (state : NPOracleState)
    (hpc : state.pc = 7)
    (hzero : state.registers 6 = 0)
    (hindex : state.registers 4 = index)
    (hformula : state.registers 2 = Encodable.encode formula)
    (hliteralBits :
      natBitLength (unitLiteralCode false index) ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hcellOneBits :
      natBitLength (unitCellOne false index) ≤ maximumBits)
    (hcodeOneBits :
      natBitLength (unitCodeOne false index) ≤ maximumBits)
    (hcellTwoBits :
      natBitLength (unitCellTwo false index) ≤ maximumBits)
    (hcodeTwoBits :
      natBitLength (unitCodeTwo false index) ≤ maximumBits)
    (hcellThreeBits :
      natBitLength (unitCellThree false index) ≤ maximumBits)
    (hcodeThreeBits :
      natBitLength (unitCodeThree false index) ≤ maximumBits)
    (hformulaCellBits :
      natBitLength (constrainedCell false index formula) ≤ maximumBits)
    (hformulaCodeBits :
      natBitLength (constrainedCode false index formula) ≤ maximumBits) :
    runNPOracleProgram prefixSATProgram maximumBits (fuel + 10) state =
      runNPOracleProgram prefixSATProgram maximumBits fuel
        (negativeQueryState state index formula) := by
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 9) (by rfl) hpc
    (by simp [hzero, hindex, unitLiteralCode]) hliteralBits]
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [run_set_instruction
    (fuel := fuel + 8) (by rfl) rfl hzeroBits]
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 7) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellOne])
    hcellOneBits]
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 6) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeOne])
    hcodeOneBits]
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 5) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellTwo])
    hcellTwoBits]
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 4) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeTwo])
    hcodeTwoBits]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 3) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellThree])
    hcellThreeBits]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeThree])
    hcodeThreeBits]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 1) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, constrainedCell,
        hformula])
    hformulaCellBits]
  rw [show fuel + 1 = fuel + 1 by rfl]
  rw [run_increment_instruction
    (fuel := fuel) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, constrainedCode])
    hformulaCodeBits]
  rfl

private def positiveQueryState
    (state : NPOracleState) (index : ℕ) (formula : EncodedCNF) :
    NPOracleState :=
  let state25 :=
    (state.write 7 (unitLiteralCode true index)).jump 25
  let state26 := (state25.write 8 0).jump 26
  let state27 := (state26.write 8 (unitCellOne true index)).jump 27
  let state28 := (state27.write 8 (unitCodeOne true index)).jump 28
  let state29 := (state28.write 8 (unitCellTwo true index)).jump 29
  let state30 := (state29.write 8 (unitCodeTwo true index)).jump 30
  let state31 := (state30.write 8 (unitCellThree true index)).jump 31
  let state32 := (state31.write 8 (unitCodeThree true index)).jump 32
  let state33 :=
    (state32.write 9 (constrainedCell true index formula)).jump 33
  (state33.write 9 (constrainedCode true index formula)).jump 34

private theorem run_positiveQuery
    (fuel maximumBits index : ℕ) (formula : EncodedCNF)
    (state : NPOracleState)
    (hpc : state.pc = 24)
    (hone : state.registers 11 = 1)
    (hindex : state.registers 4 = index)
    (hformula : state.registers 2 = Encodable.encode formula)
    (hliteralBits :
      natBitLength (unitLiteralCode true index) ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hcellOneBits :
      natBitLength (unitCellOne true index) ≤ maximumBits)
    (hcodeOneBits :
      natBitLength (unitCodeOne true index) ≤ maximumBits)
    (hcellTwoBits :
      natBitLength (unitCellTwo true index) ≤ maximumBits)
    (hcodeTwoBits :
      natBitLength (unitCodeTwo true index) ≤ maximumBits)
    (hcellThreeBits :
      natBitLength (unitCellThree true index) ≤ maximumBits)
    (hcodeThreeBits :
      natBitLength (unitCodeThree true index) ≤ maximumBits)
    (hformulaCellBits :
      natBitLength (constrainedCell true index formula) ≤ maximumBits)
    (hformulaCodeBits :
      natBitLength (constrainedCode true index formula) ≤ maximumBits) :
    runNPOracleProgram prefixSATProgram maximumBits (fuel + 10) state =
      runNPOracleProgram prefixSATProgram maximumBits fuel
        (positiveQueryState state index formula) := by
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 9) (by rfl) hpc
    (by simp [hone, hindex, unitLiteralCode]) hliteralBits]
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [run_set_instruction
    (fuel := fuel + 8) (by rfl) rfl hzeroBits]
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 7) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellOne])
    hcellOneBits]
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 6) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeOne])
    hcodeOneBits]
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 5) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellTwo])
    hcellTwoBits]
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 4) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeTwo])
    hcodeTwoBits]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 3) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCellThree])
    hcellThreeBits]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [run_increment_instruction
    (fuel := fuel + 2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, unitCodeThree])
    hcodeThreeBits]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [run_pair_instruction
    (fuel := fuel + 1) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, constrainedCell,
        hformula])
    hformulaCellBits]
  rw [show fuel + 1 = fuel + 1 by rfl]
  rw [run_increment_instruction
    (fuel := fuel) (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, constrainedCode])
    hformulaCodeBits]
  rfl

private theorem run_prefixSATLoop
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) (maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hcursor : state.registers 3 = encodeUnary count)
    (hformula : state.registers 2 = Encodable.encode formula)
    (hindex : state.registers 4 = index)
    (hreverse : state.registers 5 = latestPrefixBitCode reverseBits)
    (hzero : state.registers 6 = 0)
    (hone : state.registers 11 = 1)
    (hbits :
      natBitLength
          (prefixSATRegisterBound count index formula reverseBits) ≤
        maximumBits) :
    runNPOracleProgram prefixSATProgram maximumBits
        (prefixSATLoopFuel count index formula reverseBits) state =
      some
        (latestPrefixBitCode
          (prefixSATScan count index formula reverseBits).reverseBits) := by
  let bound := prefixSATRegisterBound count index formula reverseBits
  have hcurrent :
      prefixSATCurrentBound count index formula reverseBits ≤ bound :=
    prefixSATCurrentBound_le_registerBound count index formula reverseBits
  have honeBound : 1 ≤ bound :=
    (prefixSATCurrentBound_one count index formula reverseBits).trans hcurrent
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    valueBits (bound := bound) (by omega) hbits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    valueBits honeBound hbits
  have hreverseBits :
      natBitLength (latestPrefixBitCode reverseBits) ≤ maximumBits :=
    valueBits
      ((prefixSATCurrentBound_latestBit count index formula
        reverseBits).trans hcurrent)
      hbits
  induction count generalizing index formula reverseBits state with
  | zero =>
      rw [show prefixSATLoopFuel 0 index formula reverseBits = 1 + 1 by
        rfl]
      rw [run_branchZero_instruction
        (fuel := 1) (by rfl) hpc]
      rw [if_pos (by simp [hcursor, encodeUnary])]
      rw [show 1 = 0 + 1 by rfl]
      rw [run_halt_instruction
        (fuel := 0) (by rfl) rfl
        (by simpa [NPOracleState.jump] using hreverse)
        hreverseBits]
      rfl
  | succ count ih =>
      let zeroFormula := constrainPrefixBit false index formula
      let zeroCode := Encodable.encode zeroFormula
      have hzeroCodeBound : zeroCode ≤ bound := by
        exact prefixSATZeroQuery_le_registerBound count index formula reverseBits
      have hzeroCodeBits : natBitLength zeroCode ≤ maximumBits :=
        valueBits hzeroCodeBound hbits
      have hconstruction := unitConstruction_le false index formula
      rcases hconstruction with
        ⟨hliteralBound, hcellOneBound, hcodeOneBound,
          hcellTwoBound, hcodeTwoBound, hcellThreeBound,
          hcodeThreeBound, hformulaCellBound⟩
      have hliteralBits :
          natBitLength (unitLiteralCode false index) ≤ maximumBits :=
        valueBits (hliteralBound.trans hzeroCodeBound) hbits
      have hcellOneBits :
          natBitLength (unitCellOne false index) ≤ maximumBits :=
        valueBits (hcellOneBound.trans hzeroCodeBound) hbits
      have hcodeOneBits :
          natBitLength (unitCodeOne false index) ≤ maximumBits :=
        valueBits (hcodeOneBound.trans hzeroCodeBound) hbits
      have hcellTwoBits :
          natBitLength (unitCellTwo false index) ≤ maximumBits :=
        valueBits (hcellTwoBound.trans hzeroCodeBound) hbits
      have hcodeTwoBits :
          natBitLength (unitCodeTwo false index) ≤ maximumBits :=
        valueBits (hcodeTwoBound.trans hzeroCodeBound) hbits
      have hcellThreeBits :
          natBitLength (unitCellThree false index) ≤ maximumBits :=
        valueBits (hcellThreeBound.trans hzeroCodeBound) hbits
      have hcodeThreeBits :
          natBitLength (unitCodeThree false index) ≤ maximumBits :=
        valueBits (hcodeThreeBound.trans hzeroCodeBound) hbits
      have hformulaCellBits :
          natBitLength (constrainedCell false index formula) ≤ maximumBits :=
        valueBits (hformulaCellBound.trans hzeroCodeBound) hbits
      have hcursorTailBound : encodeUnary count ≤ bound := by
        exact
          (encodeUnary_tail_le count).trans <|
            (prefixSATCurrentBound_cursor (count + 1) index formula
              reverseBits).trans hcurrent
      have hcursorTailBits :
          natBitLength (encodeUnary count) ≤ maximumBits :=
        valueBits hcursorTailBound hbits
      let state6 := state.jump 6
      let state7 := (state6.write 3 (encodeUnary count)).jump 7
      let state17 := negativeQueryState state7 index formula
      by_cases hsatisfiable : canonicalSatBit zeroFormula = true
      · let recursiveBound :=
          prefixSATRegisterBound count (index + 1) zeroFormula
            (false :: reverseBits)
        have hrecursiveBound : recursiveBound ≤ bound := by
          simpa only [zeroFormula, hsatisfiable, if_pos] using
            prefixSATRecursiveBound_le count index formula reverseBits
        have hrecursiveBits :
            natBitLength recursiveBound ≤ maximumBits :=
          valueBits hrecursiveBound hbits
        let state18 :=
          (state17.write 10 (canonicalSatBit zeroFormula).toNat).jump 18
        let state19 := state18.jump 19
        let state20 := (state19.write 8 false.toNat).jump 20
        let state21 := (state20.write 5 false.toNat).jump 21
        let state22 := (state21.write 2 zeroCode).jump 22
        let state23 := (state22.write 4 (index + 1)).jump 23
        let state5 := state23.jump 5
        rw [show
            prefixSATLoopFuel (count + 1) index formula reverseBits =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 18) + 1 by
          simp only [prefixSATLoopFuel, zeroFormula, hsatisfiable, if_pos]
          omega]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 18)
          (by rfl) hpc]
        rw [if_neg (by
          rw [hcursor]
          simp only [encodeUnary]
          have := Nat.left_le_pair 1 (encodeUnary count)
          omega)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 18) state6 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 18 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 17) + 1 by omega]
        rw [run_unpairRight_instruction
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 17)
          (by rfl) rfl
          (by simp [state6, hcursor, encodeUnary])
          hcursorTailBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 17) state7 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 17 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 7) + 10 by omega]
        rw [run_negativeQuery
          (prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 7)
          maximumBits index formula state7 rfl
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hzero])
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hindex])
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hformula])
          hliteralBits hzeroBits hcellOneBits hcodeOneBits hcellTwoBits
          hcodeTwoBits hcellThreeBits hcodeThreeBits hformulaCellBits
          (by simpa [zeroCode] using hzeroCodeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 7) state17 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 7 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 6) + 1 by omega]
        rw [run_sat_instruction
          (query := zeroCode)
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 6)
          (by rfl) rfl
          (by
            simp [state17, negativeQueryState, zeroCode,
              zeroFormula, constrainedCode_eq])
          (by simpa [zeroCode] using hzeroCodeBits)
          (by
            have hs : encodedSat zeroCode = true := by
              simpa only [canonicalSatBit, zeroCode] using hsatisfiable
            simpa only [hs, Bool.toNat_true] using honeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 6) state18 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 6 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 5) + 1 by omega]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 5)
          (by rfl) rfl]
        rw [if_neg (by simp [state18, hsatisfiable])]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 5) state19 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 5 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 4) + 1 by omega]
        rw [run_copy_instruction
          (value := 0)
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 4)
          (by rfl) rfl
          (by simp [state19, state18, state17, negativeQueryState,
            state7, state6, NPOracleState.write, NPOracleState.jump,
            hzero])
          hzeroBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 4) state20 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 4 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 3) + 1 by omega]
        rw [run_copy_instruction
          (value := 0)
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 3)
          (by rfl) rfl
          (by
            simp [state20, state19, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump, hzero])
          hzeroBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 3) state21 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 3 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 2) + 1 by omega]
        rw [run_copy_instruction
          (value := zeroCode)
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 2)
          (by rfl) rfl
          (by simp [state21, state20, state19, state18, state17,
            negativeQueryState, zeroCode, zeroFormula])
          (by simpa [zeroCode] using hzeroCodeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 2) state22 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 2 =
              (prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 1) + 1 by omega]
        rw [run_increment_instruction
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits) + 1)
          (by rfl) rfl
          (by simp [state22, state21, state20, state19, state18,
            state17, negativeQueryState, state7, state6,
            NPOracleState.write, NPOracleState.jump, hindex])
          (valueBits
            (((prefixSATCurrentBound_index count (index + 1) zeroFormula
              (false :: reverseBits)).trans
              (prefixSATCurrentBound_le_registerBound count (index + 1)
                zeroFormula (false :: reverseBits))).trans hrecursiveBound)
            hbits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) zeroFormula
                (false :: reverseBits) + 1) state23 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 1 =
              prefixSATLoopFuel count (index + 1) zeroFormula
                  (false :: reverseBits) + 1 by rfl]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) zeroFormula
            (false :: reverseBits))
          (by rfl) rfl]
        rw [if_pos (by simp [state23, state22, state21, state20, state19,
          state18, state17, negativeQueryState, state7, state6,
          NPOracleState.write, NPOracleState.jump, hzero])]
        have hrec :=
          ih (index + 1) zeroFormula (false :: reverseBits)
            state5 rfl
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump])
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump,
              zeroCode, zeroFormula])
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump])
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump])
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump, hzero])
            (by simp [state5, state23, state22, state21, state20,
              state19, state18, state17, negativeQueryState, state7,
              state6, NPOracleState.write, NPOracleState.jump, hone])
            hrecursiveBits
            (prefixSATCurrentBound_le_registerBound count (index + 1)
              zeroFormula (false :: reverseBits))
            ((prefixSATCurrentBound_one count (index + 1) zeroFormula
              (false :: reverseBits)).trans
              (prefixSATCurrentBound_le_registerBound count (index + 1)
                zeroFormula (false :: reverseBits)))
            (by simpa using hzeroBits)
        simpa [prefixSATScan, zeroFormula, hsatisfiable] using hrec
      · let oneFormula := constrainPrefixBit true index formula
        let oneCode := Encodable.encode oneFormula
        let recursiveBound :=
          prefixSATRegisterBound count (index + 1) oneFormula
            (true :: reverseBits)
        have hrecursiveBound : recursiveBound ≤ bound := by
          simpa only [zeroFormula, oneFormula, hsatisfiable,
            Bool.false_eq_true, if_false] using
            prefixSATRecursiveBound_le count index formula reverseBits
        have hrecursiveBits :
            natBitLength recursiveBound ≤ maximumBits :=
          valueBits hrecursiveBound hbits
        have honeCodeBound : oneCode ≤ recursiveBound :=
          (prefixSATCurrentBound_formula count (index + 1) oneFormula
            (true :: reverseBits)).trans
            (prefixSATCurrentBound_le_registerBound count (index + 1)
              oneFormula (true :: reverseBits))
        have honeCodeBits : natBitLength oneCode ≤ maximumBits :=
          valueBits (honeCodeBound.trans hrecursiveBound) hbits
        have honeConstruction := unitConstruction_le true index formula
        rcases honeConstruction with
          ⟨honeLiteralBound, honeCellOneBound, honeCodeOneBound,
            honeCellTwoBound, honeCodeTwoBound, honeCellThreeBound,
            honeCodeThreeBound, honeFormulaCellBound⟩
        let state18 :=
          (state17.write 10 (canonicalSatBit zeroFormula).toNat).jump 18
        let state24 := state18.jump 24
        let state34 := positiveQueryState state24 index formula
        let state35 := (state34.write 8 true.toNat).jump 35
        let state36 := (state35.write 5 true.toNat).jump 36
        let state37 := (state36.write 2 oneCode).jump 37
        let state38 := (state37.write 4 (index + 1)).jump 38
        let state5 := state38.jump 5
        rw [show
            prefixSATLoopFuel (count + 1) index formula reverseBits =
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 28) + 1 by
          simp only [prefixSATLoopFuel, zeroFormula, oneFormula,
            hsatisfiable, Bool.false_eq_true, if_false]
          omega]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 28)
          (by rfl) hpc]
        rw [if_neg (by
          rw [hcursor]
          simp only [encodeUnary]
          have := Nat.left_le_pair 1 (encodeUnary count)
          omega)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 28) state6 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 28 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 27) + 1 by omega]
        rw [run_unpairRight_instruction
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 27)
          (by rfl) rfl
          (by simp [state6, hcursor, encodeUnary])
          hcursorTailBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 27) state7 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 27 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 17) + 10 by omega]
        rw [run_negativeQuery
          (prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 17)
          maximumBits index formula state7 rfl
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hzero])
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hindex])
          (by simp [state7, state6, NPOracleState.write,
            NPOracleState.jump, hformula])
          hliteralBits hzeroBits hcellOneBits hcodeOneBits hcellTwoBits
          hcodeTwoBits hcellThreeBits hcodeThreeBits hformulaCellBits
          (by simpa [zeroCode] using hzeroCodeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 17) state17 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 17 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 16) + 1 by omega]
        rw [run_sat_instruction
          (query := zeroCode)
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 16)
          (by rfl) rfl
          (by simp [state17, negativeQueryState, zeroCode,
            zeroFormula, constrainedCode_eq])
          (by simpa [zeroCode] using hzeroCodeBits)
          (by
            cases encodedSat zeroCode
            · exact hzeroBits
            · exact honeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 16) state18 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 16 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 15) + 1 by omega]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 15)
          (by rfl) rfl]
        rw [if_pos (by simp [state18, hsatisfiable])]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 15) state24 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 15 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 5) + 10 by omega]
        rw [run_positiveQuery
          (prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 5)
          maximumBits index formula state24 rfl
          (by simp [state24, state18, state17, negativeQueryState,
            state7, state6, NPOracleState.write, NPOracleState.jump, hone])
          (by simp [state24, state18, state17, negativeQueryState,
            state7, state6, NPOracleState.write, NPOracleState.jump, hindex])
          (by simp [state24, state18, state17, negativeQueryState,
            state7, state6, NPOracleState.write, NPOracleState.jump, hformula])
          (valueBits (honeLiteralBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          hzeroBits
          (valueBits (honeCellOneBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeCodeOneBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeCellTwoBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeCodeTwoBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeCellThreeBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeCodeThreeBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (valueBits (honeFormulaCellBound.trans <|
            honeCodeBound.trans hrecursiveBound) hbits)
          (by simpa [oneCode] using honeCodeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 5) state34 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 5 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 4) + 1 by omega]
        rw [run_copy_instruction
          (value := 1)
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 4)
          (by rfl) rfl
          (by simp [state34, positiveQueryState, state24, state18,
            state17, negativeQueryState, state7, state6,
            NPOracleState.write, NPOracleState.jump, hone])
          honeBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 4) state35 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 4 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 3) + 1 by omega]
        rw [run_copy_instruction
          (value := 1)
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 3)
          (by rfl) rfl
          (by simp [state35, state34, positiveQueryState, state24,
            state18, state17, negativeQueryState, state7, state6,
            NPOracleState.write, NPOracleState.jump, hone])
          honeBits]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 3) state36 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 3 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 2) + 1 by omega]
        rw [run_copy_instruction
          (value := oneCode)
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 2)
          (by rfl) rfl
          (by simp [state36, state35, state34, positiveQueryState,
            oneCode, oneFormula])
          (by simpa [oneCode] using honeCodeBits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 2) state37 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 2 =
              (prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 1) + 1 by omega]
        rw [run_increment_instruction
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits) + 1)
          (by rfl) rfl
          (by simp [state37, state36, state35, state34,
            positiveQueryState, state24, state18, state17,
            negativeQueryState, state7, state6, NPOracleState.write,
            NPOracleState.jump, hindex])
          (valueBits
            (((prefixSATCurrentBound_index count (index + 1) oneFormula
              (true :: reverseBits)).trans
              (prefixSATCurrentBound_le_registerBound count (index + 1)
                oneFormula (true :: reverseBits))).trans hrecursiveBound)
            hbits)]
        change
          runNPOracleProgram prefixSATProgram maximumBits
              (prefixSATLoopFuel count (index + 1) oneFormula
                (true :: reverseBits) + 1) state38 =
            _
        rw [show
            prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 1 =
              prefixSATLoopFuel count (index + 1) oneFormula
                  (true :: reverseBits) + 1 by rfl]
        rw [run_branchZero_instruction
          (fuel := prefixSATLoopFuel count (index + 1) oneFormula
            (true :: reverseBits))
          (by rfl) rfl]
        rw [if_pos (by simp [state38, state37, state36, state35, state34,
          positiveQueryState, state24, state18, state17,
          negativeQueryState, state7, state6, NPOracleState.write,
          NPOracleState.jump, hzero])]
        have hrec :=
          ih (index + 1) oneFormula (true :: reverseBits)
            state5 rfl
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump])
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump, oneCode, oneFormula])
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump])
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump])
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump, hzero])
            (by simp [state5, state38, state37, state36, state35,
              state34, positiveQueryState, state24, state18, state17,
              negativeQueryState, state7, state6, NPOracleState.write,
              NPOracleState.jump, hone])
            hrecursiveBits
            (prefixSATCurrentBound_le_registerBound count (index + 1)
              oneFormula (true :: reverseBits))
            ((prefixSATCurrentBound_one count (index + 1) oneFormula
              (true :: reverseBits)).trans
              (prefixSATCurrentBound_le_registerBound count (index + 1)
                oneFormula (true :: reverseBits)))
            (by simpa using honeBits)
        simpa [prefixSATScan, zeroFormula, oneFormula, hsatisfiable] using hrec

theorem run_prefixSATProgram
    (count inputLength : ℕ) (formula : EncodedCNF) :
    runNPOracleProgram prefixSATProgram
        (prefixSATMaximumBits count formula)
        (prefixSATFuel count formula)
        (initialNPOracleState inputLength (prefixSATInput count formula)) =
      some (prefixSATOutput count formula) := by
  let bound := prefixSATRegisterBound count 0 formula []
  have hbound :
      natBitLength bound ≤ prefixSATMaximumBits count formula := by
    apply natBitLength_mono
    exact Nat.le_max_right _ _
  have hcurrent :
      prefixSATCurrentBound count 0 formula [] ≤ bound :=
    prefixSATCurrentBound_le_registerBound count 0 formula []
  have honeBound : 1 ≤ bound :=
    (prefixSATCurrentBound_one count 0 formula []).trans hcurrent
  have hcursorBits :
      natBitLength (encodeUnary count) ≤
        prefixSATMaximumBits count formula :=
    valueBits
      ((prefixSATCurrentBound_cursor count 0 formula []).trans hcurrent)
      hbound
  have hformulaBits :
      natBitLength (Encodable.encode formula) ≤
        prefixSATMaximumBits count formula :=
    valueBits
      ((prefixSATCurrentBound_formula count 0 formula []).trans hcurrent)
      hbound
  have hzeroBits :
      natBitLength 0 ≤ prefixSATMaximumBits count formula :=
    valueBits (bound := bound) (by omega) hbound
  have honeBits :
      natBitLength 1 ≤ prefixSATMaximumBits count formula :=
    valueBits honeBound hbound
  let state0 :=
    initialNPOracleState inputLength (prefixSATInput count formula)
  let state1 := (state0.write 3 (encodeUnary count)).jump 1
  let state2 := (state1.write 2 (Encodable.encode formula)).jump 2
  let state3 := (state2.write 4 0).jump 3
  let state4 := (state3.write 5 0).jump 4
  let state5 := (state4.write 11 1).jump 5
  rw [show prefixSATFuel count formula =
      (prefixSATLoopFuel count 0 formula [] + 4) + 1 by
    unfold prefixSATFuel
    omega]
  rw [run_unpairRight_instruction
    (fuel := prefixSATLoopFuel count 0 formula [] + 4)
    (by rfl) rfl
    (by simp [prefixSATInput, initialNPOracleState])
    hcursorBits]
  change
    runNPOracleProgram prefixSATProgram
        (prefixSATMaximumBits count formula)
        (prefixSATLoopFuel count 0 formula [] + 4) state1 =
      _
  rw [show prefixSATLoopFuel count 0 formula [] + 4 =
      (prefixSATLoopFuel count 0 formula [] + 3) + 1 by omega]
  rw [run_unpairLeft_instruction
    (fuel := prefixSATLoopFuel count 0 formula [] + 3)
    (by rfl) rfl
    (by
      simp [state1, state0, prefixSATInput, initialNPOracleState,
        NPOracleState.write, NPOracleState.jump])
    hformulaBits]
  change
    runNPOracleProgram prefixSATProgram
        (prefixSATMaximumBits count formula)
        (prefixSATLoopFuel count 0 formula [] + 3) state2 =
      _
  rw [show prefixSATLoopFuel count 0 formula [] + 3 =
      (prefixSATLoopFuel count 0 formula [] + 2) + 1 by omega]
  rw [run_set_instruction
    (fuel := prefixSATLoopFuel count 0 formula [] + 2)
    (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram prefixSATProgram
        (prefixSATMaximumBits count formula)
        (prefixSATLoopFuel count 0 formula [] + 2) state3 =
      _
  rw [show prefixSATLoopFuel count 0 formula [] + 2 =
      (prefixSATLoopFuel count 0 formula [] + 1) + 1 by omega]
  rw [run_set_instruction
    (fuel := prefixSATLoopFuel count 0 formula [] + 1)
    (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram prefixSATProgram
        (prefixSATMaximumBits count formula)
        (prefixSATLoopFuel count 0 formula [] + 1) state4 =
      _
  rw [show prefixSATLoopFuel count 0 formula [] + 1 =
      prefixSATLoopFuel count 0 formula [] + 1 by rfl]
  rw [run_set_instruction
    (fuel := prefixSATLoopFuel count 0 formula [])
    (by rfl) rfl honeBits]
  have hloop :=
    run_prefixSATLoop count 0 formula []
      (prefixSATMaximumBits count formula) state5 rfl
      (by simp [state5, state4, state3, state2, state1, state0,
        NPOracleState.write, NPOracleState.jump])
      (by simp [state5, state4, state3, state2, state1, state0,
        NPOracleState.write, NPOracleState.jump])
      (by simp [state5, state4, state3, state2, state1, state0,
        NPOracleState.write, NPOracleState.jump])
      (by simp [state5, state4, state3, state2, state1, state0,
        NPOracleState.write, NPOracleState.jump, latestPrefixBitCode])
      (by simp [state5, state4, state3, state2, state1, state0,
        initialNPOracleState, NPOracleState.write, NPOracleState.jump])
      (by simp [state5, NPOracleState.write, NPOracleState.jump])
      hbound
  simpa [prefixSATOutput, recoveredPrefixReverse] using hloop

structure PrefixSATRequest where
  count : ℕ
  formula : EncodedCNF

def PrefixSATRequest.length (request : PrefixSATRequest) : ℕ :=
  natBitLength (prefixSATInput request.count request.formula)

def PrefixSATRequest.code (request : PrefixSATRequest) : ℕ :=
  prefixSATInput request.count request.formula

def PrefixSATRequest.output (request : PrefixSATRequest) : ℕ :=
  prefixSATOutput request.count request.formula

theorem PrefixSATRequest.count_le_length (request : PrefixSATRequest) :
    request.count ≤ request.length := by
  have hunary :
      request.count ≤ natBitLength (encodeUnary request.count) :=
    count_le_natBitLength_encodeUnary request.count
  have hcode :
      encodeUnary request.count ≤
        prefixSATInput request.count request.formula := by
    unfold prefixSATInput
    exact Nat.right_le_pair _ _
  exact hunary.trans <| natBitLength_mono hcode

theorem PrefixSATRequest.fuel_le_exponential (request : PrefixSATRequest) :
    prefixSATFuel request.count request.formula ≤
      exponentialBudget 6 request.length := by
  have hcount := request.count_le_length
  have hlinear := prefixSATFuel_le request.count request.formula
  have hlengthPositive : 1 ≤ request.length := by
    unfold PrefixSATRequest.length natBitLength
    omega
  unfold exponentialBudget
  let length := request.length
  have hlength : 1 ≤ length := hlengthPositive
  have hpowAll :
      ∀ n : ℕ, 1 ≤ n → 30 * n + 7 ≤ 2 ^ (6 * n) := by
    intro n hn
    induction n with
    | zero =>
        omega
    | succ n ih =>
        by_cases hnzero : n = 0
        · subst n
          norm_num
        · have ihBound := ih (by omega)
          calc
            30 * (n + 1) + 7 ≤
                64 * (30 * n + 7) := by omega
            _ ≤ 64 * 2 ^ (6 * n) :=
              Nat.mul_le_mul_left 64 ihBound
            _ = 2 ^ (6 * (n + 1)) := by
              rw [Nat.mul_add, Nat.pow_add]
              norm_num
              rw [Nat.mul_comm]
  have hpow := hpowAll length hlength
  have hlinearLength :
      prefixSATFuel request.count request.formula ≤ 30 * length + 7 := by
    omega
  exact hlinearLength.trans hpow

def prefixSATBoundedRunner :
    BoundedNatProgram PrefixSATRequest PrefixSATRequest.length
      PrefixSATRequest.code where
  program := prefixSATProgram
  fuel := fun request => prefixSATFuel request.count request.formula
  registerBits := fun request =>
    prefixSATMaximumBits request.count request.formula
  fuelPositive := by
    intro request
    unfold prefixSATFuel
    omega
  registerBitsPositive := by
    intro request
    unfold prefixSATMaximumBits natBitLength
    omega
  initialBitsFit := by
    intro request
    let code := request.code
    let bound :=
      prefixSATRegisterBound request.count 0 request.formula []
    have honeBound : 1 ≤ bound := by
      exact
        (prefixSATCurrentBound_one request.count 0 request.formula []).trans
          (prefixSATCurrentBound_le_registerBound
            request.count 0 request.formula [])
    have hlength :
        request.length ≤ max code bound := by
      change natBitLength code ≤ max code bound
      by_cases hzero : code = 0
      · simp [hzero, natBitLength, honeBound]
      · apply le_trans _ (Nat.le_max_left code bound)
        unfold natBitLength
        exact Nat.log_lt_self 2 hzero
    apply natBitLength_mono
    apply max_le hlength
    exact Nat.le_max_left code bound

def prefixSATBoundedWitness :
    BoundedNatProgramWitness PrefixSATRequest PrefixSATRequest.length
      PrefixSATRequest.code PrefixSATRequest.output where
  runner := prefixSATBoundedRunner
  computes := by
    intro request
    exact run_prefixSATProgram request.count request.length request.formula

/-! ## Semantic self-reduction contract -/

@[simp] theorem formulaEval_constrainPrefixBit
    (assignment : ℕ → Bool) (value : Bool) (index : ℕ)
    (formula : EncodedCNF) :
    formulaEval assignment (constrainPrefixBit value index formula) = true ↔
      assignment index = value ∧ formulaEval assignment formula = true := by
  cases value <;> cases hbit : assignment index <;>
    simp [constrainPrefixBit, prefixUnitClause, formulaEval,
      hbit]

private theorem constrainPrefixBit_code_mono
    (value : Bool) (index : ℕ) (formula : EncodedCNF) :
    Encodable.encode formula ≤
      Encodable.encode (constrainPrefixBit value index formula) := by
  unfold constrainPrefixBit
  exact encode_list_tail_le _ _

/-- Prefix clauses preserve the SAT opcode's syntactic guard whenever the
queried variable already lies inside the original canonical code bound. -/
theorem constrainPrefixBit_wellSized
    (value : Bool) (index : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hindex : index < natBitLength (Encodable.encode formula)) :
    wellSizedCNFEncoding
        (Encodable.encode (constrainPrefixBit value index formula))
        (constrainPrefixBit value index formula) = true := by
  have hcode :
      Encodable.encode formula ≤
        Encodable.encode (constrainPrefixBit value index formula) :=
    constrainPrefixBit_code_mono value index formula
  have hindexNew :
      index <
        natBitLength
          (Encodable.encode (constrainPrefixBit value index formula)) :=
    lt_of_lt_of_le hindex (natBitLength_mono hcode)
  rw [wellSizedCNFEncoding, Bool.and_eq_true]
  constructor
  · exact decide_eq_true
      (list_length_le_encoded_bitLength
        (constrainPrefixBit value index formula))
  · rw [wellSizedCNFEncoding, Bool.and_eq_true] at hwell
    have hold := hwell.2
    unfold constrainPrefixBit
    rw [List.all_cons, Bool.and_eq_true]
    constructor
    · cases value <;>
        simp [prefixUnitClause, positiveUnit, negativeUnit, triple,
          positive, negative]
      all_goals
        simpa [constrainPrefixBit, prefixUnitClause, positiveUnit,
          negativeUnit, triple, positive, negative] using hindexNew
    · rw [List.all_eq_true] at hold ⊢
      intro clause hclause
      have hclauseOld := hold clause hclause
      rw [Bool.and_eq_true] at hclauseOld ⊢
      refine ⟨hclauseOld.1, ?_⟩
      rw [List.all_eq_true] at hclauseOld ⊢
      intro literal hliteral
      exact decide_eq_true <|
        (of_decide_eq_true (hclauseOld.2 literal hliteral)).trans_le
          (natBitLength_mono hcode)

def FormulaSatisfiable (formula : EncodedCNF) : Prop :=
  ∃ assignment : ℕ → Bool, formulaEval assignment formula = true

theorem FormulaSatisfiable.of_constrainPrefixChoices
    (index : ℕ) (formula : EncodedCNF) (choices : List Bool)
    (hsatisfiable :
      FormulaSatisfiable
        (constrainPrefixChoices index formula choices)) :
    FormulaSatisfiable formula := by
  induction choices generalizing index formula with
  | nil =>
      exact hsatisfiable
  | cons value rest ih =>
      have hconstrained :
          FormulaSatisfiable (constrainPrefixBit value index formula) :=
        ih (index + 1) (constrainPrefixBit value index formula)
          hsatisfiable
      rcases hconstrained with ⟨assignment, haccepts⟩
      exact
        ⟨assignment,
          (formulaEval_constrainPrefixBit assignment value index formula
            |>.mp haccepts).2⟩

theorem canonicalSatBit_eq_true_iff
    (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true) :
    canonicalSatBit formula = true ↔ FormulaSatisfiable formula := by
  exact encodedSat_encode_eq_true_iff formula hwell

theorem satisfiable_constrain_other
    (index : ℕ) (formula : EncodedCNF)
    (hsatisfiable : FormulaSatisfiable formula)
    (hzero : ¬FormulaSatisfiable
      (constrainPrefixBit false index formula)) :
    FormulaSatisfiable (constrainPrefixBit true index formula) := by
  rcases hsatisfiable with ⟨assignment, haccepts⟩
  refine ⟨assignment, ?_⟩
  rw [formulaEval_constrainPrefixBit]
  refine ⟨?_, haccepts⟩
  cases hbit : assignment index with
  | false =>
      exact False.elim <| hzero
        ⟨assignment,
          formulaEval_constrainPrefixBit assignment false index formula
            |>.mpr ⟨hbit, haccepts⟩⟩
  | true =>
      rfl

theorem prefixSATScan_preserves_satisfiable
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange :
      index + count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (prefixSATScan count index formula reverseBits).constrainedFormula := by
  induction count generalizing index formula reverseBits with
  | zero =>
      exact hsatisfiable
  | succ count ih =>
      let zeroFormula := constrainPrefixBit false index formula
      have hindex :
          index < natBitLength (Encodable.encode formula) := by
        omega
      have hzeroWell :
          wellSizedCNFEncoding (Encodable.encode zeroFormula)
              zeroFormula = true := by
        exact constrainPrefixBit_wellSized false index formula hwell hindex
      have hzeroRange :
          index + 1 + count ≤
            natBitLength (Encodable.encode zeroFormula) := by
        have hmono :=
          natBitLength_mono
            (constrainPrefixBit_code_mono false index formula)
        have hmono' :
            natBitLength (Encodable.encode formula) ≤
              natBitLength (Encodable.encode zeroFormula) := by
          simpa only [zeroFormula] using hmono
        omega
      by_cases hzero : canonicalSatBit zeroFormula = true
      · have hzeroSat : FormulaSatisfiable zeroFormula :=
          (canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mp hzero
        have hrec :=
          ih (index + 1) zeroFormula (false :: reverseBits)
            hzeroWell hzeroRange hzeroSat
        simpa [prefixSATScan, zeroFormula, hzero] using hrec
      · let oneFormula := constrainPrefixBit true index formula
        have hzeroNotSat : ¬FormulaSatisfiable zeroFormula := by
          intro hzeroSat
          exact hzero
            ((canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mpr
              hzeroSat)
        have honeSat : FormulaSatisfiable oneFormula :=
          satisfiable_constrain_other index formula hsatisfiable hzeroNotSat
        have honeWell :
            wellSizedCNFEncoding (Encodable.encode oneFormula)
                oneFormula = true := by
          exact constrainPrefixBit_wellSized true index formula hwell hindex
        have honeRange :
            index + 1 + count ≤
              natBitLength (Encodable.encode oneFormula) := by
          have hmono :=
            natBitLength_mono
              (constrainPrefixBit_code_mono true index formula)
          have hmono' :
              natBitLength (Encodable.encode formula) ≤
                natBitLength (Encodable.encode oneFormula) := by
            simpa only [oneFormula] using hmono
          omega
        have hrec :=
          ih (index + 1) oneFormula (true :: reverseBits)
            honeWell honeRange honeSat
        simpa [prefixSATScan, zeroFormula, oneFormula, hzero] using hrec

theorem recoveredPrefixFormula_satisfiable
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (prefixSATScan count 0 formula []).constrainedFormula := by
  exact prefixSATScan_preserves_satisfiable count 0 formula []
    hwell (by simpa using hrange) hsatisfiable

theorem recoveredPrefix_satisfiable
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (constrainPrefixChoices 0 formula (recoveredPrefix count formula)) := by
  unfold recoveredPrefix
  rw [← prefixSATScan_constrainedFormula_eq count 0 formula []]
  exact recoveredPrefixFormula_satisfiable count formula
    hwell hrange hsatisfiable

/-- The fixed zero-first self-reduction returns the lexicographically first
satisfiable prefix.  The range hypothesis is exactly what keeps every dynamic
SAT query inside the interpreter's canonical syntactic guard. -/
theorem prefixSATChoices_lexLeast
    (count index : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange :
      index + count ≤ natBitLength (Encodable.encode formula))
    (candidate : List Bool)
    (hlength : candidate.length = count)
    (hcandidate :
      FormulaSatisfiable
        (constrainPrefixChoices index formula candidate)) :
    CanonicalBoolListLE
      (prefixSATChoices count index formula) candidate := by
  induction count generalizing index formula candidate with
  | zero =>
      have hc : candidate = [] := List.eq_nil_of_length_eq_zero hlength
      subst candidate
      exact le_refl []
  | succ count ih =>
      cases candidate with
      | nil =>
          simp at hlength
      | cons candidateHead candidateTail =>
          have htailLength : candidateTail.length = count := by
            simp only [List.length_cons] at hlength
            omega
          let zeroFormula := constrainPrefixBit false index formula
          have hindex :
              index < natBitLength (Encodable.encode formula) := by
            omega
          have hzeroWell :
              wellSizedCNFEncoding (Encodable.encode zeroFormula)
                  zeroFormula = true :=
            constrainPrefixBit_wellSized false index formula hwell hindex
          have hzeroRange :
              index + 1 + count ≤
                natBitLength (Encodable.encode zeroFormula) := by
            have hmono :
                natBitLength (Encodable.encode formula) ≤
                  natBitLength (Encodable.encode zeroFormula) := by
              simpa only [zeroFormula] using
                natBitLength_mono
                  (constrainPrefixBit_code_mono false index formula)
            omega
          by_cases hzero : canonicalSatBit zeroFormula = true
          · cases candidateHead with
            | false =>
                have htail :=
                  ih (index + 1) zeroFormula hzeroWell hzeroRange
                    candidateTail htailLength hcandidate
                simpa only [prefixSATChoices, zeroFormula, hzero, if_pos,
                  CanonicalBoolListLE] using
                    (List.cons_le_cons false htail)
            | true =>
                simp only [prefixSATChoices, zeroFormula, hzero, if_pos,
                  CanonicalBoolListLE]
                exact le_of_lt (List.Lex.rel (by decide))
          · cases candidateHead with
            | false =>
                exfalso
                have hzeroSat : FormulaSatisfiable zeroFormula := by
                  exact FormulaSatisfiable.of_constrainPrefixChoices
                    (index + 1) zeroFormula candidateTail hcandidate
                exact hzero
                  ((canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mpr
                    hzeroSat)
            | true =>
                let oneFormula := constrainPrefixBit true index formula
                have honeWell :
                    wellSizedCNFEncoding (Encodable.encode oneFormula)
                        oneFormula = true :=
                  constrainPrefixBit_wellSized true index formula hwell hindex
                have honeRange :
                    index + 1 + count ≤
                      natBitLength (Encodable.encode oneFormula) := by
                  have hmono :
                      natBitLength (Encodable.encode formula) ≤
                        natBitLength (Encodable.encode oneFormula) := by
                    simpa only [oneFormula] using
                      natBitLength_mono
                        (constrainPrefixBit_code_mono true index formula)
                  omega
                have htail :=
                  ih (index + 1) oneFormula honeWell honeRange
                    candidateTail htailLength hcandidate
                simpa only [prefixSATChoices, zeroFormula, oneFormula,
                  hzero, Bool.false_eq_true, if_false,
                  CanonicalBoolListLE] using
                    (List.cons_le_cons true htail)

theorem recoveredPrefix_lexLeast
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (candidate : List Bool)
    (hlength : candidate.length = count)
    (hcandidate :
      FormulaSatisfiable
        (constrainPrefixChoices 0 formula candidate)) :
    CanonicalBoolListLE (recoveredPrefix count formula) candidate := by
  exact prefixSATChoices_lexLeast count 0 formula hwell
    (by simpa using hrange) candidate hlength hcandidate

@[simp] theorem prefixSATOutput_eq_latestPrefixBitCode
    (count : ℕ) (formula : EncodedCNF) :
    prefixSATOutput count formula =
      latestPrefixBitCode (recoveredPrefix count formula).reverse := by
  simp only [prefixSATOutput, recoveredPrefixReverse_eq]

end NearCubicWires.CanonicalSATSelfReduction
