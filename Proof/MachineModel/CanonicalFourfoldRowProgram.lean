import Proof.Circuits.CanonicalWitnessCodec
import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.Foundations.CanonicalBinaryProgram
import Proof.MachineModel.FixedAccuracyDenominatorProgram
import Proof.MachineModel.FourfoldRequestEnvelopeProgram
import Proof.Supplier.SupplierEstimator

/-!
# Canonical executable fourfold rows

This module fixes the raw ABI and the finite-index decoders used by the shared
normalized estimator.  Production code enumerates the explicit mixed-radix
indices below; the `Fintype` views in `SupplierEstimator` remain specifications
used only to prove that this enumeration is the same finite probability space.
-/

namespace NearCubicWires.CanonicalFourfoldRowProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierRadix
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge
open NearCubicWires.VerifiedLinker

/-! ## Computable arithmetic and characteristic-two normalization -/

/-- Integer ceiling of the square root.  Unlike `Real.sqrt` followed by
`Nat.ceil`, this definition is directly executable and uses the verified
floor-square-root primitive only once. -/
def natCeilSqrt (value : ℕ) : ℕ :=
  let root := Nat.sqrt value
  if root * root = value then root else root + 1

theorem le_natCeilSqrt_sq (value : ℕ) :
    value ≤ natCeilSqrt value * natCeilSqrt value := by
  change value ≤
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1) *
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1)
  split
  · rename_i hperfect
    rw [hperfect]
  · exact (Nat.lt_succ_sqrt value).le

theorem sq_lt_of_lt_natCeilSqrt
    {candidate value : ℕ} (hcandidate : candidate < natCeilSqrt value) :
    candidate * candidate < value := by
  change candidate <
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1) at hcandidate
  split at hcandidate
  · rename_i hperfect
    exact hperfect ▸ Nat.mul_self_lt_mul_self hcandidate
  · rename_i himperfect
    have hcandidateRoot : candidate ≤ Nat.sqrt value := by omega
    have hsquareLe :
        candidate * candidate ≤ Nat.sqrt value * Nat.sqrt value :=
      Nat.mul_self_le_mul_self hcandidateRoot
    have hrootSquareLe :
        Nat.sqrt value * Nat.sqrt value ≤ value :=
      Nat.sqrt_le value
    have hrootSquareNe :
        Nat.sqrt value * Nat.sqrt value ≠ value :=
      himperfect
    exact hsquareLe.trans_lt
      (lt_of_le_of_ne hrootSquareLe hrootSquareNe)

theorem natCeilSqrt_eq_ceil_real_sqrt (value : ℕ) :
    natCeilSqrt value = ⌈Real.sqrt (value : ℝ)⌉₊ := by
  apply le_antisymm
  · by_contra hle
    have hstrict :
        ⌈Real.sqrt (value : ℝ)⌉₊ < natCeilSqrt value :=
      Nat.lt_of_not_ge hle
    have hsquareStrict :=
      sq_lt_of_lt_natCeilSqrt hstrict
    have hsqrtUpper :
        Real.sqrt (value : ℝ) ≤
          (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hsquareUpper :
        (value : ℝ) ≤
          (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) ^ 2 :=
      (Real.sqrt_le_left (by positivity)).mp hsqrtUpper
    have hsquareUpperNat :
        value ≤
          ⌈Real.sqrt (value : ℝ)⌉₊ *
            ⌈Real.sqrt (value : ℝ)⌉₊ := by
      have hsquareUpperMul :
          (value : ℝ) ≤
            (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) *
              (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) := by
        simpa [pow_two] using hsquareUpper
      exact_mod_cast hsquareUpperMul
    exact (not_lt_of_ge hsquareUpperNat) hsquareStrict
  · apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hsquare :
        (value : ℝ) ≤
          (natCeilSqrt value : ℝ) *
            (natCeilSqrt value : ℝ) := by
      exact_mod_cast le_natCeilSqrt_sq value
    simpa [pow_two] using hsquare

/-- Taking an integer ceiling before exact natural ceiling division does not
change the final ceiling.  This is the key bridge from real schedule notation
to the executable integer implementation. -/
theorem ceil_ceilDiv_eq_ceil_div
    (value : ℝ)
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    ⌈value⌉₊ ⌈/⌉ denominator =
      ⌈value / denominator⌉₊ := by
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hdenominator).mpr
    apply Nat.ceil_le.mpr
    have hdenominatorReal : (0 : ℝ) < denominator := by
      exact_mod_cast hdenominator
    have hquotient :
        value / (denominator : ℝ) ≤
          (⌈value / denominator⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hproduct :
        value ≤
          (⌈value / denominator⌉₊ : ℝ) *
            (denominator : ℝ) :=
      (div_le_iff₀ hdenominatorReal).mp hquotient
    have hproductNat :
        ⌈value / denominator⌉₊ * denominator ≥
          ⌈value⌉₊ := by
      apply Nat.ceil_le.mpr
      simpa only [Nat.cast_mul] using hproduct
    simpa [mul_comm] using hproductNat
  · apply Nat.ceil_le.mpr
    have hceilProduct :
        ⌈value⌉₊ ≤
          denominator * (⌈value⌉₊ ⌈/⌉ denominator) :=
      (ceilDiv_le_iff_le_mul hdenominator).mp le_rfl
    have hvalueCeil : value ≤ (⌈value⌉₊ : ℝ) := Nat.le_ceil _
    have hdenominatorReal : (0 : ℝ) < denominator := by
      exact_mod_cast hdenominator
    apply (div_le_iff₀ hdenominatorReal).mpr
    have hproductReal :
        value ≤
          (denominator : ℝ) *
            (⌈value⌉₊ ⌈/⌉ denominator : ℕ) :=
      hvalueCeil.trans (by exact_mod_cast hceilProduct)
    simpa [mul_comm] using hproductReal

/-- Executable form of the graded window.  The square root is rounded only
after scaling by 64, then divided with the canonical natural ceiling
division.  This is algebraically the same order of rounding as the real
formula in `gradedWindow`; its refinement theorem below is the only bridge
back to reals. -/
def executableGradedWindow
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) : ℕ :=
  64 +
    (natCeilSqrt (64 ^ 2 * activeBound) ⌈/⌉
      (2 ^ (level.val / 3))
    )

theorem executableGradedWindow_pos
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) :
    0 < executableGradedWindow activeBound level := by
  unfold executableGradedWindow
  omega

theorem executableGradedWindow_eq_gradedWindow
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) :
    executableGradedWindow activeBound level =
      gradedWindow activeBound level := by
  let denominator := 2 ^ (level.val / 3)
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hdenominatorCast :
      (denominator : ℝ) =
        (2 : ℝ) ^ (level.val / 3) := by
    dsimp [denominator]
    push_cast
    rfl
  have hscaledSqrt :
      Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) =
        64 * Real.sqrt (activeBound : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (by positivity)]
    norm_num
  have hschedule :
      (64 : ℝ) *
          (Real.sqrt activeBound / denominator + 1) =
        Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
            denominator +
          64 := by
    rw [hscaledSqrt]
    ring
  unfold executableGradedWindow gradedWindow
  rw [← hdenominatorCast]
  change
    64 +
        (natCeilSqrt (64 ^ 2 * activeBound) ⌈/⌉ denominator) =
      ⌈(64 : ℝ) *
        (Real.sqrt activeBound / denominator + 1)⌉₊
  rw [natCeilSqrt_eq_ceil_real_sqrt]
  rw [ceil_ceilDiv_eq_ceil_div
    (Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ))
    denominator hdenominator]
  rw [hschedule]
  change
    64 +
        ⌈Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
          (denominator : ℝ)⌉₊ =
      ⌈Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
          (denominator : ℝ) + ((64 : ℕ) : ℝ)⌉₊
  rw [Nat.ceil_add_natCast (by positivity) 64]
  omega

/-- A monomial is a sorted list of variable codes.  Repetition is retained:
it represents an exponent, while ordering is erased by multiplication. -/
abbrev EncodedGF2Monomial := List ℕ

/-- A structural polynomial records one entry per coefficient occurrence.
Duplicate monomials therefore cancel when the list is normalized over `𝔽₂`. -/
abbrev StructuralGF2Polynomial := List EncodedGF2Monomial

def normalizeEncodedGF2Monomial
    (monomial : EncodedGF2Monomial) : EncodedGF2Monomial :=
  monomial.insertionSort (· ≤ ·)

/-- Toggle one normalized formal monomial.  A `Finset` is the canonical normal
form for coefficients in `𝔽₂`: inserting a second copy cancels the first. -/
def toggleGF2Monomial
    (monomial : EncodedGF2Monomial)
    (polynomial : Finset EncodedGF2Monomial) :
    Finset EncodedGF2Monomial :=
  if monomial ∈ polynomial then
    polynomial.erase monomial
  else
    insert monomial polynomial

/-- Structural normalization, independent of `MvPolynomial.support` and hence
fully executable. -/
def normalizeGF2Monomials :
    StructuralGF2Polynomial → Finset EncodedGF2Monomial
  | [] => ∅
  | monomial :: monomials =>
      toggleGF2Monomial (normalizeEncodedGF2Monomial monomial)
        (normalizeGF2Monomials monomials)

def structuralGF2Zero : StructuralGF2Polynomial :=
  []

def structuralGF2One : StructuralGF2Polynomial :=
  [[]]

def structuralGF2Add
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  left ++ right

def structuralGF2Mul
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  left.flatMap fun leftMonomial =>
    right.map fun rightMonomial => leftMonomial ++ rightMonomial

def structuralGF2Scale
    (coefficient : ZMod 2)
    (polynomial : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  if coefficient = 0 then [] else polynomial

/-- Evaluation is deliberately defined on the structural monomial list, not
through `MvPolynomial.support`.  Multiplicity in the list is coefficient
multiplicity and the final odd test is therefore exactly reduction in
characteristic two. -/
def evaluateStructuralGF2
    (assignment : ℕ → Bool)
    (polynomial : StructuralGF2Polynomial) : Bool :=
  exactPolynomialValue
    (fun code (_row : Unit) (_column : Unit) => assignment code)
    polynomial () ()

@[simp] theorem evaluateStructuralGF2_zero
    (assignment : ℕ → Bool) :
    evaluateStructuralGF2 assignment structuralGF2Zero = false := by
  simp [evaluateStructuralGF2, structuralGF2Zero,
    exactPolynomialValue, polynomialOccurrenceCount]

@[simp] theorem evaluateStructuralGF2_one
    (assignment : ℕ → Bool) :
    evaluateStructuralGF2 assignment structuralGF2One = true := by
  simp [evaluateStructuralGF2, structuralGF2One,
    exactPolynomialValue, polynomialOccurrenceCount, exactMonomialValue]

@[simp] theorem mem_toggleGF2Monomial
    (candidate monomial : EncodedGF2Monomial)
    (polynomial : Finset EncodedGF2Monomial) :
    candidate ∈ toggleGF2Monomial monomial polynomial ↔
      (candidate = monomial ∧ candidate ∉ polynomial) ∨
        (candidate ≠ monomial ∧ candidate ∈ polynomial) := by
  by_cases hmember : monomial ∈ polynomial
  · by_cases hequal : candidate = monomial
    · subst candidate
      simp [toggleGF2Monomial, hmember]
    · simp [toggleGF2Monomial, hmember, hequal]
  · by_cases hequal : candidate = monomial
    · subst candidate
      simp [toggleGF2Monomial, hmember]
    · simp [toggleGF2Monomial, hmember, hequal]

theorem mem_normalizeGF2Monomials_iff_odd
    (candidate : EncodedGF2Monomial)
    (monomials : StructuralGF2Polynomial)
    (hnormalized :
      ∀ monomial ∈ monomials,
        normalizeEncodedGF2Monomial monomial = monomial) :
    candidate ∈ normalizeGF2Monomials monomials ↔
      Odd (monomials.count candidate) := by
  induction monomials with
  | nil => simp [normalizeGF2Monomials]
  | cons monomial monomials ih =>
      have hhead := hnormalized monomial (by simp)
      have htail :
          ∀ candidate ∈ monomials,
            normalizeEncodedGF2Monomial candidate = candidate := by
        intro candidate hcandidate
        exact hnormalized candidate (by simp [hcandidate])
      rw [normalizeGF2Monomials, hhead, mem_toggleGF2Monomial, ih htail]
      by_cases hequal : monomial = candidate
      · subst monomial
        simp only [List.count_cons_self]
        rw [Nat.odd_add_one]
        simp
      · have hcandidate : candidate ≠ monomial := Ne.symm hequal
        simp [hequal, hcandidate]

/-! ## Executable structural list-polynomial compiler -/

def encodeListLiteralVariable
    {depth population : ℕ} :
    ListLiteralVariable depth population → ℕ
  | .terminal coordinate => Nat.pair 0 coordinate.val
  | .delta level slot => Nat.pair (level.val + 1) slot.val

def decodeListLiteralVariable
    (depth population code : ℕ) :
    Option (ListLiteralVariable depth population) :=
  let tagged := Nat.unpair code
  if _hterminal : tagged.1 = 0 then
    if hcoordinate : tagged.2 < population then
      some (.terminal ⟨tagged.2, hcoordinate⟩)
    else
      none
  else if hlevel : tagged.1 - 1 < depth then
    if hslot : tagged.2 < 2 * population then
      some (.delta ⟨tagged.1 - 1, hlevel⟩ ⟨tagged.2, hslot⟩)
    else
      none
  else
    none

@[simp] theorem decodeListLiteralVariable_encode
    {depth population : ℕ}
    (literal : ListLiteralVariable depth population) :
    decodeListLiteralVariable depth population
        (encodeListLiteralVariable literal) =
      some literal := by
  cases literal with
  | terminal coordinate =>
      simp [encodeListLiteralVariable, decodeListLiteralVariable,
        Nat.unpair_pair, coordinate.isLt]
  | delta level slot =>
      simp [encodeListLiteralVariable, decodeListLiteralVariable,
        Nat.unpair_pair, level.isLt, slot.isLt]

theorem encodeListLiteralVariable_injective
    {depth population : ℕ} :
    Function.Injective
      (@encodeListLiteralVariable depth population) := by
  intro left right hequal
  have := congrArg
    (decodeListLiteralVariable depth population) hequal
  rw [decodeListLiteralVariable_encode,
    decodeListLiteralVariable_encode] at this
  exact Option.some.inj this

def encodedListLiteralBooleanAssignment
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) : Bool :=
  match decodeListLiteralVariable depth population code with
  | some literal =>
      listLiteralBooleanAssignment active label seed literal
  | none => false

@[simp] theorem encodedListLiteralBooleanAssignment_encode
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (literal : ListLiteralVariable depth population) :
    encodedListLiteralBooleanAssignment (depth := depth) active label seed
        (encodeListLiteralVariable literal) =
      listLiteralBooleanAssignment active label seed literal := by
  simp [encodedListLiteralBooleanAssignment]

/-- Proof-only denotation of one encoded monomial.  Invalid variable codes map
to zero, matching the total Boolean decoder; production evaluation never calls
this noncomputable `MvPolynomial` view. -/
noncomputable def interpretEncodedGF2Monomial
    {depth population : ℕ} (monomial : EncodedGF2Monomial) :
    MvPolynomial (ListLiteralVariable depth population) (ZMod 2) :=
  (monomial.map fun code =>
    match decodeListLiteralVariable depth population code with
    | some literal => MvPolynomial.X literal
    | none => 0).prod

/-- Proof-only denotation of the executable occurrence list. -/
noncomputable def interpretStructuralGF2
    {depth population : ℕ} (polynomial : StructuralGF2Polynomial) :
    MvPolynomial (ListLiteralVariable depth population) (ZMod 2) :=
  (polynomial.map interpretEncodedGF2Monomial).sum

theorem aeval_interpretEncodedGF2Monomial
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (monomial : EncodedGF2Monomial) :
    MvPolynomial.aeval
        (fun literal => ((assignment literal).toNat : ZMod 2))
        (interpretEncodedGF2Monomial monomial) =
      ((monomial.all fun code =>
        match decodeListLiteralVariable depth population code with
        | some literal => assignment literal
        | none => false).toNat : ZMod 2) := by
  induction monomial with
  | nil =>
      simp [interpretEncodedGF2Monomial]
  | cons code monomial ih =>
      change
        MvPolynomial.aeval
            (fun literal => ((assignment literal).toNat : ZMod 2))
            ((match decodeListLiteralVariable depth population code with
              | some literal => MvPolynomial.X literal
              | none => 0) *
              interpretEncodedGF2Monomial monomial) =
          ((match decodeListLiteralVariable depth population code with
            | some literal => assignment literal
            | none => false) &&
            (monomial.all fun candidate =>
              match decodeListLiteralVariable depth population candidate with
              | some literal => assignment literal
              | none => false)).toNat
      rw [map_mul, ih]
      cases hdecode :
          decodeListLiteralVariable depth population code with
      | none => simp
      | some literal =>
          cases hvalue : assignment literal <;> simp [hvalue]

theorem aeval_interpretStructuralGF2
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (polynomial : StructuralGF2Polynomial) :
    MvPolynomial.aeval
        (fun literal => ((assignment literal).toNat : ZMod 2))
        (interpretStructuralGF2 polynomial) =
      (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) =>
          match decodeListLiteralVariable depth population code with
          | some literal => assignment literal
          | none => false)
        polynomial () () : ZMod 2) := by
  induction polynomial with
  | nil =>
      simp [interpretStructuralGF2, polynomialOccurrenceCount]
  | cons monomial polynomial ih =>
      change
        MvPolynomial.aeval
            (fun literal => ((assignment literal).toNat : ZMod 2))
            (interpretEncodedGF2Monomial monomial +
              interpretStructuralGF2 polynomial) =
          ((exactMonomialValue
              (fun code (_row : Unit) (_column : Unit) =>
                match decodeListLiteralVariable depth population code with
                | some literal => assignment literal
                | none => false)
              monomial () ()).toNat +
            polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) =>
                match decodeListLiteralVariable depth population code with
                | some literal => assignment literal
                | none => false)
              polynomial () () : ℕ)
      rw [map_add, aeval_interpretEncodedGF2Monomial, ih]
      unfold exactMonomialValue
      rw [Nat.cast_add]

theorem evaluateStructuralGF2_eq_aeval
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2
        (fun code =>
          match decodeListLiteralVariable depth population code with
          | some literal => assignment literal
          | none => false)
        polynomial =
      decide
        (MvPolynomial.aeval
          (fun literal => ((assignment literal).toNat : ZMod 2))
          (interpretStructuralGF2 polynomial) = 1) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [aeval_interpretStructuralGF2]
  exact decide_eq_decide.mpr ZMod.natCast_eq_one_iff_odd.symm

def structuralGF2Sum
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.flatten

@[simp] theorem interpretStructuralGF2_zero
    {depth population : ℕ} :
    interpretStructuralGF2
        (depth := depth) (population := population) structuralGF2Zero =
      0 := by
  simp [interpretStructuralGF2, structuralGF2Zero]

@[simp] theorem interpretStructuralGF2_one
    {depth population : ℕ} :
    interpretStructuralGF2
        (depth := depth) (population := population) structuralGF2One =
      1 := by
  simp [interpretStructuralGF2, interpretEncodedGF2Monomial,
    structuralGF2One]

@[simp] theorem interpretEncodedGF2Monomial_append
    {depth population : ℕ}
    (left right : EncodedGF2Monomial) :
    interpretEncodedGF2Monomial
        (depth := depth) (population := population) (left ++ right) =
      interpretEncodedGF2Monomial left *
        interpretEncodedGF2Monomial right := by
  simp [interpretEncodedGF2Monomial, List.map_append, List.prod_append]

@[simp] theorem interpretStructuralGF2_add
    {depth population : ℕ}
    (left right : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Add left right) =
      interpretStructuralGF2 left + interpretStructuralGF2 right := by
  simp [interpretStructuralGF2, structuralGF2Add, List.map_append,
    List.sum_append]

private theorem interpretStructuralGF2_map_append
    {depth population : ℕ}
    (monomial : EncodedGF2Monomial)
    (polynomial : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (polynomial.map fun right => monomial ++ right) =
      interpretEncodedGF2Monomial monomial *
        interpretStructuralGF2 polynomial := by
  induction polynomial with
  | nil =>
      simp [interpretStructuralGF2]
  | cons right polynomial ih =>
      change
        interpretEncodedGF2Monomial (monomial ++ right) +
            interpretStructuralGF2
              (polynomial.map fun candidate => monomial ++ candidate) =
          interpretEncodedGF2Monomial monomial *
            (interpretEncodedGF2Monomial right +
              interpretStructuralGF2 polynomial)
      rw [interpretEncodedGF2Monomial_append, ih]
      ring

@[simp] theorem interpretStructuralGF2_mul
    {depth population : ℕ}
    (left right : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Mul left right) =
      interpretStructuralGF2 left * interpretStructuralGF2 right := by
  induction left with
  | nil =>
      simp [structuralGF2Mul, interpretStructuralGF2]
  | cons monomial left ih =>
      change
        interpretStructuralGF2
            ((right.map fun rightMonomial => monomial ++ rightMonomial) ++
              structuralGF2Mul left right) =
          (interpretEncodedGF2Monomial monomial +
              interpretStructuralGF2 left) *
            interpretStructuralGF2 right
      rw [show
        interpretStructuralGF2
            ((right.map fun rightMonomial => monomial ++ rightMonomial) ++
              structuralGF2Mul left right) =
          interpretStructuralGF2
              (right.map fun rightMonomial => monomial ++ rightMonomial) +
            interpretStructuralGF2 (structuralGF2Mul left right) by
              exact interpretStructuralGF2_add _ _]
      rw [interpretStructuralGF2_map_append, ih]
      ring

private theorem zmodTwo_eq_one_of_ne_zero
    (coefficient : ZMod 2) (hnonzero : coefficient ≠ 0) :
    coefficient = 1 := by
  apply (ZMod.val_eq_one (by norm_num) coefficient).mp
  have hvalueLt := ZMod.val_lt coefficient
  have hvalueNe : coefficient.val ≠ 0 := by
    intro hzero
    exact hnonzero ((ZMod.val_eq_zero coefficient).mp hzero)
  omega

@[simp] theorem interpretStructuralGF2_scale
    {depth population : ℕ}
    (coefficient : ZMod 2) (polynomial : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Scale coefficient polynomial) =
      MvPolynomial.C coefficient * interpretStructuralGF2 polynomial := by
  by_cases hzero : coefficient = 0
  · subst coefficient
    rw [show structuralGF2Scale (0 : ZMod 2) polynomial =
      structuralGF2Zero by simp [structuralGF2Scale, structuralGF2Zero]]
    rw [interpretStructuralGF2_zero]
    simp
  · rw [zmodTwo_eq_one_of_ne_zero coefficient hzero]
    simp [structuralGF2Scale]

@[simp] theorem interpretStructuralGF2_sum
    {depth population : ℕ}
    (polynomials : List StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Sum polynomials) =
      (polynomials.map interpretStructuralGF2).sum := by
  induction polynomials with
  | nil =>
      simp [structuralGF2Sum, interpretStructuralGF2]
  | cons polynomial polynomials ih =>
      change
        interpretStructuralGF2
            (polynomial ++ structuralGF2Sum polynomials) =
          interpretStructuralGF2 polynomial +
            (polynomials.map interpretStructuralGF2).sum
      rw [show
        interpretStructuralGF2
            (polynomial ++ structuralGF2Sum polynomials) =
          interpretStructuralGF2 polynomial +
            interpretStructuralGF2 (structuralGF2Sum polynomials) by
              exact interpretStructuralGF2_add _ _]
      rw [ih]

def structuralGF2Variable (code : ℕ) : StructuralGF2Polynomial :=
  [[code]]

/-- Boolean negation in algebraic normal form over `𝔽₂`. -/
def structuralGF2Not
    (polynomial : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Add structuralGF2One polynomial

/-- Boolean disjunction in algebraic normal form:
`x ∨ y = x + y + xy` over `𝔽₂`. -/
def structuralGF2Or
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Add (structuralGF2Add left right)
    (structuralGF2Mul left right)

/-- Conjunction of a finite, explicitly ordered polynomial family. -/
def structuralGF2Product
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.foldr structuralGF2Mul structuralGF2One

/-- Disjunction of a finite, explicitly ordered polynomial family. -/
def structuralGF2Disjunction
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.foldr structuralGF2Or structuralGF2Zero

@[simp] theorem exactMonomialValue_append_structural
    (assignment : ℕ → Bool)
    (left right : EncodedGF2Monomial) :
    exactMonomialValue
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (left ++ right) () () =
      (exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () &&
        exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () ()) := by
  simp [exactMonomialValue, List.all_append]

theorem polynomialOccurrenceCount_structuralGF2Add
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (structuralGF2Add left right) () () =
      polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () +
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  simp [polynomialOccurrenceCount, structuralGF2Add,
    List.map_append, List.sum_append]

private theorem polynomialOccurrenceCount_map_append
    (assignment : ℕ → Bool)
    (left : EncodedGF2Monomial)
    (right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (right.map fun rightMonomial => left ++ rightMonomial) () () =
      (exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () ()).toNat *
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  induction right with
  | nil =>
      simp [polynomialOccurrenceCount]
  | cons right rightPolynomial ih =>
      simp only [List.map_cons, polynomialOccurrenceCount, List.sum_cons]
      rw [exactMonomialValue_append_structural]
      have htail :
          (rightPolynomial.map
              ((fun monomial =>
                (exactMonomialValue
                  (fun code (_row : Unit) (_column : Unit) =>
                    assignment code)
                  monomial () ()).toNat) ∘
                fun rightMonomial => left ++ rightMonomial)).sum =
            (exactMonomialValue
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              left () ()).toNat *
              (rightPolynomial.map
                (fun rightMonomial =>
                  (exactMonomialValue
                    (fun code (_row : Unit) (_column : Unit) =>
                      assignment code)
                    rightMonomial () ()).toNat)).sum := by
        unfold polynomialOccurrenceCount at ih
        rw [List.map_map] at ih
        exact ih
      rw [List.map_map]
      rw [htail]
      cases
          exactMonomialValue
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            left () () <;>
        simp

theorem polynomialOccurrenceCount_structuralGF2Mul
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (structuralGF2Mul left right) () () =
      polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () *
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  induction left with
  | nil =>
      simp [structuralGF2Mul, polynomialOccurrenceCount]
  | cons leftMonomial leftPolynomial ih =>
      change
        polynomialOccurrenceCount
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            ((right.map fun rightMonomial =>
                leftMonomial ++ rightMonomial) ++
              structuralGF2Mul leftPolynomial right) () () =
          polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              (leftMonomial :: leftPolynomial) () () *
            polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              right () ()
      change
        polynomialOccurrenceCount
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            (structuralGF2Add
              (right.map fun rightMonomial =>
                leftMonomial ++ rightMonomial)
              (structuralGF2Mul leftPolynomial right)) () () =
          _
      rw [polynomialOccurrenceCount_structuralGF2Add]
      rw [polynomialOccurrenceCount_map_append, ih]
      unfold polynomialOccurrenceCount
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.add_mul]

@[simp] theorem evaluateStructuralGF2_variable
    (assignment : ℕ → Bool) (code : ℕ) :
    evaluateStructuralGF2 assignment (structuralGF2Variable code) =
      assignment code := by
  cases hvalue : assignment code <;>
    simp [evaluateStructuralGF2, exactPolynomialValue,
      polynomialOccurrenceCount, exactMonomialValue,
      structuralGF2Variable, hvalue]

@[simp] theorem evaluateStructuralGF2_add
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Add left right) =
      (evaluateStructuralGF2 assignment left !=
        evaluateStructuralGF2 assignment right) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [polynomialOccurrenceCount_structuralGF2Add]
  simp only [Nat.odd_add, ← Nat.not_odd_iff_even]
  by_cases hleft :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        left () ())
  <;> by_cases hright :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        right () ())
  <;> simp [hleft, hright]

@[simp] theorem evaluateStructuralGF2_mul
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Mul left right) =
      (evaluateStructuralGF2 assignment left &&
        evaluateStructuralGF2 assignment right) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [polynomialOccurrenceCount_structuralGF2Mul]
  simp only [Nat.odd_mul]
  by_cases hleft :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        left () ())
  <;> by_cases hright :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        right () ())
  <;> simp [hleft, hright]

@[simp] theorem evaluateStructuralGF2_not
    (assignment : ℕ → Bool)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Not polynomial) =
      !(evaluateStructuralGF2 assignment polynomial) := by
  simp [structuralGF2Not]

@[simp] theorem evaluateStructuralGF2_or
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Or left right) =
      (evaluateStructuralGF2 assignment left ||
        evaluateStructuralGF2 assignment right) := by
  cases hleft : evaluateStructuralGF2 assignment left <;>
    cases hright : evaluateStructuralGF2 assignment right <;>
      simp [structuralGF2Or, hleft, hright]

@[simp] theorem evaluateStructuralGF2_product
    (assignment : ℕ → Bool)
    (polynomials : List StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2Product polynomials) =
      polynomials.all (evaluateStructuralGF2 assignment) := by
  induction polynomials with
  | nil => simp [structuralGF2Product]
  | cons polynomial polynomials ih =>
      change
        evaluateStructuralGF2 assignment
            (structuralGF2Mul polynomial
              (structuralGF2Product polynomials)) =
          _
      rw [evaluateStructuralGF2_mul, ih]
      simp

@[simp] theorem evaluateStructuralGF2_disjunction
    (assignment : ℕ → Bool)
    (polynomials : List StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2Disjunction polynomials) =
      polynomials.any (evaluateStructuralGF2 assignment) := by
  induction polynomials with
  | nil =>
      simp [structuralGF2Disjunction]
  | cons polynomial polynomials ih =>
      change
        evaluateStructuralGF2 assignment
            (structuralGF2Or polynomial
              (structuralGF2Disjunction polynomials)) =
          _
      rw [evaluateStructuralGF2_or, ih]
      simp

/-- Capture-avoiding composition of executable structural polynomials.
Variable codes remain natural-number ABI values; `atom` is the sole lowering
map and every source monomial occurrence is retained. -/
def structuralGF2Substitute
    (atom : ℕ → StructuralGF2Polynomial) :
    StructuralGF2Polynomial → StructuralGF2Polynomial
  | [] => structuralGF2Zero
  | monomial :: polynomial =>
      structuralGF2Add
        (structuralGF2Product (monomial.map atom))
        (structuralGF2Substitute atom polynomial)

@[simp] theorem evaluateStructuralGF2_singletonMonomial
    (assignment : ℕ → Bool) (monomial : EncodedGF2Monomial) :
    evaluateStructuralGF2 assignment [monomial] =
      monomial.all assignment := by
  cases hvalue : monomial.all assignment <;>
    simp [evaluateStructuralGF2, exactPolynomialValue,
      polynomialOccurrenceCount, exactMonomialValue, hvalue]

/-- Structural composition is semantically literal substitution on every
Boolean assignment.  This theorem is the bridge used to lower seed-local list
literals into the shared occurrence-residual variables. -/
@[simp] theorem evaluateStructuralGF2_substitute
    (assignment : ℕ → Bool)
    (atom : ℕ → StructuralGF2Polynomial)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2Substitute atom polynomial) =
      evaluateStructuralGF2
        (fun code => evaluateStructuralGF2 assignment (atom code))
        polynomial := by
  induction polynomial with
  | nil =>
      change
        evaluateStructuralGF2 assignment structuralGF2Zero =
          evaluateStructuralGF2
            (fun code => evaluateStructuralGF2 assignment (atom code))
            structuralGF2Zero
      simp
  | cons monomial polynomial ih =>
      rw [structuralGF2Substitute, evaluateStructuralGF2_add,
        evaluateStructuralGF2_product, ih]
      change
        ((monomial.map atom).all (evaluateStructuralGF2 assignment) !=
            evaluateStructuralGF2
              (fun code => evaluateStructuralGF2 assignment (atom code))
              polynomial) =
          evaluateStructuralGF2
            (fun code => evaluateStructuralGF2 assignment (atom code))
            (structuralGF2Add [monomial] polynomial)
      rw [evaluateStructuralGF2_add,
        evaluateStructuralGF2_singletonMonomial]
      simp [Function.comp_def]

/-- Executable parity over a finite coordinate family.  The recursion exposes
the same low-to-high ordering used by every fixed row ABI. -/
def structuralGF2FinParity :
    {arity : ℕ} →
      (Fin arity → StructuralGF2Polynomial) →
        StructuralGF2Polynomial
  | 0, _ => structuralGF2Zero
  | _ + 1, polynomials =>
      structuralGF2Add (polynomials 0)
        (structuralGF2FinParity fun index => polynomials index.succ)

private theorem boolParity_fin_succ
    {arity : ℕ} (value : Fin (arity + 1) → Bool) :
    boolParity value =
      (value 0 != boolParity (fun index : Fin arity => value index.succ)) := by
  unfold boolParity
  rw [Fin.sum_univ_succ]
  cases value 0 <;>
    simp [Nat.odd_add, ← Nat.not_odd_iff_even]

theorem boolParity_equiv
    {Source Target : Type} [Fintype Source] [Fintype Target]
    (equivalence : Source ≃ Target) (value : Target → Bool) :
    boolParity (fun source => value (equivalence source)) =
      boolParity value := by
  unfold boolParity
  exact congrArg (fun count => decide (Odd count))
    (equivalence.sum_comp fun target => (value target).toNat)

/-- A disjoint Boolean list may be read as parity without changing its OR.
This is the exact point where the imported decomposition's disjointness avoids
an exponential ANF expansion. -/
theorem boolParity_finGet_eq_any_of_disjoint
    {Item : Type} (items : List Item) (predicate : Item → Bool)
    (hdisjoint : (items.filter predicate).length ≤ 1) :
    boolParity (fun index : Fin items.length =>
        predicate (items.get index)) =
      items.any predicate := by
  unfold boolParity
  rw [sum_predicate_get_toNat_eq_filter_length,
    filterLength_eq_any_toNat items predicate hdisjoint]
  cases items.any predicate <;> rfl

@[simp] theorem evaluateStructuralGF2_finParity
    (assignment : ℕ → Bool) {arity : ℕ}
    (polynomials : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2FinParity polynomials) =
      boolParity fun index =>
        evaluateStructuralGF2 assignment (polynomials index) := by
  induction arity with
  | zero =>
      simp [structuralGF2FinParity, boolParity]
  | succ arity ih =>
      rw [structuralGF2FinParity, evaluateStructuralGF2_add,
        ih, boolParity_fin_succ]

/-- Structural version of the canonical total one-hot lookup.  Only lookup
coordinates whose table entry is true are retained, so this does not expand
to a truth table or introduce a parallel selection path. -/
def structuralGF2OneHotLookup
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot :
      Fin (populationBound + 1) → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun candidate =>
    if lookup candidate then oneHot candidate else structuralGF2Zero

@[simp] theorem evaluateStructuralGF2_oneHotLookup
    (assignment : ℕ → Bool)
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot :
      Fin (populationBound + 1) → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2OneHotLookup lookup oneHot) =
      oneHotLookupRow lookup fun candidate =>
        evaluateStructuralGF2 assignment (oneHot candidate) := by
  rw [structuralGF2OneHotLookup, evaluateStructuralGF2_finParity]
  unfold oneHotLookupRow
  congr 1
  funext candidate
  cases lookup candidate <;>
    simp

/-- Indicator polynomial for one complete Boolean assignment.  A false target
bit contributes `1 + x`; a true target bit contributes `x`, so the degree is
exactly the source arity and no auxiliary selector variables are introduced. -/
def structuralGF2BooleanSelector
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) :
    StructuralGF2Polynomial :=
  structuralGF2Product <|
    List.ofFn fun index =>
      if target index then bits index
      else structuralGF2Not (bits index)

@[simp] theorem evaluateStructuralGF2_booleanSelector
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) :
    evaluateStructuralGF2 assignment
        (structuralGF2BooleanSelector bits target) =
      decide
        ((fun index =>
          evaluateStructuralGF2 assignment (bits index)) = target) := by
  rw [structuralGF2BooleanSelector, evaluateStructuralGF2_product]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro hall
    funext index
    have hselected := hall
      (if target index then bits index
        else structuralGF2Not (bits index))
      (List.mem_ofFn.mpr ⟨index, rfl⟩)
    cases htarget : target index <;>
      cases hvalue : evaluateStructuralGF2 assignment (bits index) <;>
      simp_all
  · intro hequal polynomial hmember
    rcases List.mem_ofFn.mp hmember with ⟨index, rfl⟩
    have hindex := congrFun hequal index
    cases htarget : target index <;>
      cases hvalue : evaluateStructuralGF2 assignment (bits index) <;>
      simp_all

/-- Canonical low-to-high decoding of an in-range truth-table row. -/
def structuralTruthAssignment
    (arity : ℕ) (code : Fin (2 ^ arity)) : BitInput arity :=
  fun index => code.val.testBit index.val

@[simp] theorem structuralTruthAssignment_encode
    {arity : ℕ} (assignment : BitInput arity) :
    structuralTruthAssignment arity
        ⟨encodeBitInput assignment, by
          rw [encodeBitInput_eq_ofBits]
          exact Nat.ofBits_lt_two_pow assignment⟩ =
      assignment := by
  funext index
  change (encodeBitInput assignment).testBit index.val = assignment index
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt assignment index.val index.isLt

/-- Algebraic-normal-form truth-table compiler.  It is reserved for
logarithmic-arity fixed Boolean combiners (not population-sized lookups):
the assignment indicators are disjoint, so parity is exactly the requested
function on every input, including malformed upstream rows. -/
def structuralGF2TruthTable
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code : Fin (2 ^ arity) =>
    if function (structuralTruthAssignment arity code) then
      structuralGF2BooleanSelector bits
        (structuralTruthAssignment arity code)
    else
      structuralGF2Zero

@[simp] theorem evaluateStructuralGF2_truthTable
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool) :
    evaluateStructuralGF2 assignment
        (structuralGF2TruthTable bits function) =
      function fun index =>
        evaluateStructuralGF2 assignment (bits index) := by
  let actual : BitInput arity :=
    fun index => evaluateStructuralGF2 assignment (bits index)
  let actualCode : Fin (2 ^ arity) :=
    ⟨encodeBitInput actual, by
      rw [encodeBitInput_eq_ofBits]
      exact Nat.ofBits_lt_two_pow actual⟩
  have hdecodeActual :
      structuralTruthAssignment arity actualCode = actual := by
    exact structuralTruthAssignment_encode actual
  have hdecodeInjective :
      Function.Injective (structuralTruthAssignment arity) := by
    intro left right hequal
    apply Fin.ext
    have hencoded := congrArg encodeBitInput hequal
    unfold structuralTruthAssignment at hencoded
    rw [encodeBitInput_testBit left.isLt,
      encodeBitInput_testBit right.isLt] at hencoded
    exact hencoded
  rw [structuralGF2TruthTable, evaluateStructuralGF2_finParity]
  have hrow :
      (fun code : Fin (2 ^ arity) =>
          evaluateStructuralGF2 assignment
            (if function (structuralTruthAssignment arity code) then
              structuralGF2BooleanSelector bits
                (structuralTruthAssignment arity code)
            else
              structuralGF2Zero)) =
        fun code =>
          decide (code = actualCode) &&
            function (structuralTruthAssignment arity code) := by
    funext code
    rw [apply_ite (evaluateStructuralGF2 assignment)]
    rw [evaluateStructuralGF2_booleanSelector]
    change
      (if function (structuralTruthAssignment arity code) then
          decide (actual = structuralTruthAssignment arity code)
        else false) =
        (decide (code = actualCode) &&
          function (structuralTruthAssignment arity code))
    by_cases hfunction :
        function (structuralTruthAssignment arity code) = true
    · rw [if_pos hfunction]
      simp only [hfunction, Bool.and_true]
      apply decide_eq_decide.mpr
      constructor
      · intro hequal
        apply hdecodeInjective
        rw [hdecodeActual]
        exact hequal.symm
      · intro hequal
        subst code
        exact hdecodeActual.symm
    · have hfalse :=
        Bool.eq_false_of_not_eq_true hfunction
      rw [if_neg hfunction]
      simp [hfalse]
  rw [hrow, boolParity_exactSelector]
  rw [hdecodeActual]

/-- Majority over the walk-time coordinate family.  Only this logarithmic
combiner uses the truth-table compiler; population lookups stay linear via
`structuralGF2OneHotLookup`. -/
def structuralGF2BitMajority
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2TruthTable bits compiledBitMajority

@[simp] theorem evaluateStructuralGF2_bitMajority
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2BitMajority bits) =
      compiledBitMajority fun index =>
        evaluateStructuralGF2 assignment (bits index) := by
  exact evaluateStructuralGF2_truthTable
    assignment bits compiledBitMajority

/-- Structural finite conjunction used by the symmetric circuit segments. -/
def structuralGF2FiniteConjunction
    {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Product (List.ofFn values)

@[simp] theorem evaluateStructuralGF2_finiteConjunction
    (assignment : ℕ → Bool) {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2FiniteConjunction values) =
      finiteBoolConjunction fun index =>
        evaluateStructuralGF2 assignment (values index) := by
  rw [structuralGF2FiniteConjunction, evaluateStructuralGF2_product]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, finiteBoolConjunction_eq_true_iff]
  constructor
  · intro hall index
    exact hall (values index) (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro hall value hmember
    rcases List.mem_ofFn.mp hmember with ⟨index, rfl⟩
    exact hall index

/-- Structural finite disjunction used where total malformed-row OR semantics
is required; unlike parity, this remains correct when several rows are true. -/
def structuralGF2FiniteDisjunction
    {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Disjunction (List.ofFn values)

@[simp] theorem evaluateStructuralGF2_finiteDisjunction
    (assignment : ℕ → Bool) {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2FiniteDisjunction values) =
      finiteBoolDisjunction fun index =>
        evaluateStructuralGF2 assignment (values index) := by
  rw [structuralGF2FiniteDisjunction,
    evaluateStructuralGF2_disjunction]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, finiteBoolDisjunction_eq_true_iff]
  constructor
  · rintro ⟨value, hmember, htrue⟩
    rcases List.mem_ofFn.mp hmember with ⟨index, rfl⟩
    exact ⟨index, htrue⟩
  · rintro ⟨index, htrue⟩
    exact ⟨values index, List.mem_ofFn.mpr ⟨index, rfl⟩, htrue⟩

/-- Finite disjunction is invariant under a reindexing equivalence.  This
keeps dependent mixed-radix products executable without changing their total
OR semantics. -/
theorem finiteBoolDisjunction_equiv
    {Source Target : Type}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (equivalence : Source ≃ Target) (value : Target → Bool) :
    finiteBoolDisjunction (fun source => value (equivalence source)) =
      finiteBoolDisjunction value := by
  apply Bool.eq_iff_iff.mpr
  rw [finiteBoolDisjunction_eq_true_iff,
    finiteBoolDisjunction_eq_true_iff]
  constructor
  · rintro ⟨source, htrue⟩
    exact ⟨equivalence source, htrue⟩
  · rintro ⟨target, htrue⟩
    exact ⟨equivalence.symm target, by simpa⟩

/-- Direct executable expansion of an elementary symmetric polynomial.  The
input is a duplicate-free list of variable codes; `sublistsLen` enumerates
exactly the degree-sized subsets without quotienting through `Finset.toList`. -/
def structuralGF2ElementarySymmetric
    (codes : List ℕ) (degree : ℕ) :
    StructuralGF2Polynomial :=
  codes.sublistsLen degree

private theorem sublistsLen_map
    {α β : Type} (mapValue : α → β)
    (degree : ℕ) (values : List α) :
    List.sublistsLen degree (values.map mapValue) =
      (List.sublistsLen degree values).map (List.map mapValue) := by
  induction degree generalizing values with
  | zero =>
      simp [List.sublistsLen_zero]
  | succ degree ih =>
      induction values with
      | nil =>
          simp [List.sublistsLen_succ_nil]
      | cons value values tailIH =>
          rw [List.map_cons, List.sublistsLen_succ_cons,
            List.sublistsLen_succ_cons, tailIH, ih]
          simp [List.map_append, Function.comp_def]

theorem interpretStructuralGF2_elementarySymmetric
    {depth population : ℕ}
    (codes : List ℕ) (degree : ℕ) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2ElementarySymmetric codes degree) =
      ((codes.map fun code =>
        match decodeListLiteralVariable depth population code with
        | some literal => MvPolynomial.X literal
        | none => 0 : List
          (MvPolynomial (ListLiteralVariable depth population) (ZMod 2))) :
        Multiset
          (MvPolynomial (ListLiteralVariable depth population) (ZMod 2))).esymm
        degree := by
  unfold structuralGF2ElementarySymmetric interpretStructuralGF2
  unfold interpretEncodedGF2Monomial Multiset.esymm
  rw [Multiset.powersetCard_coe]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  rw [sublistsLen_map]
  simp [Function.comp_def, Multiset.prod_coe]

theorem interpretStructuralGF2_elementarySymmetric_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (degree : ℕ) :
    interpretStructuralGF2
        (structuralGF2ElementarySymmetric
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          degree) =
      MvPolynomial.rename embed
        (MvPolynomial.esymm (Fin arity) (ZMod 2) degree) := by
  rw [interpretStructuralGF2_elementarySymmetric]
  simp only [List.map_ofFn, Function.comp_def,
    decodeListLiteralVariable_encode]
  rw [← Fin.univ_val_map]
  rw [Finset.esymm_map_val]
  unfold MvPolynomial.esymm
  simp only [map_sum, map_prod, MvPolynomial.rename_X]

def structuralGF2ShiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.Nat.antidiagonal degree).map fun indices =>
      structuralGF2Scale
        ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : ZMod 2)
        (structuralGF2ElementarySymmetric codes indices.1)

theorem interpretStructuralGF2_shiftedElementarySymmetric_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (offset degree : ℕ) :
    interpretStructuralGF2
        (structuralGF2ShiftedElementarySymmetric
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          offset degree) =
      MvPolynomial.rename embed
        (SupplierWindow.shiftedEsymm arity offset degree) := by
  unfold structuralGF2ShiftedElementarySymmetric
  rw [interpretStructuralGF2_sum]
  simp only [List.map_map, Function.comp_def,
    interpretStructuralGF2_scale,
    interpretStructuralGF2_elementarySymmetric_ofFn]
  unfold SupplierWindow.shiftedEsymm
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  rfl

def structuralGF2ConsecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.range (width + 1)).map fun degree =>
      structuralGF2Scale
        (SupplierWindow.triangularCoefficient
          (SupplierWindow.windowDelta target) degree)
        (structuralGF2ShiftedElementarySymmetric
          codes offset degree)

theorem interpretStructuralGF2_consecutiveWindowIndicator_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (offset width target : ℕ) :
    interpretStructuralGF2
        (structuralGF2ConsecutiveWindowIndicator
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          offset width target) =
      MvPolynomial.rename embed
        (SupplierWindow.consecutiveWindowIndicator
          arity offset width target) := by
  unfold structuralGF2ConsecutiveWindowIndicator
  rw [interpretStructuralGF2_sum]
  simp only [List.map_map, Function.comp_def,
    interpretStructuralGF2_scale,
    interpretStructuralGF2_shiftedElementarySymmetric_ofFn]
  unfold SupplierWindow.consecutiveWindowIndicator
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  rfl

def terminalLiteralVariableCodes
    (depth population : ℕ) : List ℕ :=
  List.ofFn fun coordinate : Fin population =>
    encodeListLiteralVariable
      (ListLiteralVariable.terminal (depth := depth) coordinate)

def deltaLiteralVariableCodes
    {depth population : ℕ} (level : Fin depth) : List ℕ :=
  List.ofFn fun slot : Fin (2 * population) =>
    encodeListLiteralVariable
      (ListLiteralVariable.delta level slot)

def structuralTerminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2ConsecutiveWindowIndicator
    (terminalLiteralVariableCodes depth population)
    0 terminalWindow target

theorem interpretStructuralTerminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    interpretStructuralGF2
        (structuralTerminalWindowPolynomial
          depth population terminalWindow target) =
      terminalWindowPolynomial depth population terminalWindow target := by
  unfold structuralTerminalWindowPolynomial terminalLiteralVariableCodes
  rw [interpretStructuralGF2_consecutiveWindowIndicator_ofFn]
  rfl

def structuralDeltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  structuralGF2ConsecutiveWindowIndicator
    (deltaLiteralVariableCodes (population := population) level)
    (childCard - window level) (2 * window level) target

theorem interpretStructuralDeltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    interpretStructuralGF2
        (structuralDeltaWindowPolynomial
          label seed window level target) =
      deltaWindowPolynomial label seed window level target := by
  unfold structuralDeltaWindowPolynomial deltaLiteralVariableCodes
  unfold deltaWindowPolynomial
  dsimp only
  rw [interpretStructuralGF2_consecutiveWindowIndicator_ofFn]

def structuralDeltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  match deltaTarget? childCard (window level)
      parent.val child.val with
  | none => structuralGF2Zero
  | some target =>
      structuralDeltaWindowPolynomial label seed window level target

theorem interpretStructuralDeltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralDeltaFactor label seed window level parent child) =
      deltaFactor label seed window level parent child := by
  unfold structuralDeltaFactor deltaFactor
  dsimp only
  split <;>
    simp_all [interpretStructuralGF2_zero,
      interpretStructuralDeltaWindowPolynomial]

abbrev StructuralListPolynomialVector (population : ℕ) :=
  Fin (population + 1) → StructuralGF2Polynomial

def structuralTerminalPolynomialVector
    (depth population terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  fun candidate =>
    structuralTerminalWindowPolynomial depth population
      terminalWindow candidate.val

theorem interpretStructuralTerminalPolynomialVector
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralTerminalPolynomialVector
          depth population terminalWindow candidate) =
      terminalPolynomialVector depth population terminalWindow candidate := by
  unfold structuralTerminalPolynomialVector terminalPolynomialVector
  exact interpretStructuralTerminalWindowPolynomial
    depth population terminalWindow candidate.val

def structuralCombineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population) :
    StructuralListPolynomialVector population :=
  fun parent =>
    structuralGF2Sum <|
      List.ofFn fun child : Fin (population + 1) =>
        structuralGF2Mul (childPolynomials child)
          (structuralDeltaFactor label seed window level parent child)

theorem interpretStructuralCombineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (childSpecification : ListPolynomialVector depth population)
    (hrefines : ∀ child,
      interpretStructuralGF2 (childPolynomials child) =
        childSpecification child)
    (parent : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralCombineListLevel label seed window level
          childPolynomials parent) =
      combineListLevel label seed window level childSpecification parent := by
  unfold structuralCombineListLevel combineListLevel
  rw [interpretStructuralGF2_sum]
  simp only [List.map_ofFn, Function.comp_def,
    interpretStructuralGF2_mul]
  simp_rw [hrefines, interpretStructuralDeltaFactor]
  rw [List.sum_ofFn]

/-- Structural recursion over the remaining levels.  Every constructor is
computable; no `MvPolynomial.support`, quotient enumeration, or classical
choice is present in the production path. -/
def structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ) :
    StructuralListPolynomialVector population :=
  if hlevel : level < depth then
    structuralCombineListLevel label seed window ⟨level, hlevel⟩
      (structuralListPolynomialVectorFrom label seed window
        terminalWindow (level + 1))
  else
    structuralTerminalPolynomialVector depth population terminalWindow
termination_by depth - level
decreasing_by omega

theorem interpretStructuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralListPolynomialVectorFrom label seed window
          terminalWindow level candidate) =
      listPolynomialVectorFrom label seed window
        terminalWindow level candidate := by
  rw [structuralListPolynomialVectorFrom, listPolynomialVectorFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext, dif_pos hnext]
    apply interpretStructuralCombineListLevel label seed window
      ⟨level, hnext⟩ _ _
    intro child
    exact interpretStructuralListPolynomialVectorFrom label seed window
      terminalWindow (level + 1) child
  · rw [dif_neg hnext, dif_neg hnext]
    exact interpretStructuralTerminalPolynomialVector
      depth population terminalWindow candidate
termination_by depth - level
decreasing_by omega

def structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  structuralListPolynomialVectorFrom label seed window terminalWindow 0

theorem interpretStructuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralListPolynomialVector label seed window
          terminalWindow candidate) =
      listPolynomialVector label seed window
        terminalWindow candidate := by
  unfold structuralListPolynomialVector listPolynomialVector
  exact interpretStructuralListPolynomialVectorFrom label seed window
    terminalWindow 0 candidate

/-- Total decoder for the doubled literal population.  The left half carries
active sibling coordinates; the right half carries complemented child
coordinates. -/
def decodeListLiteralSlot
    {population : ℕ} (slot : Fin (2 * population)) :
    Sum (Fin population) (Fin population) :=
  if hleft : slot.val < population then
    .inl ⟨slot.val, hleft⟩
  else
    .inr ⟨slot.val - population, by omega⟩

@[simp] theorem decodeListLiteralSlot_left
    {population : ℕ} (coordinate : Fin population) :
    decodeListLiteralSlot (leftLiteralSlot coordinate) =
      .inl coordinate := by
  unfold decodeListLiteralSlot leftLiteralSlot
  rw [dif_pos coordinate.isLt]

@[simp] theorem decodeListLiteralSlot_right
    {population : ℕ} (coordinate : Fin population) :
    decodeListLiteralSlot (rightLiteralSlot coordinate) =
      .inr coordinate := by
  have hright :
      ¬(rightLiteralSlot coordinate).val < population := by
    simp [rightLiteralSlot]
  unfold decodeListLiteralSlot
  rw [dif_neg hright]
  apply congrArg Sum.inr
  apply Fin.ext
  simp [rightLiteralSlot]

private theorem decodeListLiteralSlot_inl
    {population : ℕ} {slot : Fin (2 * population)}
    {coordinate : Fin population}
    (hdecode : decodeListLiteralSlot slot = .inl coordinate) :
    slot = leftLiteralSlot coordinate := by
  unfold decodeListLiteralSlot at hdecode
  split at hdecode
  · simp only [Sum.inl.injEq] at hdecode
    subst coordinate
    apply Fin.ext
    rfl
  · simp at hdecode

private theorem decodeListLiteralSlot_inr
    {population : ℕ} {slot : Fin (2 * population)}
    {coordinate : Fin population}
    (hdecode : decodeListLiteralSlot slot = .inr coordinate) :
    slot = rightLiteralSlot coordinate := by
  unfold decodeListLiteralSlot at hdecode
  split at hdecode
  · simp at hdecode
  · simp only [Sum.inr.injEq] at hdecode
    subst coordinate
    apply Fin.ext
    simp [rightLiteralSlot]
    omega

private theorem mem_deltaLiteralActive_left
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ)
    (coordinate : Fin population) :
    leftLiteralSlot coordinate ∈
        deltaLiteralActive active label seed level ↔
      coordinate ∈ active ∧
        toeplitzHash (label coordinate) seed ∈
          siblingPrefixCell rank level := by
  constructor
  · intro hmember
    rcases Finset.mem_union.mp hmember with hleft | hright
    · rcases Finset.mem_image.mp hleft with
        ⟨source, hsource, hequal⟩
      have hsourceEq : source = coordinate :=
        leftLiteralSlot_injective hequal
      subst source
      exact
        ⟨(Finset.mem_inter.mp hsource).1,
          (mem_hashIndexCell _ _ _ _).mp
            (Finset.mem_inter.mp hsource).2⟩
    · rcases Finset.mem_image.mp hright with
        ⟨source, _hsource, hequal⟩
      exact False.elim
        (left_rightLiteralSlot_ne coordinate source hequal.symm)
  · rintro ⟨hactive, hhash⟩
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact
      ⟨coordinate,
        Finset.mem_inter.mpr
          ⟨hactive, (mem_hashIndexCell _ _ _ _).mpr hhash⟩,
        rfl⟩

private theorem mem_deltaLiteralActive_right
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ)
    (coordinate : Fin population) :
    rightLiteralSlot coordinate ∈
        deltaLiteralActive active label seed level ↔
      toeplitzHash (label coordinate) seed ∈
          zeroPrefixCell rank (level + 1) ∧
        coordinate ∉ active := by
  constructor
  · intro hmember
    rcases Finset.mem_union.mp hmember with hleft | hright
    · rcases Finset.mem_image.mp hleft with
        ⟨source, _hsource, hequal⟩
      exact False.elim
        (left_rightLiteralSlot_ne source coordinate hequal)
    · rcases Finset.mem_image.mp hright with
        ⟨source, hsource, hequal⟩
      have hsourceEq : source = coordinate :=
        rightLiteralSlot_injective hequal
      subst source
      exact
        ⟨(mem_hashIndexCell _ _ _ _).mp
            (Finset.mem_sdiff.mp hsource).1,
          (Finset.mem_sdiff.mp hsource).2⟩
  · rintro ⟨hhash, hactive⟩
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact
      ⟨coordinate,
        Finset.mem_sdiff.mpr
          ⟨(mem_hashIndexCell _ _ _ _).mpr hhash, hactive⟩,
        rfl⟩

/-- Total assignment decoder for the occurrence-variable ABI.  Invalid codes
are false, matching `decodeListLiteralVariable`'s malformed-code semantics. -/
def encodedFiniteBooleanAssignment
    {population : ℕ} (active : Fin population → Bool)
    (code : ℕ) : Bool :=
  if hcode : code < population then active ⟨code, hcode⟩ else false

/-- One masked residual coordinate as a structural polynomial. -/
def structuralMaskedCoordinate
    {population : ℕ} (mask : Finset (Fin population))
    (coordinate : Fin population) : StructuralGF2Polynomial :=
  if coordinate ∈ mask then
    structuralGF2Variable coordinate.val
  else
    structuralGF2Zero

@[simp] theorem evaluateStructuralMaskedCoordinate
    {population : ℕ} (active : Fin population → Bool)
    (mask : Finset (Fin population)) (coordinate : Fin population) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedCoordinate mask coordinate) =
      (active coordinate && decide (coordinate ∈ mask)) := by
  by_cases hmask : coordinate ∈ mask
  · simp [structuralMaskedCoordinate, hmask,
      encodedFiniteBooleanAssignment, coordinate.isLt]
  · simp [structuralMaskedCoordinate, hmask]

/-- Seed-local list literals lowered into the single shared population of
masked residual variables.  Hash membership is compile-time data; the only
nonconstant atoms are `x` and `1 + x`. -/
def structuralListLiteralAtom
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    StructuralGF2Polynomial :=
  match decodeListLiteralVariable depth population code with
  | none => structuralGF2Zero
  | some (.terminal coordinate) =>
      if toeplitzHash (label coordinate) seed ∈
          zeroPrefixCell rank depth then
        structuralMaskedCoordinate mask coordinate
      else
        structuralGF2Zero
  | some (.delta level slot) =>
      match decodeListLiteralSlot slot with
      | .inl coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              siblingPrefixCell rank level.val then
            structuralMaskedCoordinate mask coordinate
          else
            structuralGF2Zero
      | .inr coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              zeroPrefixCell rank (level.val + 1) then
            structuralGF2Not
              (structuralMaskedCoordinate mask coordinate)
          else
            structuralGF2Zero

/-- Every lowered atom evaluates exactly as the original set-based list
literal on the masked active set. -/
theorem evaluateStructuralListLiteralAtom
    {rank depth population : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralListLiteralAtom (depth := depth)
          mask label seed code) =
      match decodeListLiteralVariable depth population code with
      | some literal =>
          listLiteralBooleanAssignment
            ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
            label seed literal
      | none => false := by
  cases hdecode :
      decodeListLiteralVariable depth population code with
  | none =>
      simp [structuralListLiteralAtom, hdecode]
  | some literal =>
    cases literal with
    | terminal coordinate =>
        simp only [structuralListLiteralAtom, hdecode]
        unfold listLiteralBooleanAssignment terminalLiteralActive
        by_cases hhash :
            toeplitzHash (label coordinate) seed ∈
              zeroPrefixCell rank depth
        <;> cases hactive : active coordinate
        <;> by_cases hmask : coordinate ∈ mask
        <;> simp [hhash, hactive, hmask, mem_hashIndexCell]
    | delta level slot =>
        cases hslot : decodeListLiteralSlot slot with
        | inl coordinate =>
          have hslotEq :=
            decodeListLiteralSlot_inl hslot
          subst slot
          simp only [structuralListLiteralAtom, hdecode,
            decodeListLiteralSlot_left]
          change
            evaluateStructuralGF2
                (encodedFiniteBooleanAssignment active)
                (if toeplitzHash (label coordinate) seed ∈
                    siblingPrefixCell rank level.val then
                  structuralMaskedCoordinate mask coordinate
                else structuralGF2Zero) =
              decide
                (leftLiteralSlot coordinate ∈
                  deltaLiteralActive
                    ((Finset.univ.filter fun candidate =>
                      active candidate) ∩ mask)
                    label seed level.val)
          simp only [mem_deltaLiteralActive_left]
          by_cases hhash :
              toeplitzHash (label coordinate) seed ∈
                siblingPrefixCell rank level.val
          <;> cases hactive : active coordinate
          <;> by_cases hmask : coordinate ∈ mask
          <;> simp [hhash, hactive, hmask]
        | inr coordinate =>
          have hslotEq :=
            decodeListLiteralSlot_inr hslot
          subst slot
          simp only [structuralListLiteralAtom, hdecode,
            decodeListLiteralSlot_right]
          change
            evaluateStructuralGF2
                (encodedFiniteBooleanAssignment active)
                (if toeplitzHash (label coordinate) seed ∈
                    zeroPrefixCell rank (level.val + 1) then
                  structuralGF2Not
                    (structuralMaskedCoordinate mask coordinate)
                else structuralGF2Zero) =
              decide
                (rightLiteralSlot coordinate ∈
                  deltaLiteralActive
                    ((Finset.univ.filter fun candidate =>
                      active candidate) ∩ mask)
                    label seed level.val)
          simp only [mem_deltaLiteralActive_right]
          by_cases hhash :
              toeplitzHash (label coordinate) seed ∈
                zeroPrefixCell rank (level.val + 1)
          <;> cases hactive : active coordinate
          <;> by_cases hmask : coordinate ∈ mask
          <;> simp [hhash, hactive, hmask]

/-- One structural list coordinate after lowering all seed-local literals to
the shared masked population. -/
def structuralMaskedListCoordinate
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
  StructuralGF2Polynomial :=
  structuralGF2Substitute
    (structuralListLiteralAtom (depth := depth) mask label seed)
    (structuralListPolynomialVector label seed window
      terminalWindow candidate)

def evaluateStructuralListCoordinate
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) : Bool :=
  evaluateStructuralGF2
    (encodedListLiteralBooleanAssignment (depth := depth) active label seed)
    (structuralListPolynomialVector label seed window
      terminalWindow candidate)

theorem evaluateStructuralListCoordinate_eq_compiled
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    evaluateStructuralListCoordinate active label seed window
        terminalWindow candidate =
      compiledListCoordinate active label seed window
        terminalWindow candidate := by
  unfold evaluateStructuralListCoordinate
  change
    evaluateStructuralGF2
        (fun code =>
          match decodeListLiteralVariable depth population code with
          | some literal =>
              listLiteralBooleanAssignment active label seed literal
          | none => false)
        (structuralListPolynomialVector label seed window
          terminalWindow candidate) =
      compiledListCoordinate active label seed window
        terminalWindow candidate
  rw [evaluateStructuralGF2_eq_aeval,
    interpretStructuralListPolynomialVector]
  unfold compiledListCoordinate
  rw [exactPolynomialValue_compiled]

@[simp] theorem evaluateStructuralMaskedListCoordinate
    {rank depth population : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedListCoordinate mask label seed window
          terminalWindow candidate) =
      compiledListCoordinate
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label seed window terminalWindow candidate := by
  rw [structuralMaskedListCoordinate,
    evaluateStructuralGF2_substitute]
  simp_rw [evaluateStructuralListLiteralAtom]
  exact evaluateStructuralListCoordinate_eq_compiled
    ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
    label seed window terminalWindow candidate

/-- One powered-walk list coordinate as a polynomial in the shared masked
population.  Only the logarithmic walk-time combiner uses the truth-table
compiler; each seed coordinate retains the structural window polynomial. -/
def structuralMaskedWalkListCoordinate
    {rank depth population t : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  structuralGF2BitMajority fun time =>
    structuralMaskedListCoordinate mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

def executableWalkListCoordinate
    {rank depth population t : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) : Bool :=
  compiledBitMajority fun time =>
    evaluateStructuralListCoordinate active label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

theorem executableWalkListCoordinate_eq_compiled
    {rank depth population t : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    executableWalkListCoordinate active label window terminalWindow
        sample candidate =
      compiledWalkListCoordinate active label window terminalWindow
        sample candidate := by
  unfold executableWalkListCoordinate compiledWalkListCoordinate
  congr 1
  funext time
  exact evaluateStructuralListCoordinate_eq_compiled active label
    (toeplitzWalkEncoding rank (sample.vertex time)).1
    window terminalWindow candidate

@[simp] theorem evaluateStructuralMaskedWalkListCoordinate
    {rank depth population t : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedWalkListCoordinate mask label window
          terminalWindow sample candidate) =
      executableWalkListCoordinate
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label window terminalWindow sample candidate := by
  rw [structuralMaskedWalkListCoordinate,
    evaluateStructuralGF2_bitMajority]
  unfold executableWalkListCoordinate
  congr 1
  funext time
  exact
    (evaluateStructuralMaskedListCoordinate active mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate).trans
      (evaluateStructuralListCoordinate_eq_compiled
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label (toeplitzWalkEncoding rank (sample.vertex time)).1
        window terminalWindow candidate).symm

/-- The production occurrence-list coordinate.  The real-valued graded schedule
is absent from execution: `executableGradedWindow` is the proved-equal natural
ceiling formula, and every polynomial is the structural GF(2) syntax above. -/
def executableCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) : Bool :=
  executableWalkListCoordinate
    (depth := canonicalGradedDepth
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    active.1
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (executableGradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate

theorem executableCanonicalOccurrenceListCoordinate_refines
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    executableCanonicalOccurrenceListCoordinate occurrences liveScale
        denominator active sample candidate =
      canonicalOccurrenceListCoordinate occurrences liveScale
        denominator active sample candidate := by
  unfold executableCanonicalOccurrenceListCoordinate
    canonicalOccurrenceListCoordinate
  have hwindow :
      executableGradedWindow
          (depth := canonicalGradedDepth
            (touchingCost (occurrenceSupport occurrences)
              (normalizedLiveSet occurrences liveScale)))
          (touchingCost (occurrenceSupport occurrences)
            (normalizedLiveSet occurrences liveScale)) =
        gradedWindow
          (depth := canonicalGradedDepth
            (touchingCost (occurrenceSupport occurrences)
              (normalizedLiveSet occurrences liveScale)))
          (touchingCost (occurrenceSupport occurrences)
            (normalizedLiveSet occurrences liveScale)) := by
    funext level
    exact executableGradedWindow_eq_gradedWindow _ level
  rw [hwindow]
  exact executableWalkListCoordinate_eq_compiled _ _ _ _
    sample candidate

/-- Canonical occurrence-list coordinate as a structural polynomial in the
shared residual-gate variables.  The mask is explicit because every circuit
segment and coefficient digit reuses the same occurrence universe. -/
def structuralCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    StructuralGF2Polynomial :=
  structuralMaskedWalkListCoordinate mask
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (executableGradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate

@[simp] theorem evaluateStructuralCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceListCoordinate occurrences
          liveScale denominator mask sample candidate) =
      executableCanonicalOccurrenceListCoordinate occurrences
        liveScale denominator
        (normalizedMaskedResidualActiveSet occurrences
          liveScale input mask)
        sample candidate := by
  unfold structuralCanonicalOccurrenceListCoordinate
    executableCanonicalOccurrenceListCoordinate
  simp [normalizedMaskedResidualActiveSet,
    occurrenceMaskedResidualActiveSet, occurrenceResidualActiveSet]

def executableCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) : Bool :=
  oneHotLookupRow lookup fun candidate =>
    executableCanonicalOccurrenceListCoordinate occurrences liveScale
      denominator active sample candidate

theorem executableCanonicalOccurrenceLookupRow_refines
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    executableCanonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup =
      canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup := by
  unfold executableCanonicalOccurrenceLookupRow
    canonicalOccurrenceLookupRow
  congr 1
  funext candidate
  exact executableCanonicalOccurrenceListCoordinate_refines occurrences
    liveScale denominator active sample candidate

/-- Linear structural lookup over the canonical occurrence-list coordinates. -/
def structuralCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    StructuralGF2Polynomial :=
  structuralGF2OneHotLookup lookup fun candidate =>
    structuralCanonicalOccurrenceListCoordinate occurrences
      liveScale denominator mask sample candidate

@[simp] theorem evaluateStructuralCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceLookupRow occurrences
          liveScale denominator mask sample lookup) =
      executableCanonicalOccurrenceLookupRow occurrences
        liveScale denominator
        (normalizedMaskedResidualActiveSet occurrences
          liveScale input mask)
        sample lookup := by
  rw [structuralCanonicalOccurrenceLookupRow,
    evaluateStructuralGF2_oneHotLookup]
  unfold executableCanonicalOccurrenceLookupRow
  congr 1
  funext candidate
  exact evaluateStructuralCanonicalOccurrenceListCoordinate
    occurrences liveScale denominator input mask sample candidate

def executableCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  executableCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator
    (normalizedMaskedResidualActiveSet
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    sample
    (shiftedFiniteLookup
      (occurrenceResidualConstantCount
        (symmetricFourfoldOccurrences request) liveScale input
        (symmetricCircuitMask request circuitIndex))
      (symmetricCircuitTopLookup request circuitIndex))

theorem executableCanonicalSymmetricCircuitRow_refines
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample =
      canonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample := by
  unfold executableCanonicalSymmetricCircuitRow
    canonicalSymmetricCircuitRow
  exact executableCanonicalOccurrenceLookupRow_refines _ _ _ _ _ _

/-- One symmetric circuit segment with its frozen residual-constant offset
made explicit.  The production column selector supplies this offset; the
polynomial itself contains only shared residual variables. -/
def structuralCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : ℕ) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator
    (symmetricCircuitMask request circuitIndex)
    sample
    (shiftedFiniteLookup constantOffset
      (symmetricCircuitTopLookup request circuitIndex))

@[simp] theorem evaluateStructuralCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : ℕ)
    (hoffset :
      constantOffset =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricCircuitRow request liveScale
          denominator circuitIndex sample constantOffset) =
      executableCanonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample := by
  subst constantOffset
  unfold structuralCanonicalSymmetricCircuitRow
    executableCanonicalSymmetricCircuitRow
  exact evaluateStructuralCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator input
    (symmetricCircuitMask request circuitIndex) sample
    (shiftedFiniteLookup
      (occurrenceResidualConstantCount
        (symmetricFourfoldOccurrences request) liveScale input
        (symmetricCircuitMask request circuitIndex))
      (symmetricCircuitTopLookup request circuitIndex))

/-- Complete symmetric row polynomial, parameterized only by the finite vector
of frozen circuit offsets selected by the external column. -/
def structuralCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2FiniteConjunction fun circuitIndex =>
    structuralCanonicalSymmetricCircuitRow request liveScale denominator
      circuitIndex sample (constantOffset circuitIndex)

def executableCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  finiteBoolConjunction fun circuitIndex : Fin request.circuits.length =>
    executableCanonicalSymmetricCircuitRow request liveScale denominator input
      circuitIndex sample

theorem executableCanonicalSymmetricFourfoldRow_refines
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalSymmetricFourfoldRow request liveScale denominator
        input sample =
      canonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  unfold executableCanonicalSymmetricFourfoldRow
    canonicalSymmetricFourfoldRow
  apply finiteBoolConjunction_congr
  intro circuitIndex
  exact executableCanonicalSymmetricCircuitRow_refines request liveScale
    denominator input circuitIndex sample

@[simp] theorem evaluateStructuralCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricFourfoldRow request liveScale
          denominator sample constantOffset) =
      executableCanonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  rw [structuralCanonicalSymmetricFourfoldRow,
    evaluateStructuralGF2_finiteConjunction]
  unfold executableCanonicalSymmetricFourfoldRow
  apply finiteBoolConjunction_congr
  intro circuitIndex
  exact evaluateStructuralCanonicalSymmetricCircuitRow request liveScale
    denominator input circuitIndex sample (constantOffset circuitIndex)
    (hoffset circuitIndex)

theorem evaluateStructuralCanonicalSymmetricFourfoldRow_eq_canonical
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricFourfoldRow request liveScale
          denominator sample constantOffset) =
      canonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  exact
    (evaluateStructuralCanonicalSymmetricFourfoldRow request liveScale
      denominator input sample constantOffset hoffset).trans
      (executableCanonicalSymmetricFourfoldRow_refines request liveScale
        denominator input sample)

/-- Structural form of the total modular-radix row.  `finFunctionFinEquiv` is
the executable mixed-radix enumeration of all digit tuples; the polynomial
keeps one selected list coordinate per digit and parity across tuple rows. -/
def structuralGF2ModularRadixRow
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot :
      Fin digits → Fin (populationBound + 1) →
        StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code :
      Fin ((populationBound + 1) ^ digits) =>
    let tuple :=
      (finFunctionFinEquiv :
        (Fin digits → Fin (populationBound + 1)) ≃
          Fin ((populationBound + 1) ^ digits)).symm code
    if modularTupleAccepts modulus offset base tuple then
      structuralGF2FiniteConjunction fun digit =>
        oneHot digit (tuple digit)
    else
      structuralGF2Zero

@[simp] theorem evaluateStructuralGF2_modularRadixRow
    (assignment : ℕ → Bool)
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot :
      Fin digits → Fin (populationBound + 1) →
        StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2ModularRadixRow modulus offset base oneHot) =
      modularRadixRow modulus offset base fun digit candidate =>
        evaluateStructuralGF2 assignment (oneHot digit candidate) := by
  rw [structuralGF2ModularRadixRow,
    evaluateStructuralGF2_finParity]
  let equivalence :
      Fin ((populationBound + 1) ^ digits) ≃
        (Fin digits → Fin (populationBound + 1)) :=
    (finFunctionFinEquiv :
      (Fin digits → Fin (populationBound + 1)) ≃
        Fin ((populationBound + 1) ^ digits)).symm
  have hrow :
      (fun code : Fin ((populationBound + 1) ^ digits) =>
        evaluateStructuralGF2 assignment
          (let tuple := equivalence code
          if modularTupleAccepts modulus offset base tuple then
            structuralGF2FiniteConjunction fun digit =>
              oneHot digit (tuple digit)
          else
            structuralGF2Zero)) =
        fun code =>
          digitTupleMatches
              (fun digit candidate =>
                evaluateStructuralGF2 assignment
                  (oneHot digit candidate))
              (equivalence code) &&
            modularTupleAccepts modulus offset base (equivalence code) := by
    funext code
    dsimp only
    cases modularTupleAccepts modulus offset base (equivalence code) <;>
      simp [digitTupleMatches, finiteBoolConjunction]
  rw [hrow]
  unfold modularRadixRow
  exact boolParity_equiv equivalence
    (fun tuple =>
      digitTupleMatches
          (fun digit candidate =>
            evaluateStructuralGF2 assignment (oneHot digit candidate))
          tuple &&
        modularTupleAccepts modulus offset base tuple)

def executableCanonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) : Bool :=
  modularRadixRow modulus offset base fun digit candidate =>
    executableCanonicalOccurrenceListCoordinate occurrences liveScale
      denominator (active digit) sample candidate

theorem executableCanonicalOccurrenceModularRadixRow_refines
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) :
    executableCanonicalOccurrenceModularRadixRow occurrences liveScale
        denominator active sample modulus offset base =
      canonicalOccurrenceModularRadixRow occurrences liveScale
        denominator active sample modulus offset base := by
  unfold executableCanonicalOccurrenceModularRadixRow
    canonicalOccurrenceModularRadixRow
  congr 1
  funext digit candidate
  exact executableCanonicalOccurrenceListCoordinate_refines occurrences
    liveScale denominator (active digit) sample candidate

/-- Canonical modular-radix polynomial over a digit-indexed mask family. -/
def structuralCanonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Fin digits → Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2ModularRadixRow modulus offset base fun digit candidate =>
    structuralCanonicalOccurrenceListCoordinate occurrences
      liveScale denominator (mask digit) sample candidate

@[simp] theorem
    evaluateStructuralCanonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Fin digits → Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceModularRadixRow occurrences
          liveScale denominator mask sample modulus offset base) =
      executableCanonicalOccurrenceModularRadixRow occurrences
        liveScale denominator
        (fun digit =>
          normalizedMaskedResidualActiveSet occurrences
            liveScale input (mask digit))
        sample modulus offset base := by
  rw [structuralCanonicalOccurrenceModularRadixRow,
    evaluateStructuralGF2_modularRadixRow]
  unfold executableCanonicalOccurrenceModularRadixRow
  congr 1
  funext digit candidate
  exact evaluateStructuralCanonicalOccurrenceListCoordinate
    occurrences liveScale denominator input (mask digit) sample candidate

def executableCanonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) : Bool :=
  executableCanonicalOccurrenceModularRadixRow occurrences liveScale
    denominator
    (fun digit : Fin digits =>
      normalizedCoefficientBitActiveSet occurrences liveScale input
        mask coefficient digit.val)
    sample modulus offset 2

theorem executableCanonicalOccurrenceCoefficientRadixRow_refines
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) :
    executableCanonicalOccurrenceCoefficientRadixRow (digits := digits)
        occurrences liveScale denominator input mask coefficient sample
        modulus offset =
      canonicalOccurrenceCoefficientRadixRow (digits := digits)
        occurrences liveScale denominator input mask coefficient sample
        modulus offset := by
  unfold executableCanonicalOccurrenceCoefficientRadixRow
    canonicalOccurrenceCoefficientRadixRow
  exact executableCanonicalOccurrenceModularRadixRow_refines
    occurrences liveScale denominator _ sample modulus offset 2

/-- Coefficient-bit specialization of the structural modular-radix row. -/
def structuralCanonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceModularRadixRow (digits := digits) occurrences
    liveScale denominator
    (fun digit =>
      mask.filter fun index =>
        (coefficient index).testBit digit.val)
    sample modulus offset 2

@[simp] theorem
    evaluateStructuralCanonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceCoefficientRadixRow
          (digits := digits) occurrences liveScale denominator
          mask coefficient sample modulus offset) =
      executableCanonicalOccurrenceCoefficientRadixRow
        (digits := digits) occurrences liveScale denominator input
        mask coefficient sample modulus offset := by
  rw [structuralCanonicalOccurrenceCoefficientRadixRow,
    evaluateStructuralCanonicalOccurrenceModularRadixRow]
  unfold executableCanonicalOccurrenceCoefficientRadixRow
  congr 2

def executableCanonicalThresholdSelectionRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (selection : ThresholdChildSelection algorithm request)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator) : Bool :=
  let equation := thresholdSelectionEquation algorithm request selection
  executableCanonicalOccurrenceCoefficientRadixRow
    (digits := modulusDigitCount prime.val)
    (thresholdFourfoldOccurrences request) liveScale denominator input
    Finset.univ (modularCoefficientResidue equation prime.val)
    sample prime.val
    (modularResidualOffset (thresholdFourfoldOccurrences request)
      liveScale input equation prime.val)

theorem executableCanonicalThresholdSelectionRow_refines
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (selection : ThresholdChildSelection algorithm request)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalThresholdSelectionRow algorithm request liveScale
        denominator input selection prime sample =
      canonicalThresholdSelectionRow algorithm request liveScale
        denominator input selection prime sample := by
  unfold executableCanonicalThresholdSelectionRow
    canonicalThresholdSelectionRow
  exact executableCanonicalOccurrenceCoefficientRadixRow_refines
    (thresholdFourfoldOccurrences request) liveScale denominator input
    Finset.univ _ sample prime.val _

/-- One threshold child-selection polynomial with its frozen modular residual
offset explicit. -/
def structuralCanonicalThresholdSelectionRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ)
    (selection : ThresholdChildSelection algorithm request)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator)
    (residualOffset : ℕ) :
    StructuralGF2Polynomial :=
  let equation := thresholdSelectionEquation algorithm request selection
  structuralCanonicalOccurrenceCoefficientRadixRow
    (digits := modulusDigitCount prime.val)
    (thresholdFourfoldOccurrences request) liveScale denominator
    Finset.univ (modularCoefficientResidue equation prime.val)
    sample prime.val residualOffset

@[simp] theorem evaluateStructuralCanonicalThresholdSelectionRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (selection : ThresholdChildSelection algorithm request)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator)
    (residualOffset : ℕ)
    (hoffset :
      residualOffset =
        modularResidualOffset (thresholdFourfoldOccurrences request)
          liveScale input
          (thresholdSelectionEquation algorithm request selection)
          prime.val) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (thresholdFourfoldOccurrences request)
            (normalizedLiveSet
              (thresholdFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalThresholdSelectionRow algorithm request
          liveScale denominator selection prime sample residualOffset) =
      executableCanonicalThresholdSelectionRow algorithm request liveScale
        denominator input selection prime sample := by
  subst residualOffset
  unfold structuralCanonicalThresholdSelectionRow
    executableCanonicalThresholdSelectionRow
  exact evaluateStructuralCanonicalOccurrenceCoefficientRadixRow
    (digits := modulusDigitCount prime.val)
    (thresholdFourfoldOccurrences request) liveScale denominator input
    Finset.univ
    (modularCoefficientResidue
      (thresholdSelectionEquation algorithm request selection) prime.val)
    sample prime.val
    (modularResidualOffset (thresholdFourfoldOccurrences request)
      liveScale input
      (thresholdSelectionEquation algorithm request selection) prime.val)

def executableCanonicalThresholdPrimeRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator) : Bool :=
  finiteBoolDisjunction
    (fun selection : ThresholdChildSelection algorithm request =>
      executableCanonicalThresholdSelectionRow algorithm request liveScale
        denominator input selection prime sample)

theorem executableCanonicalThresholdPrimeRow_refines
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalThresholdPrimeRow algorithm request liveScale
        denominator input prime sample =
      canonicalThresholdPrimeRow algorithm request liveScale
        denominator input prime sample := by
  unfold executableCanonicalThresholdPrimeRow canonicalThresholdPrimeRow
  apply finiteBoolDisjunction_congr
  intro selection
  exact executableCanonicalThresholdSelectionRow_refines algorithm request
    liveScale denominator input selection prime sample

def executableCanonicalThresholdFourfoldRow
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale primeDenominator listDenominator : ℕ)
    (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request primeDenominator) ×
        NormalizedOccurrenceListSeed
          (thresholdFourfoldOccurrences request) liveScale listDenominator) :
    Bool :=
  executableCanonicalThresholdPrimeRow algorithm request liveScale
    listDenominator input sample.1 sample.2

theorem executableCanonicalThresholdFourfoldRow_refines
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale primeDenominator listDenominator : ℕ)
    (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request primeDenominator) ×
        NormalizedOccurrenceListSeed
          (thresholdFourfoldOccurrences request) liveScale listDenominator) :
    executableCanonicalThresholdFourfoldRow algorithm request liveScale
        primeDenominator listDenominator input sample =
      canonicalThresholdFourfoldRow algorithm request liveScale
        primeDenominator listDenominator input sample := by
  unfold executableCanonicalThresholdFourfoldRow canonicalThresholdFourfoldRow
  exact executableCanonicalThresholdPrimeRow_refines algorithm request
    liveScale listDenominator input sample.1 sample.2

/-- Executable mixed-radix code for the dependent Cartesian product of exact
top-child choices.  Empty child families produce the empty `Fin 0` index, so
the structural disjunction remains total without a special case. -/
def thresholdChildSelectionFinEquiv
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    ThresholdChildSelection algorithm request ≃
      Fin (∏ circuitIndex : Fin request.circuits.length,
        (topChildren algorithm
          (request.circuits.get circuitIndex)).length) :=
  finPiFinEquiv

/-- Structural threshold-prime row.  The external column fixes one residual
offset per exact child selection; all remaining dependence is on the shared
occurrence-residual variables. -/
def structuralCanonicalThresholdPrimeRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2FiniteDisjunction fun code :
      Fin (∏ circuitIndex : Fin request.circuits.length,
        (topChildren algorithm
          (request.circuits.get circuitIndex)).length) =>
    let selection :=
      (thresholdChildSelectionFinEquiv algorithm request).symm code
    structuralCanonicalThresholdSelectionRow algorithm request liveScale
      denominator selection prime sample (residualOffset selection)

@[simp] theorem evaluateStructuralCanonicalThresholdPrimeRow
    {cutoff : ℕ}
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed
      (thresholdFourfoldOccurrences request) liveScale denominator)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ)
    (hoffset : ∀ selection,
      residualOffset selection =
        modularResidualOffset (thresholdFourfoldOccurrences request)
          liveScale input
          (thresholdSelectionEquation algorithm request selection)
          prime.val) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (thresholdFourfoldOccurrences request)
            (normalizedLiveSet
              (thresholdFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalThresholdPrimeRow algorithm request liveScale
          denominator prime sample residualOffset) =
      executableCanonicalThresholdPrimeRow algorithm request liveScale
        denominator input prime sample := by
  rw [structuralCanonicalThresholdPrimeRow,
    evaluateStructuralGF2_finiteDisjunction]
  calc
    _ = finiteBoolDisjunction
        (fun code :
            Fin (∏ circuitIndex : Fin request.circuits.length,
              (topChildren algorithm
                (request.circuits.get circuitIndex)).length) =>
          executableCanonicalThresholdSelectionRow algorithm request
            liveScale denominator input
            ((thresholdChildSelectionFinEquiv algorithm request).symm code)
            prime sample) := by
      apply finiteBoolDisjunction_congr
      intro code
      exact evaluateStructuralCanonicalThresholdSelectionRow algorithm request
        liveScale denominator input
        ((thresholdChildSelectionFinEquiv algorithm request).symm code)
        prime sample _ (hoffset _)
    _ = finiteBoolDisjunction
        (fun selection : ThresholdChildSelection algorithm request =>
          executableCanonicalThresholdSelectionRow algorithm request
            liveScale denominator input selection prime sample) := by
      exact finiteBoolDisjunction_equiv
        (thresholdChildSelectionFinEquiv algorithm request).symm
        (fun selection : ThresholdChildSelection algorithm request =>
          executableCanonicalThresholdSelectionRow algorithm request
            liveScale denominator input selection prime sample)
    _ = executableCanonicalThresholdPrimeRow algorithm request liveScale
          denominator input prime sample := rfl

/-- Full structural threshold row for the prime/list sample selected by the
public row index. -/
def structuralCanonicalThresholdFourfoldRow
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale primeDenominator listDenominator : ℕ)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request primeDenominator) ×
        NormalizedOccurrenceListSeed
          (thresholdFourfoldOccurrences request) liveScale listDenominator)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ) :
    StructuralGF2Polynomial :=
  structuralCanonicalThresholdPrimeRow algorithm request liveScale
    listDenominator sample.1 sample.2 residualOffset

@[simp] theorem evaluateStructuralCanonicalThresholdFourfoldRow
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale primeDenominator listDenominator : ℕ)
    (input : BitInput request.q)
    (sample :
      PrimeIndex
          (thresholdPrimeCutoff algorithm request primeDenominator) ×
        NormalizedOccurrenceListSeed
          (thresholdFourfoldOccurrences request) liveScale listDenominator)
    (residualOffset : ThresholdChildSelection algorithm request → ℕ)
    (hoffset : ∀ selection,
      residualOffset selection =
        modularResidualOffset (thresholdFourfoldOccurrences request)
          liveScale input
          (thresholdSelectionEquation algorithm request selection)
          sample.1.val) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (thresholdFourfoldOccurrences request)
            (normalizedLiveSet
              (thresholdFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalThresholdFourfoldRow algorithm request liveScale
          primeDenominator listDenominator sample residualOffset) =
      executableCanonicalThresholdFourfoldRow algorithm request liveScale
        primeDenominator listDenominator input sample := by
  unfold structuralCanonicalThresholdFourfoldRow
    executableCanonicalThresholdFourfoldRow
  exact evaluateStructuralCanonicalThresholdPrimeRow algorithm request
    liveScale listDenominator input sample.1 sample.2 residualOffset hoffset

/-! ## Residual variables to imported exact equations -/

/-- Exact children for one physical bottom-gate occurrence.  Every occurrence
is decomposed separately, even when two gates are definitionally equal. -/
def occurrenceExactChildren
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) : List (ExactThresholdGate q) :=
  (algorithm.run
    (CompilerSemantics.nonStrictAsStrict
      (occurrences.get index).gate)).children

/-- The one total decoder for pair-coded exact children.  Keeping decoding
here prevents the semantic equation and Boolean assignment paths from
silently disagreeing on malformed addresses. -/
def occurrenceExactChild?
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (code : ℕ) : Option (ExactThresholdGate q) :=
  let address := Nat.unpair code
  if hoccurrence : address.1 < occurrences.length then
    let index : Fin occurrences.length := ⟨address.1, hoccurrence⟩
    if hchild : address.2 <
        (occurrenceExactChildren algorithm occurrences index).length then
      some ((occurrenceExactChildren algorithm occurrences index).get
        ⟨address.2, hchild⟩)
    else
      none
  else
    none

/-- Pair-coded exact-child assignment.  Invalid occurrence or child addresses
are false; generated atoms below use only canonical in-range pairs. -/
def occurrenceExactChildAssignment
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (code : ℕ) : Bool :=
  match occurrenceExactChild? algorithm occurrences code with
  | some child => child.eval input
  | none => false

@[simp] theorem occurrenceExactChildAssignment_pair
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (index : Fin occurrences.length)
    (childIndex :
      Fin (occurrenceExactChildren algorithm occurrences index).length) :
    occurrenceExactChildAssignment algorithm occurrences input
        (Nat.pair index.val childIndex.val) =
      ((occurrenceExactChildren algorithm occurrences index).get
        childIndex).eval input := by
  simp [occurrenceExactChildAssignment, occurrenceExactChild?,
    index.isLt, childIndex.isLt]

/-- Disjointness of the imported decomposition turns its exact-child OR into
linear GF(2) parity. -/
theorem occurrenceExactChildren_parity_eq
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (index : Fin occurrences.length) :
    boolParity
        (fun childIndex :
            Fin (occurrenceExactChildren algorithm occurrences index).length =>
          ((occurrenceExactChildren algorithm occurrences index).get
            childIndex).eval input) =
      (occurrences.get index).eval input := by
  let gate := (occurrences.get index).gate
  let decomposition :=
    algorithm.run (CompilerSemantics.nonStrictAsStrict gate)
  calc
    boolParity
        (fun childIndex : Fin decomposition.children.length =>
          (decomposition.children.get childIndex).eval input) =
        decomposition.children.any (fun child => child.eval input) :=
      boolParity_finGet_eq_any_of_disjoint decomposition.children
        (fun child => child.eval input) (decomposition.disjoint input)
    _ = (CompilerSemantics.nonStrictAsStrict gate).strictEval input :=
      (decomposition.equivalent input).symm
    _ = gate.eval input :=
      CompilerSemantics.nonStrictAsStrict_eval gate input
    _ = (occurrences.get index).eval input := rfl

/-- One occurrence residual lowered to imported exact-child variables.  A
frozen-one residual is identically zero; otherwise disjoint exact children are
added in GF(2). -/
def structuralOccurrenceResidualAtom
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (index : Fin occurrences.length) : StructuralGF2Polynomial :=
  if constant index then
    structuralGF2Zero
  else
    structuralGF2FinParity fun childIndex :
        Fin (occurrenceExactChildren algorithm occurrences index).length =>
      structuralGF2Variable (Nat.pair index.val childIndex.val)

@[simp] theorem evaluateStructuralOccurrenceResidualAtom
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (constant : Fin occurrences.length → Bool)
    (index : Fin occurrences.length)
    (hconstant :
      constant index =
        occurrenceResidualConstant occurrences live input index) :
    evaluateStructuralGF2
        (occurrenceExactChildAssignment algorithm occurrences input)
        (structuralOccurrenceResidualAtom algorithm occurrences constant index) =
      occurrenceResidualVariable occurrences live input index := by
  cases hresidualConstant :
      occurrenceResidualConstant occurrences live input index with
  | false =>
      have hconstantFalse : constant index = false :=
        hconstant.trans hresidualConstant
      have hresidualGate :
          residualConstant (occurrences.get index).gate live input = false := by
        simpa [occurrenceResidualConstant] using hresidualConstant
      rw [structuralOccurrenceResidualAtom, hconstantFalse]
      simp only [Bool.false_eq_true, ↓reduceIte,
        evaluateStructuralGF2_finParity,
        evaluateStructuralGF2_variable,
        occurrenceExactChildAssignment_pair]
      rw [occurrenceExactChildren_parity_eq]
      unfold occurrenceResidualVariable residualVariable
        SupportedNormalizedGate.eval
      rw [hresidualGate]
      cases (occurrences.get index).gate.eval input <;> rfl
  | true =>
      have hconstantTrue : constant index = true :=
        hconstant.trans hresidualConstant
      have hresidualGate :
          residualConstant (occurrences.get index).gate live input = true := by
        simpa [occurrenceResidualConstant] using hresidualConstant
      have hgate :
          (occurrences.get index).gate.eval input = true :=
        residualConstant_implies_gate (occurrences.get index).gate live input
          hresidualGate
      rw [structuralOccurrenceResidualAtom]
      simp only [hconstantTrue, ↓reduceIte,
        evaluateStructuralGF2_zero]
      unfold occurrenceResidualVariable residualVariable
      rw [hresidualGate, hgate]
      rfl

/-- Total source-code lowering used by structural substitution. -/
def structuralOccurrenceResidualAtomOfCode
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (code : ℕ) : StructuralGF2Polynomial :=
  if hcode : code < occurrences.length then
    structuralOccurrenceResidualAtom algorithm occurrences constant
      ⟨code, hcode⟩
  else
    structuralGF2Zero

/-- The unique exact-child expansion of a canonical structural row. -/
def structuralOccurrenceExactPolynomial
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (polynomial : StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  structuralGF2Substitute
    (structuralOccurrenceResidualAtomOfCode algorithm occurrences constant)
    polynomial

@[simp] theorem evaluateStructuralOccurrenceExactPolynomial
    {q : ℕ} (algorithm : ExecutableExactDecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (constant : Fin occurrences.length → Bool)
    (hconstant : ∀ index,
      constant index =
        occurrenceResidualConstant occurrences live input index)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2
        (occurrenceExactChildAssignment algorithm occurrences input)
        (structuralOccurrenceExactPolynomial algorithm occurrences
          constant polynomial) =
      evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences live input index)
        polynomial := by
  rw [structuralOccurrenceExactPolynomial,
    evaluateStructuralGF2_substitute]
  congr 1
  funext code
  by_cases hcode : code < occurrences.length
  · simpa [structuralOccurrenceResidualAtomOfCode,
      encodedFiniteBooleanAssignment, hcode] using
      evaluateStructuralOccurrenceResidualAtom algorithm occurrences live input
        constant ⟨code, hcode⟩ (hconstant ⟨code, hcode⟩)
  · simp [structuralOccurrenceResidualAtomOfCode,
      encodedFiniteBooleanAssignment, hcode]

/-! ## One five-field row ABI -/

def normalizedEstimatorModeCode : NormalizedEstimatorMode → ℕ
  | .symmetric => 0
  | .threshold => 1

def decodeNormalizedEstimatorMode : ℕ → Option NormalizedEstimatorMode
  | 0 => some .symmetric
  | 1 => some .threshold
  | _ => none

@[simp] theorem decodeNormalizedEstimatorMode_code
    (mode : NormalizedEstimatorMode) :
    decodeNormalizedEstimatorMode (normalizedEstimatorModeCode mode) =
      some mode := by
  cases mode <;> rfl

/-- The sole row-call record.  The envelope is already the canonical
family/arity/circuit-list handoff; all other numeric fields use the unique
canonical natural encoding. -/
structure FourfoldRowRequest where
  mode : NormalizedEstimatorMode
  q : ℕ
  envelopeCode : ℕ
  rowIndex : ℕ
  inputCode : ℕ
  deriving DecidableEq, Repr

def FourfoldRowRequest.code (request : FourfoldRowRequest) : ℕ :=
  encodeBalancedList
    [ normalizedEstimatorModeCode request.mode
    , request.q
    , request.envelopeCode
    , request.rowIndex
    , request.inputCode
    ]

private def decodeFourfoldRowRequestCandidate
    (code : ℕ) : Option FourfoldRowRequest :=
  match decodeBalancedList code with
  | some [modeCode, q, envelopeCode, rowIndex, inputCode] =>
      match decodeNormalizedEstimatorMode modeCode with
      | some mode =>
          some
            { mode := mode
              q := q
              envelopeCode := envelopeCode
              rowIndex := rowIndex
              inputCode := inputCode }
      | none => none
  | _ => none

/-- Malformed, noncanonical, or wrong-shape row calls are rejected. -/
def decodeFourfoldRowRequest (code : ℕ) : Option FourfoldRowRequest :=
  (decodeFourfoldRowRequestCandidate code).bind fun request =>
    if request.code = code then some request else none

@[simp] theorem decodeFourfoldRowRequest_code
    (request : FourfoldRowRequest) :
    decodeFourfoldRowRequest request.code = some request := by
  cases request with
  | mk mode q envelopeCode rowIndex inputCode =>
      cases mode <;>
        simp [FourfoldRowRequest.code, decodeFourfoldRowRequest,
          decodeFourfoldRowRequestCandidate, normalizedEstimatorModeCode,
          decodeNormalizedEstimatorMode]

theorem FourfoldRowRequest.code_of_decode
    {code : ℕ} {request : FourfoldRowRequest}
    (hdecode : decodeFourfoldRowRequest code = some request) :
    request.code = code := by
  unfold decodeFourfoldRowRequest at hdecode
  generalize hcandidate :
    decodeFourfoldRowRequestCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

/-! ## Fixed public-ABI decoder -/

/-- Right-associated internal handoff.  Public framing remains the canonical
balanced five-atom tree; the VM removes that framing exactly once so every
later stage can use the machine's native pair projections. -/
def FourfoldRowRequest.handoffCode (request : FourfoldRowRequest) : ℕ :=
  Nat.pair (normalizedEstimatorModeCode request.mode)
    (Nat.pair request.q
      (Nat.pair request.envelopeCode
        (Nat.pair request.rowIndex request.inputCode)))

/-- Fixed-shape balanced decoder.  Registers `r2`--`r6` hold mode, arity,
envelope, row index, and input respectively before the handoff is repacked in
`r0`; all other registers are scratch. -/
def fourfoldRowEnvelopeProgram : NPOracleProgram :=
  [ .unpairRight 0 7 1
  , .unpairLeft 7 8 2
  , .unpairRight 7 9 3
  , .unpairRight 8 10 4
  , .unpairLeft 10 11 5
  , .unpairRight 10 12 6
  , .unpairRight 11 13 7
  , .unpairLeft 13 14 8
  , .unpairRight 13 15 9
  , .unpairRight 14 2 10
  , .unpairRight 15 3 11
  , .unpairRight 12 4 12
  , .unpairRight 9 16 13
  , .unpairLeft 16 17 14
  , .unpairRight 16 18 15
  , .unpairRight 17 5 16
  , .unpairRight 18 6 17
  , .pair 5 6 19 18
  , .pair 4 19 19 19
  , .pair 3 19 19 20
  , .pair 2 19 0 21
  , .halt 0
  ]

@[simp] theorem fourfoldRowEnvelopeProgram_oracleFree :
    OracleFree fourfoldRowEnvelopeProgram := by
  rfl

def fourfoldRowEnvelopeRegisterBound
    (request : FourfoldRowRequest) : ℕ :=
  max request.code request.handoffCode + 1

def fourfoldRowEnvelopeBits (request : FourfoldRowRequest) : ℕ :=
  natBitLength (fourfoldRowEnvelopeRegisterBound request)

private theorem rowEnvelope_boundedValueBits
    {request : FourfoldRowRequest} {value maximumBits : ℕ}
    (hvalue : value ≤ fourfoldRowEnvelopeRegisterBound request)
    (hbits : fourfoldRowEnvelopeBits request ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

theorem run_fourfoldRowEnvelopeProgram
    (request : FourfoldRowRequest) (maximumBits : ℕ)
    (hbits : fourfoldRowEnvelopeBits request ≤ maximumBits) :
    runNPOracleProgram fourfoldRowEnvelopeProgram maximumBits 22
        (initialNPOracleState request.q request.code) =
      some request.handoffCode := by
  let modeCode := normalizedEstimatorModeCode request.mode
  let modeLeaf := Nat.pair 1 modeCode
  let qLeaf := Nat.pair 1 request.q
  let envelopeLeaf := Nat.pair 1 request.envelopeCode
  let rowLeaf := Nat.pair 1 request.rowIndex
  let inputLeaf := Nat.pair 1 request.inputCode
  let modeQPayload := Nat.pair modeLeaf qLeaf
  let modeQNode := Nat.pair 2 modeQPayload
  let leftPayload := Nat.pair modeQNode envelopeLeaf
  let leftNode := Nat.pair 2 leftPayload
  let rightPayload := Nat.pair rowLeaf inputLeaf
  let rightNode := Nat.pair 2 rightPayload
  let rootPayload := Nat.pair leftNode rightNode
  let raw := Nat.pair 2 rootPayload
  let rowInput := Nat.pair request.rowIndex request.inputCode
  let envelopeTail := Nat.pair request.envelopeCode rowInput
  let qTail := Nat.pair request.q envelopeTail
  let output := Nat.pair modeCode qTail
  have hrawEq : request.code = raw := by
    simp [FourfoldRowRequest.code, raw, rootPayload, leftNode,
      rightNode, leftPayload, rightPayload, modeQNode, modeQPayload,
      modeLeaf, qLeaf, envelopeLeaf, rowLeaf, inputLeaf, modeCode,
      encodeBalancedList]
  have houtputEq : request.handoffCode = output := by
    rfl
  have hrawBits : natBitLength raw ≤ maximumBits := by
    apply rowEnvelope_boundedValueBits (request := request) (hbits := hbits)
    rw [fourfoldRowEnvelopeRegisterBound, hrawEq, houtputEq]
    omega
  have houtputBits : natBitLength output ≤ maximumBits := by
    apply rowEnvelope_boundedValueBits (request := request) (hbits := hbits)
    rw [fourfoldRowEnvelopeRegisterBound, hrawEq, houtputEq]
    omega
  have hrootPayloadBits : natBitLength rootPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 2 rootPayload)).trans hrawBits
  have hleftNodeBits : natBitLength leftNode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair leftNode rightNode)).trans hrootPayloadBits
  have hrightNodeBits : natBitLength rightNode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair leftNode rightNode)).trans hrootPayloadBits
  have hleftPayloadBits : natBitLength leftPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 2 leftPayload)).trans hleftNodeBits
  have hmodeQNodeBits : natBitLength modeQNode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair modeQNode envelopeLeaf)).trans hleftPayloadBits
  have henvelopeLeafBits : natBitLength envelopeLeaf ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeQNode envelopeLeaf)).trans hleftPayloadBits
  have hmodeQPayloadBits : natBitLength modeQPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 2 modeQPayload)).trans hmodeQNodeBits
  have hmodeLeafBits : natBitLength modeLeaf ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair modeLeaf qLeaf)).trans hmodeQPayloadBits
  have hqLeafBits : natBitLength qLeaf ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeLeaf qLeaf)).trans hmodeQPayloadBits
  have hrightPayloadBits : natBitLength rightPayload ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 2 rightPayload)).trans hrightNodeBits
  have hrowLeafBits : natBitLength rowLeaf ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair rowLeaf inputLeaf)).trans hrightPayloadBits
  have hinputLeafBits : natBitLength inputLeaf ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair rowLeaf inputLeaf)).trans hrightPayloadBits
  have hmodeBits : natBitLength modeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1 modeCode)).trans hmodeLeafBits
  have hqBits : natBitLength request.q ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1 request.q)).trans hqLeafBits
  have henvelopeBits : natBitLength request.envelopeCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1 request.envelopeCode)).trans henvelopeLeafBits
  have hrowBits : natBitLength request.rowIndex ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1 request.rowIndex)).trans hrowLeafBits
  have hinputBits : natBitLength request.inputCode ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair 1 request.inputCode)).trans hinputLeafBits
  have hrowInputBits : natBitLength rowInput ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair request.envelopeCode rowInput)).trans <|
        (natBitLength_mono
          (Nat.right_le_pair request.q envelopeTail)).trans <|
            (natBitLength_mono
              (Nat.right_le_pair modeCode qTail)).trans houtputBits
  have henvelopeTailBits : natBitLength envelopeTail ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair request.q envelopeTail)).trans <|
        (natBitLength_mono
          (Nat.right_le_pair modeCode qTail)).trans houtputBits
  have hqTailBits : natBitLength qTail ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair modeCode qTail)).trans houtputBits
  rw [hrawEq, houtputEq]
  simp [fourfoldRowEnvelopeProgram, raw, output, rootPayload,
    leftNode, rightNode, leftPayload, rightPayload, modeQNode,
    modeQPayload, modeLeaf, qLeaf, envelopeLeaf, rowLeaf, inputLeaf,
    rowInput, envelopeTail, qTail, runNPOracleProgram,
    initialNPOracleState, NPOracleState.boundedWrite,
    NPOracleState.write, NPOracleState.jump,
    hrootPayloadBits, hleftNodeBits, hrightNodeBits, hleftPayloadBits,
    hmodeQNodeBits, henvelopeLeafBits, hmodeQPayloadBits, hmodeLeafBits,
    hqLeafBits, hrightPayloadBits, hrowLeafBits, hinputLeafBits,
    hmodeBits, hqBits, henvelopeBits, hrowBits, hinputBits,
    hrowInputBits, henvelopeTailBits, hqTailBits, houtputBits]

/-! ## Reusable binary machine arithmetic -/

/-- The comparator's request ABI: a callee is entered with its operand in `r0`
and the public length in `r1`, and this stage is always called with `left` and
`right` in exactly those two registers.  One increment and one pairing turn the
pending question `left < right` into the fixed native question
`left + 1 ≤ right`. -/
private def binaryNatLtPrepareProgram : NPOracleProgram :=
  [ .increment 0 1
  , .pair 0 1 0 2
  , .halt 0
  ]

private theorem binaryNatLtPrepareProgram_oracleFree :
    OracleFree binaryNatLtPrepareProgram := by
  rfl

/-- Binary less-than.  The earlier stage decremented scratch copies of both
operands in lockstep, so its charge was `Θ(min left right)` — a magnitude, not
a width — and every caller of this comparator inherited that exponential
budget.  The production stage instead poses the equivalent question
`left + 1 ≤ right` to the fixed native comparator of
`CanonicalBinaryArithmeticProgram`, whose scan is charged by the operands'
binary widths.  The public surface `binaryNatLtProgram`,
`binaryNatLtProgram_oracleFree`, `binaryNatLtLoopFuel`, `binaryNatLtBits` and
`run_binaryNatLtProgram` is unchanged. -/
def binaryNatLtProgram : NPOracleProgram :=
  linkPrograms binaryNatLtPrepareProgram nativeNatLeProgram

@[simp] theorem binaryNatLtProgram_oracleFree :
    OracleFree binaryNatLtProgram :=
  oracleFree_linkPrograms binaryNatLtPrepareProgram_oracleFree
    nativeNatLeProgram_oracleFree

/-- One comparison costs three preparation instructions, the linker's fixed
plumbing, and the width-linear native scan. -/
def binaryNatLtLoopFuel (left right : ℕ) : ℕ :=
  programRegisterSpan nativeNatLeProgram + 6 +
    nativeNatLeFuel (left + 1) right

def binaryNatLtBits (left right : ℕ) : ℕ :=
  max 1 <| max (natBitLength right) (nativeNatLeBits (left + 1) right)

private theorem run_binaryNatLtPrepareProgram
    (left right maximumBits : ℕ)
    (hbits : binaryNatLtBits left right ≤ maximumBits) :
    runNPOracleProgram binaryNatLtPrepareProgram maximumBits 3
        (initialNPOracleState right left) =
      some (nativeNatLeInput (left + 1) right) := by
  have hpair :
      natBitLength (nativeNatLeInput (left + 1) right) ≤ maximumBits :=
    le_trans (by simp [binaryNatLtBits, nativeNatLeBits]) hbits
  have hsuccessor : natBitLength (left + 1) ≤ maximumBits := by
    refine le_trans (natBitLength_mono ?_) hpair
    exact Nat.left_le_pair (left + 1) right
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_increment_instruction (value := left + 1)
    (by rfl) rfl
    (by simp [initialNPOracleState]) hsuccessor]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := nativeNatLeInput (left + 1) right)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        nativeNatLeInput])
    hpair]
  exact run_halt_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair

private theorem nativeNatLeOutput_successor (left right : ℕ) :
    nativeNatLeOutput (left + 1) right =
      (decide (left < right)).toNat := by
  rw [nativeNatLeOutput_eq]
  congr 1

theorem run_binaryNatLtProgram
    (left right maximumBits : ℕ)
    (hbits : binaryNatLtBits left right ≤ maximumBits) :
    runNPOracleProgram binaryNatLtProgram maximumBits
        (2 + binaryNatLtLoopFuel left right)
        (initialNPOracleState right left) =
      some (decide (left < right)).toNat := by
  have hpositive : 1 ≤ maximumBits :=
    le_trans (by simp [binaryNatLtBits]) hbits
  have hlength : natBitLength right ≤ maximumBits :=
    le_trans (by simp [binaryNatLtBits]) hbits
  have hcompareBits : nativeNatLeBits (left + 1) right ≤ maximumBits :=
    le_trans (by simp [binaryNatLtBits]) hbits
  have hprepare :
      runNPOracleProgram binaryNatLtPrepareProgram maximumBits 3
          (initialNPOracleState right left) =
        some (nativeNatLeInput (left + 1) right) :=
    run_binaryNatLtPrepareProgram left right maximumBits hbits
  have hcompare :
      runNPOracleProgram nativeNatLeProgram maximumBits
          (nativeNatLeFuel (left + 1) right)
          (initialNPOracleState right (nativeNatLeInput (left + 1) right)) =
        some (decide (left < right)).toNat := by
    rw [← nativeNatLeOutput_successor left right]
    exact run_bits_mono
      (run_nativeNatLeProgram right (left + 1) right) hcompareBits
  have hfuel :
      2 + binaryNatLtLoopFuel left right =
        linkFuel nativeNatLeProgram 3
          (nativeNatLeFuel (left + 1) right) := by
    simp only [binaryNatLtLoopFuel, linkFuel]
    omega
  rw [binaryNatLtProgram, hfuel]
  exact run_linkPrograms hpositive hlength hprepare hcompare

/-- **The comparator's charge is linear in the operands' binary widths.**  No
term of `binaryNatLtLoopFuel` grows with an operand magnitude; this is the fact
every less-than caller's polynomial envelope consumes. -/
theorem binaryNatLtLoopFuel_le (left right : ℕ) :
    binaryNatLtLoopFuel left right ≤
      programRegisterSpan nativeNatLeProgram + 14 +
        36 * max (natBitLength (left + 1)) (natBitLength right) := by
  have hscan := nativeNatLeFuel_le (left + 1) right
  have hpair := pairCodeBits_le (left + 1) right
  have hwidth :
      nativeNatLeBits (left + 1) right ≤
        2 * max (natBitLength (left + 1)) (natBitLength right) := by
    simpa [nativeNatLeBits, nativeNatLeInput] using hpair
  unfold binaryNatLtLoopFuel
  omega

/-- Destructive binary addition.  The second operand is copied to `r2` and
consumed; `r0` grows monotonically to the sum, so a bound on the final sum is
also a bound on every intermediate register value. -/
def binaryNatAddProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .branchZero 2 5 2
  , .increment 0 3
  , .decrement 2 4
  , .branchZero 3 1 1
  , .halt 0
  ]

@[simp] theorem binaryNatAddProgram_oracleFree :
    OracleFree binaryNatAddProgram := by
  rfl

def binaryNatAddLoopFuel : ℕ → ℕ
  | 0 => 2
  | counter + 1 => 4 + binaryNatAddLoopFuel counter

private theorem run_binaryNatAddLoop
    (accumulator counter maximumBits : ℕ) (state : NPOracleState)
    (hpc : state.pc = 1)
    (haccumulator : state.registers 0 = accumulator)
    (hcounter : state.registers 2 = counter)
    (hzero : state.registers 3 = 0)
    (hsumBits :
      natBitLength (accumulator + counter) ≤ maximumBits) :
    runNPOracleProgram binaryNatAddProgram maximumBits
        (binaryNatAddLoopFuel counter) state =
      some (accumulator + counter) := by
  induction counter generalizing accumulator state with
  | zero =>
      rw [show binaryNatAddLoopFuel 0 = 1 + 1 by rfl]
      rw [run_branchZero_instruction (fuel := 1) (by rfl) hpc]
      rw [hcounter, if_pos rfl]
      rw [show 1 = 0 + 1 by rfl]
      rw [run_halt_instruction (state := state.jump 5)
        (fuel := 0) (value := accumulator)
        (by rfl) rfl haccumulator (by simpa using hsumBits)]
      simp
  | succ counter inductionHypothesis =>
      have hincLe :
          accumulator + 1 ≤ accumulator + (counter + 1) := by
        omega
      have hincBits :
          natBitLength (accumulator + 1) ≤ maximumBits :=
        (natBitLength_mono hincLe).trans hsumBits
      have hnextSum :
          (accumulator + 1) + counter =
            accumulator + (counter + 1) := by
        omega
      have hnextSumBits :
          natBitLength ((accumulator + 1) + counter) ≤ maximumBits := by
        rw [hnextSum]
        exact hsumBits
      rw [show binaryNatAddLoopFuel (counter + 1) =
        (3 + binaryNatAddLoopFuel counter) + 1 by
          simp only [binaryNatAddLoopFuel]
          omega]
      rw [run_branchZero_instruction
        (fuel := 3 + binaryNatAddLoopFuel counter) (by rfl) hpc]
      rw [hcounter, if_neg (Nat.succ_ne_zero counter)]
      rw [show 3 + binaryNatAddLoopFuel counter =
        (2 + binaryNatAddLoopFuel counter) + 1 by omega]
      rw [run_increment_instruction
        (fuel := 2 + binaryNatAddLoopFuel counter)
        (value := accumulator + 1) (by rfl) rfl
        (by exact congrArg (fun value => value + 1) haccumulator)
        hincBits]
      rw [show 2 + binaryNatAddLoopFuel counter =
        (1 + binaryNatAddLoopFuel counter) + 1 by omega]
      rw [run_decrement_instruction
        (fuel := 1 + binaryNatAddLoopFuel counter)
        (value := counter) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcounter])
        ((decrement_bits_le (counter + 1)).trans <|
          (natBitLength_mono (by omega)).trans hsumBits)]
      rw [show 1 + binaryNatAddLoopFuel counter =
        binaryNatAddLoopFuel counter + 1 by omega]
      rw [run_branchZero_instruction
        (fuel := binaryNatAddLoopFuel counter) (by rfl) rfl]
      simp only [NPOracleState.write, NPOracleState.jump, hzero]
      rw [inductionHypothesis (accumulator := accumulator + 1) _
        rfl
        (by simp)
        (by simp)
        (by simp [hzero])
        hnextSumBits]
      rw [hnextSum]

def binaryNatAddBits (left right : ℕ) : ℕ :=
  natBitLength (left + right)

theorem run_binaryNatAddProgram
    (left right maximumBits : ℕ)
    (hbits : binaryNatAddBits left right ≤ maximumBits) :
    runNPOracleProgram binaryNatAddProgram maximumBits
        (1 + binaryNatAddLoopFuel right)
        (initialNPOracleState right left) =
      some (left + right) := by
  have hrightBits : natBitLength right ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hbits
  rw [show 1 + binaryNatAddLoopFuel right =
    binaryNatAddLoopFuel right + 1 by omega]
  rw [run_copy_instruction
    (fuel := binaryNatAddLoopFuel right) (value := right)
    (by rfl) rfl (by simp [initialNPOracleState]) hrightBits]
  exact run_binaryNatAddLoop left right maximumBits _ rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hbits

/-- Fixed square-root controller.  It maintains
`square = candidate²` and `odd = 2*candidate+1`, compares `square` with the
input by lockstep decrement, and advances with
`(candidate+1)² = square+odd`. -/
def binaryNatCeilSqrtProgram : NPOracleProgram :=
  [ .set 1 0 1
  , .set 2 0 2
  , .set 3 1 3
  , .set 7 0 4
  , .copy 2 4 5
  , .copy 0 5 6
  , .branchZero 4 10 7
  , .branchZero 5 16 8
  , .decrement 4 9
  , .decrement 5 6
  , .branchZero 5 16 11
  , .copy 3 6 12
  , .branchZero 6 15 13
  , .increment 2 14
  , .decrement 6 12
  , .increment 1 17
  , .copy 1 0 20
  , .increment 3 18
  , .increment 3 19
  , .branchZero 7 4 4
  , .halt 0
  ]

@[simp] theorem binaryNatCeilSqrtProgram_oracleFree :
    OracleFree binaryNatCeilSqrtProgram := by
  rfl

/-- Comparison mutates only its two cursors.  Keeping this relation abstract
lets the exact trace proof compose with either the advance or halt branch
without exposing an implementation-specific scratch-state normal form. -/
private def PreservesOutside45
    (before after : NPOracleState) : Prop :=
  ∀ register, register ≠ 4 → register ≠ 5 →
    after.registers register = before.registers register

private theorem preservesOutside45_trans
    {first middle last : NPOracleState}
    (hfirst : PreservesOutside45 first middle)
    (hlast : PreservesOutside45 middle last) :
    PreservesOutside45 first last := by
  intro register hfour hfive
  exact (hlast register hfour hfive).trans
    (hfirst register hfour hfive)

private def binaryNatCeilSqrtCompareFuel (operand : ℕ) : ℕ :=
  4 * operand + 2

private theorem run_binaryNatCeilSqrtCompare_lt
    (square value maximumBits extraFuel output : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 6)
    (hsquare : state.registers 4 = square)
    (hvalue : state.registers 5 = value)
    (hlt : square < value)
    (hsquareBits : natBitLength square ≤ maximumBits)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hcontinue : ∀ nextState,
      PreservesOutside45 state nextState →
      nextState.pc = 11 →
      runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        extraFuel nextState = some output) :
    runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        (binaryNatCeilSqrtCompareFuel square + extraFuel) state =
      some output := by
  induction square generalizing value state with
  | zero =>
      cases value with
      | zero => omega
      | succ value =>
          rw [show binaryNatCeilSqrtCompareFuel 0 + extraFuel =
            (1 + extraFuel) + 1 by
              unfold binaryNatCeilSqrtCompareFuel
              omega]
          rw [run_branchZero_instruction
            (fuel := 1 + extraFuel) (by rfl) hpc]
          rw [hsquare, if_pos rfl]
          rw [show 1 + extraFuel = extraFuel + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := extraFuel) (by rfl) rfl]
          rw [show (state.jump 10).registers 5 = value + 1 by
            exact hvalue]
          rw [if_neg (Nat.succ_ne_zero value)]
          apply hcontinue
          · intro register hfour hfive
            rfl
          · rfl
  | succ square inductionHypothesis =>
      cases value with
      | zero => omega
      | succ value =>
          have hsquarePredBits :
              natBitLength square ≤ maximumBits :=
            (decrement_bits_le (square + 1)).trans hsquareBits
          have hvaluePredBits :
              natBitLength value ≤ maximumBits :=
            (decrement_bits_le (value + 1)).trans hvalueBits
          rw [show
            binaryNatCeilSqrtCompareFuel (square + 1) + extraFuel =
              (3 +
                (binaryNatCeilSqrtCompareFuel square + extraFuel)) + 1 by
                simp [binaryNatCeilSqrtCompareFuel]
                omega]
          rw [run_branchZero_instruction
            (fuel := 3 +
              (binaryNatCeilSqrtCompareFuel square + extraFuel))
            (by rfl) hpc]
          rw [hsquare, if_neg (Nat.succ_ne_zero square)]
          rw [show
            3 + (binaryNatCeilSqrtCompareFuel square + extraFuel) =
              (2 +
                (binaryNatCeilSqrtCompareFuel square + extraFuel)) + 1 by
                omega]
          rw [run_branchZero_instruction
            (fuel := 2 +
              (binaryNatCeilSqrtCompareFuel square + extraFuel))
            (by rfl) rfl]
          rw [show (state.jump 7).registers 5 = value + 1 by
            exact hvalue]
          rw [if_neg (Nat.succ_ne_zero value)]
          rw [show
            2 + (binaryNatCeilSqrtCompareFuel square + extraFuel) =
              (1 +
                (binaryNatCeilSqrtCompareFuel square + extraFuel)) + 1 by
                omega]
          rw [run_decrement_instruction
            (fuel := 1 +
              (binaryNatCeilSqrtCompareFuel square + extraFuel))
            (value := square) (by rfl) rfl
            (by simp [NPOracleState.jump, hsquare]) hsquarePredBits]
          rw [show
            1 + (binaryNatCeilSqrtCompareFuel square + extraFuel) =
              (binaryNatCeilSqrtCompareFuel square + extraFuel) + 1 by
                omega]
          rw [run_decrement_instruction
            (fuel := binaryNatCeilSqrtCompareFuel square + extraFuel)
            (value := value) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hvalue])
            hvaluePredBits]
          apply inductionHypothesis value _
          · rfl
          · simp
          · simp
          · omega
          · exact hsquarePredBits
          · exact hvaluePredBits
          · intro finalState hpreserved hfinalPc
            apply hcontinue finalState
              (preservesOutside45_trans (by
                intro register hfour hfive
                simp [NPOracleState.write, NPOracleState.jump,
                  hfour, hfive]) hpreserved)
              hfinalPc

private theorem run_binaryNatCeilSqrtCompare_not_lt
    (square value maximumBits extraFuel output : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 6)
    (hsquare : state.registers 4 = square)
    (hvalue : state.registers 5 = value)
    (hnotLt : ¬ square < value)
    (hsquareBits : natBitLength square ≤ maximumBits)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hcontinue : ∀ nextState,
      PreservesOutside45 state nextState →
      nextState.pc = 16 →
      runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        extraFuel nextState = some output) :
    runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        (binaryNatCeilSqrtCompareFuel value + extraFuel) state =
      some output := by
  induction value generalizing square state with
  | zero =>
      cases square with
      | zero =>
          rw [show binaryNatCeilSqrtCompareFuel 0 + extraFuel =
            (1 + extraFuel) + 1 by
              unfold binaryNatCeilSqrtCompareFuel
              omega]
          rw [run_branchZero_instruction
            (fuel := 1 + extraFuel) (by rfl) hpc]
          rw [hsquare, if_pos rfl]
          rw [show 1 + extraFuel = extraFuel + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := extraFuel) (by rfl) rfl]
          rw [show (state.jump 10).registers 5 = 0 by exact hvalue]
          rw [if_pos rfl]
          apply hcontinue
          · intro register hfour hfive
            rfl
          · rfl
      | succ square =>
          rw [show binaryNatCeilSqrtCompareFuel 0 + extraFuel =
            (1 + extraFuel) + 1 by
              unfold binaryNatCeilSqrtCompareFuel
              omega]
          rw [run_branchZero_instruction
            (fuel := 1 + extraFuel) (by rfl) hpc]
          rw [hsquare, if_neg (Nat.succ_ne_zero square)]
          rw [show 1 + extraFuel = extraFuel + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := extraFuel) (by rfl) rfl]
          rw [show (state.jump 7).registers 5 = 0 by exact hvalue]
          rw [if_pos rfl]
          apply hcontinue
          · intro register hfour hfive
            rfl
          · rfl
  | succ value inductionHypothesis =>
      cases square with
      | zero => omega
      | succ square =>
          have hsquarePredBits :
              natBitLength square ≤ maximumBits :=
            (decrement_bits_le (square + 1)).trans hsquareBits
          have hvaluePredBits :
              natBitLength value ≤ maximumBits :=
            (decrement_bits_le (value + 1)).trans hvalueBits
          rw [show
            binaryNatCeilSqrtCompareFuel (value + 1) + extraFuel =
              (3 +
                (binaryNatCeilSqrtCompareFuel value + extraFuel)) + 1 by
                simp [binaryNatCeilSqrtCompareFuel]
                omega]
          rw [run_branchZero_instruction
            (fuel := 3 +
              (binaryNatCeilSqrtCompareFuel value + extraFuel))
            (by rfl) hpc]
          rw [hsquare, if_neg (Nat.succ_ne_zero square)]
          rw [show
            3 + (binaryNatCeilSqrtCompareFuel value + extraFuel) =
              (2 +
                (binaryNatCeilSqrtCompareFuel value + extraFuel)) + 1 by
                omega]
          rw [run_branchZero_instruction
            (fuel := 2 +
              (binaryNatCeilSqrtCompareFuel value + extraFuel))
            (by rfl) rfl]
          rw [show (state.jump 7).registers 5 = value + 1 by
            exact hvalue]
          rw [if_neg (Nat.succ_ne_zero value)]
          rw [show
            2 + (binaryNatCeilSqrtCompareFuel value + extraFuel) =
              (1 +
                (binaryNatCeilSqrtCompareFuel value + extraFuel)) + 1 by
                omega]
          rw [run_decrement_instruction
            (fuel := 1 +
              (binaryNatCeilSqrtCompareFuel value + extraFuel))
            (value := square) (by rfl) rfl
            (by simp [NPOracleState.jump, hsquare]) hsquarePredBits]
          rw [show
            1 + (binaryNatCeilSqrtCompareFuel value + extraFuel) =
              (binaryNatCeilSqrtCompareFuel value + extraFuel) + 1 by
                omega]
          rw [run_decrement_instruction
            (fuel := binaryNatCeilSqrtCompareFuel value + extraFuel)
            (value := value) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hvalue])
            hvaluePredBits]
          apply inductionHypothesis square _
          · rfl
          · simp
          · simp
          · omega
          · exact hsquarePredBits
          · exact hvaluePredBits
          · intro finalState hpreserved hfinalPc
            apply hcontinue finalState
              (preservesOutside45_trans (by
                intro register hfour hfive
                simp [NPOracleState.write, NPOracleState.jump,
                  hfour, hfive]) hpreserved)
              hfinalPc

private def PreservesOutside26
    (before after : NPOracleState) : Prop :=
  ∀ register, register ≠ 2 → register ≠ 6 →
    after.registers register = before.registers register

private theorem preservesOutside26_trans
    {first middle last : NPOracleState}
    (hfirst : PreservesOutside26 first middle)
    (hlast : PreservesOutside26 middle last) :
    PreservesOutside26 first last := by
  intro register htwo hsix
  exact (hlast register htwo hsix).trans
    (hfirst register htwo hsix)

private def binaryNatCeilSqrtAddFuel (counter : ℕ) : ℕ :=
  3 * counter + 1

private theorem run_binaryNatCeilSqrtAdd
    (accumulator counter maximumBits extraFuel output : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 12)
    (haccumulator : state.registers 2 = accumulator)
    (hcounter : state.registers 6 = counter)
    (hsumBits :
      natBitLength (accumulator + counter) ≤ maximumBits)
    (hcontinue : ∀ nextState,
      PreservesOutside26 state nextState →
      nextState.pc = 15 →
      nextState.registers 2 = accumulator + counter →
      runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        extraFuel nextState = some output) :
    runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        (binaryNatCeilSqrtAddFuel counter + extraFuel) state =
      some output := by
  induction counter generalizing accumulator state with
  | zero =>
      rw [show binaryNatCeilSqrtAddFuel 0 + extraFuel =
        extraFuel + 1 by
          unfold binaryNatCeilSqrtAddFuel
          omega]
      rw [run_branchZero_instruction
        (fuel := extraFuel) (by rfl) hpc]
      rw [hcounter, if_pos rfl]
      apply hcontinue
      · intro register htwo hsix
        rfl
      · rfl
      · simpa using haccumulator
  | succ counter inductionHypothesis =>
      have hincLe :
          accumulator + 1 ≤ accumulator + (counter + 1) := by
        omega
      have hincBits :
          natBitLength (accumulator + 1) ≤ maximumBits :=
        (natBitLength_mono hincLe).trans hsumBits
      have hnextSum :
          (accumulator + 1) + counter =
            accumulator + (counter + 1) := by
        omega
      have hnextSumBits :
          natBitLength ((accumulator + 1) + counter) ≤ maximumBits := by
        rw [hnextSum]
        exact hsumBits
      rw [show
        binaryNatCeilSqrtAddFuel (counter + 1) + extraFuel =
          (2 + (binaryNatCeilSqrtAddFuel counter + extraFuel)) + 1 by
            unfold binaryNatCeilSqrtAddFuel
            omega]
      rw [run_branchZero_instruction
        (fuel := 2 +
          (binaryNatCeilSqrtAddFuel counter + extraFuel))
        (by rfl) hpc]
      rw [hcounter, if_neg (Nat.succ_ne_zero counter)]
      rw [show
        2 + (binaryNatCeilSqrtAddFuel counter + extraFuel) =
          (1 + (binaryNatCeilSqrtAddFuel counter + extraFuel)) + 1 by
            omega]
      rw [run_increment_instruction
        (fuel := 1 +
          (binaryNatCeilSqrtAddFuel counter + extraFuel))
        (value := accumulator + 1) (by rfl) rfl
        (by exact congrArg (fun value => value + 1) haccumulator)
        hincBits]
      rw [show
        1 + (binaryNatCeilSqrtAddFuel counter + extraFuel) =
          (binaryNatCeilSqrtAddFuel counter + extraFuel) + 1 by
            omega]
      rw [run_decrement_instruction
        (fuel := binaryNatCeilSqrtAddFuel counter + extraFuel)
        (value := counter) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcounter])
        ((decrement_bits_le (counter + 1)).trans <|
          (natBitLength_mono (by omega)).trans hsumBits)]
      apply inductionHypothesis (accumulator := accumulator + 1) _
      · rfl
      · simp
      · simp
      · exact hnextSumBits
      · intro finalState hpreserved hfinalPc hfinalAccumulator
        apply hcontinue finalState
          (preservesOutside26_trans (by
            intro register htwo hsix
            simp [NPOracleState.write, NPOracleState.jump, htwo, hsix])
            hpreserved)
          hfinalPc
          (by rwa [hnextSum] at hfinalAccumulator)

private def binaryNatCeilSqrtRegisterBound (value : ℕ) : ℕ :=
  max 1 <|
    max value <|
      max (natCeilSqrt value) <|
        max (natCeilSqrt value * natCeilSqrt value)
          (2 * natCeilSqrt value + 1)

def binaryNatCeilSqrtBits (value : ℕ) : ℕ :=
  natBitLength (binaryNatCeilSqrtRegisterBound value)

private theorem one_le_binaryNatCeilSqrtRegisterBound (value : ℕ) :
    1 ≤ binaryNatCeilSqrtRegisterBound value :=
  le_max_left _ _

private theorem value_le_binaryNatCeilSqrtRegisterBound (value : ℕ) :
    value ≤ binaryNatCeilSqrtRegisterBound value :=
  (le_max_left _ _).trans (le_max_right _ _)

private theorem root_le_binaryNatCeilSqrtRegisterBound (value : ℕ) :
    natCeilSqrt value ≤ binaryNatCeilSqrtRegisterBound value :=
  (le_max_left _ _).trans <|
    (le_max_right _ _).trans <|
      le_max_right _ _

private theorem rootSquare_le_binaryNatCeilSqrtRegisterBound (value : ℕ) :
    natCeilSqrt value * natCeilSqrt value ≤
      binaryNatCeilSqrtRegisterBound value :=
  (le_max_left _ _).trans <|
    (le_max_right _ _).trans <|
      (le_max_right _ _).trans <|
        le_max_right _ _

private theorem rootOdd_le_binaryNatCeilSqrtRegisterBound (value : ℕ) :
    2 * natCeilSqrt value + 1 ≤
      binaryNatCeilSqrtRegisterBound value :=
  (le_max_right _ _).trans <|
    (le_max_right _ _).trans <|
      (le_max_right _ _).trans <|
        le_max_right _ _

private def binaryNatCeilSqrtMainFuel
    (value candidate : ℕ) : ℕ → ℕ
  | 0 => binaryNatCeilSqrtCompareFuel value + 4
  | remaining + 1 =>
      binaryNatCeilSqrtCompareFuel (candidate * candidate) +
        binaryNatCeilSqrtAddFuel (2 * candidate + 1) + 7 +
          binaryNatCeilSqrtMainFuel value (candidate + 1) remaining

private theorem run_binaryNatCeilSqrtMain
    (value candidate remaining maximumBits : ℕ)
    (state : NPOracleState)
    (hremaining :
      candidate + remaining = natCeilSqrt value)
    (hpc : state.pc = 4)
    (hvalue : state.registers 0 = value)
    (hcandidate : state.registers 1 = candidate)
    (hsquare : state.registers 2 = candidate * candidate)
    (hodd : state.registers 3 = 2 * candidate + 1)
    (hzero : state.registers 7 = 0)
    (hbits : binaryNatCeilSqrtBits value ≤ maximumBits) :
    runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        (binaryNatCeilSqrtMainFuel value candidate remaining) state =
      some (natCeilSqrt value) := by
  induction remaining generalizing candidate state with
  | zero =>
      have hcandidateEq : candidate = natCeilSqrt value := by
        simpa using hremaining
      have hvalueBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono
          (value_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hcandidateBits :
          natBitLength candidate ≤ maximumBits := by
        rw [hcandidateEq]
        exact (natBitLength_mono
          (root_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hrootBits :
          natBitLength (natCeilSqrt value) ≤ maximumBits :=
        (natBitLength_mono
          (root_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hsquareBits :
          natBitLength (candidate * candidate) ≤ maximumBits := by
        rw [hcandidateEq]
        exact (natBitLength_mono
          (rootSquare_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hnotLt : ¬ candidate * candidate < value := by
        rw [hcandidateEq]
        exact not_lt_of_ge (le_natCeilSqrt_sq value)
      rw [show
        binaryNatCeilSqrtMainFuel value candidate 0 =
          (binaryNatCeilSqrtCompareFuel value + 3) + 1 by
            unfold binaryNatCeilSqrtMainFuel
            omega]
      rw [run_copy_instruction
        (fuel := binaryNatCeilSqrtCompareFuel value + 3)
        (value := candidate * candidate) (by rfl) hpc hsquare hsquareBits]
      rw [show
        binaryNatCeilSqrtCompareFuel value + 3 =
          (binaryNatCeilSqrtCompareFuel value + 2) + 1 by omega]
      rw [run_copy_instruction
        (fuel := binaryNatCeilSqrtCompareFuel value + 2)
        (value := value) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hvalue])
        hvalueBits]
      apply run_binaryNatCeilSqrtCompare_not_lt
        (candidate * candidate) value maximumBits 2
        (natCeilSqrt value) _
      · rfl
      · simp
      · simp
      · exact hnotLt
      · exact hsquareBits
      · exact hvalueBits
      · intro haltState hpreserved hhaltPc
        have hhaltCandidate :
            haltState.registers 1 = natCeilSqrt value := by
          rw [hpreserved 1 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump,
            hcandidateEq] using hcandidate
        rw [show 2 = 1 + 1 by omega]
        rw [run_copy_instruction (fuel := 1)
          (value := natCeilSqrt value) (by rfl) hhaltPc
          hhaltCandidate hrootBits]
        rw [show 1 = 0 + 1 by rfl]
        rw [run_halt_instruction (fuel := 0)
          (value := natCeilSqrt value) (by rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          hrootBits]
  | succ remaining inductionHypothesis =>
      have hcandidateLt :
          candidate < natCeilSqrt value := by
        omega
      have hnextRemaining :
          candidate + 1 + remaining = natCeilSqrt value := by
        omega
      have hnextCandidateLe :
          candidate + 1 ≤ natCeilSqrt value := by
        omega
      have hvalueBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono
          (value_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hsquareLe :
          candidate * candidate ≤
            natCeilSqrt value * natCeilSqrt value :=
        Nat.mul_self_le_mul_self hcandidateLt.le
      have hsquareBits :
          natBitLength (candidate * candidate) ≤ maximumBits :=
        (natBitLength_mono hsquareLe).trans <|
          (natBitLength_mono
            (rootSquare_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hoddLe :
          2 * candidate + 1 ≤ 2 * natCeilSqrt value + 1 := by
        omega
      have hoddBits :
          natBitLength (2 * candidate + 1) ≤ maximumBits :=
        (natBitLength_mono hoddLe).trans <|
          (natBitLength_mono
            (rootOdd_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hnextSquare :
          candidate * candidate + (2 * candidate + 1) =
            (candidate + 1) * (candidate + 1) := by
        ring
      have hnextSquareLe :
          (candidate + 1) * (candidate + 1) ≤
            natCeilSqrt value * natCeilSqrt value :=
        Nat.mul_self_le_mul_self hnextCandidateLe
      have hnextSquareBits :
          natBitLength
              (candidate * candidate + (2 * candidate + 1)) ≤
            maximumBits := by
        rw [hnextSquare]
        exact (natBitLength_mono hnextSquareLe).trans <|
          (natBitLength_mono
            (rootSquare_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hnextCandidateBits :
          natBitLength (candidate + 1) ≤ maximumBits :=
        (natBitLength_mono
          (hnextCandidateLe.trans
            (root_le_binaryNatCeilSqrtRegisterBound value))).trans hbits
      have hoddOneBits :
          natBitLength (2 * candidate + 1 + 1) ≤ maximumBits :=
        (natBitLength_mono (by
          calc
            2 * candidate + 1 + 1 ≤ 2 * (candidate + 1) + 1 := by omega
            _ ≤ 2 * natCeilSqrt value + 1 := by omega
            _ ≤ binaryNatCeilSqrtRegisterBound value :=
              rootOdd_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hnextOddBits :
          natBitLength (2 * (candidate + 1) + 1) ≤ maximumBits :=
        (natBitLength_mono (by
          calc
            2 * (candidate + 1) + 1 ≤
                2 * natCeilSqrt value + 1 := by omega
            _ ≤ binaryNatCeilSqrtRegisterBound value :=
              rootOdd_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
      have hsquareLt : candidate * candidate < value :=
        sq_lt_of_lt_natCeilSqrt hcandidateLt
      let recursiveFuel :=
        binaryNatCeilSqrtMainFuel value (candidate + 1) remaining
      let additionTail :=
        binaryNatCeilSqrtAddFuel (2 * candidate + 1) +
          4 + recursiveFuel
      rw [show
        binaryNatCeilSqrtMainFuel value candidate (remaining + 1) =
          (binaryNatCeilSqrtCompareFuel (candidate * candidate) +
            (additionTail + 2)) + 1 by
              dsimp [binaryNatCeilSqrtMainFuel, additionTail, recursiveFuel]
              omega]
      rw [run_copy_instruction
        (fuel := binaryNatCeilSqrtCompareFuel (candidate * candidate) +
          (additionTail + 2))
        (value := candidate * candidate) (by rfl) hpc hsquare hsquareBits]
      rw [show
        binaryNatCeilSqrtCompareFuel (candidate * candidate) +
            (additionTail + 2) =
          (binaryNatCeilSqrtCompareFuel (candidate * candidate) +
            (additionTail + 1)) + 1 by omega]
      rw [run_copy_instruction
        (fuel := binaryNatCeilSqrtCompareFuel (candidate * candidate) +
          (additionTail + 1))
        (value := value) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hvalue])
        hvalueBits]
      apply run_binaryNatCeilSqrtCompare_lt
        (candidate * candidate) value maximumBits (additionTail + 1)
        (natCeilSqrt value) _
      · rfl
      · simp
      · simp
      · exact hsquareLt
      · exact hsquareBits
      · exact hvalueBits
      · intro addEntry hcomparePreserved haddPc
        have haddValue : addEntry.registers 0 = value := by
          rw [hcomparePreserved 0 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hvalue
        have haddCandidate :
            addEntry.registers 1 = candidate := by
          rw [hcomparePreserved 1 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hcandidate
        have haddSquare :
            addEntry.registers 2 = candidate * candidate := by
          rw [hcomparePreserved 2 (by omega) (by omega)]
          simp [NPOracleState.write, NPOracleState.jump, hsquare]
        have haddOdd :
            addEntry.registers 3 = 2 * candidate + 1 := by
          rw [hcomparePreserved 3 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hodd
        have haddZero : addEntry.registers 7 = 0 := by
          rw [hcomparePreserved 7 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hzero
        rw [run_copy_instruction
          (fuel := additionTail)
          (value := 2 * candidate + 1) (by rfl) haddPc haddOdd hoddBits]
        rw [show additionTail =
          binaryNatCeilSqrtAddFuel (2 * candidate + 1) +
            (4 + recursiveFuel) by
              dsimp [additionTail]
              omega]
        apply run_binaryNatCeilSqrtAdd
          (candidate * candidate) (2 * candidate + 1) maximumBits
          (4 + recursiveFuel) (natCeilSqrt value) _
        · rfl
        · simpa [NPOracleState.write, NPOracleState.jump] using haddSquare
        · simp [NPOracleState.write, NPOracleState.jump]
        · exact hnextSquareBits
        · intro advanceEntry haddPreserved hadvancePc hadvanceSquare
          have hadvanceValue :
              advanceEntry.registers 0 = value := by
            rw [haddPreserved 0 (by omega) (by omega)]
            simpa [NPOracleState.write, NPOracleState.jump] using haddValue
          have hadvanceCandidate :
              advanceEntry.registers 1 = candidate := by
            rw [haddPreserved 1 (by omega) (by omega)]
            simpa [NPOracleState.write, NPOracleState.jump] using haddCandidate
          have hadvanceOdd :
              advanceEntry.registers 3 = 2 * candidate + 1 := by
            rw [haddPreserved 3 (by omega) (by omega)]
            simpa [NPOracleState.write, NPOracleState.jump] using haddOdd
          have hadvanceZero : advanceEntry.registers 7 = 0 := by
            rw [haddPreserved 7 (by omega) (by omega)]
            simpa [NPOracleState.write, NPOracleState.jump] using haddZero
          rw [show 4 + recursiveFuel =
            (3 + recursiveFuel) + 1 by omega]
          rw [run_increment_instruction
            (fuel := 3 + recursiveFuel)
            (value := candidate + 1) (by rfl) hadvancePc
            (by exact congrArg (fun value => value + 1) hadvanceCandidate)
            hnextCandidateBits]
          rw [show 3 + recursiveFuel =
            (2 + recursiveFuel) + 1 by omega]
          rw [run_increment_instruction
            (fuel := 2 + recursiveFuel)
            (value := 2 * candidate + 1 + 1) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump,
              hadvanceOdd])
            hoddOneBits]
          rw [show 2 + recursiveFuel =
            (1 + recursiveFuel) + 1 by omega]
          rw [run_increment_instruction
            (fuel := 1 + recursiveFuel)
            (value := 2 * (candidate + 1) + 1) (by rfl) rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump]
              omega)
            hnextOddBits]
          rw [show 1 + recursiveFuel = recursiveFuel + 1 by omega]
          rw [run_branchZero_instruction
            (fuel := recursiveFuel) (by rfl) rfl]
          simp only [NPOracleState.write, NPOracleState.jump,
            hadvanceZero]
          dsimp [recursiveFuel]
          apply inductionHypothesis (candidate := candidate + 1) _
          · exact hnextRemaining
          · rfl
          · simp [hadvanceValue]
          · simp
          · simp [hadvanceSquare, hnextSquare]
          · simp
          · simp [hadvanceZero]

def binaryNatCeilSqrtFuel (value : ℕ) : ℕ :=
  4 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value)

theorem run_binaryNatCeilSqrtProgram
    (value maximumBits : ℕ)
    (hbits : binaryNatCeilSqrtBits value ≤ maximumBits) :
    runNPOracleProgram binaryNatCeilSqrtProgram maximumBits
        (binaryNatCeilSqrtFuel value)
        (initialNPOracleState 0 value) =
      some (natCeilSqrt value) := by
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono
      (one_le_binaryNatCeilSqrtRegisterBound value)).trans hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le 1)).trans honeBits
  rw [show binaryNatCeilSqrtFuel value =
    (3 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value)) + 1 by
      unfold binaryNatCeilSqrtFuel
      omega]
  rw [run_set_instruction
    (fuel := 3 +
      binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value))
    (value := 0) (by rfl) rfl hzeroBits]
  rw [show
    3 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value) =
      (2 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value)) + 1 by
        omega]
  rw [run_set_instruction
    (fuel := 2 +
      binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value))
    (value := 0) (by rfl) rfl hzeroBits]
  rw [show
    2 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value) =
      (1 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value)) + 1 by
        omega]
  rw [run_set_instruction
    (fuel := 1 +
      binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value))
    (value := 1) (by rfl) rfl honeBits]
  rw [show
    1 + binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value) =
      binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value) + 1 by
        omega]
  rw [run_set_instruction
    (fuel := binaryNatCeilSqrtMainFuel value 0 (natCeilSqrt value))
    (value := 0) (by rfl) rfl hzeroBits]
  apply run_binaryNatCeilSqrtMain value 0 (natCeilSqrt value)
    maximumBits _
  · simp
  · rfl
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · exact hbits

/-- Positive-denominator ceiling division by chunked subtraction.  The
denominator remains in `r1`; `r0` is the residual numerator, `r2` the
quotient, and `r3` the current chunk cursor. -/
def binaryNatCeilDivProgram : NPOracleProgram :=
  [ .set 2 0 1
  , .set 4 0 2
  , .branchZero 0 10 3
  , .increment 2 4
  , .copy 1 3 5
  , .branchZero 3 2 6
  , .branchZero 0 10 7
  , .decrement 0 8
  , .decrement 3 9
  , .branchZero 4 5 5
  , .copy 2 0 11
  , .halt 0
  ]

@[simp] theorem binaryNatCeilDivProgram_oracleFree :
    OracleFree binaryNatCeilDivProgram := by
  rfl

private def PreservesOutside03
    (before after : NPOracleState) : Prop :=
  ∀ register, register ≠ 0 → register ≠ 3 →
    after.registers register = before.registers register

private theorem preservesOutside03_trans
    {first middle last : NPOracleState}
    (hfirst : PreservesOutside03 first middle)
    (hlast : PreservesOutside03 middle last) :
    PreservesOutside03 first last := by
  intro register hzero hthree
  exact (hlast register hzero hthree).trans
    (hfirst register hzero hthree)

private def binaryNatCeilDivFullChunkFuel (denominator : ℕ) : ℕ :=
  5 * denominator + 1

private theorem run_binaryNatCeilDivFullChunk
    (denominator remaining maximumBits extraFuel output : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hnumerator :
      state.registers 0 = denominator + remaining)
    (hcursor : state.registers 3 = denominator)
    (hzero : state.registers 4 = 0)
    (hnumeratorBits :
      natBitLength (denominator + remaining) ≤ maximumBits)
    (hcursorBits : natBitLength denominator ≤ maximumBits)
    (hcontinue : ∀ nextState,
      PreservesOutside03 state nextState →
      nextState.pc = 2 →
      nextState.registers 0 = remaining →
      runNPOracleProgram binaryNatCeilDivProgram maximumBits
        extraFuel nextState = some output) :
    runNPOracleProgram binaryNatCeilDivProgram maximumBits
        (binaryNatCeilDivFullChunkFuel denominator + extraFuel) state =
      some output := by
  induction denominator generalizing remaining state with
  | zero =>
      rw [show binaryNatCeilDivFullChunkFuel 0 + extraFuel =
        extraFuel + 1 by
          unfold binaryNatCeilDivFullChunkFuel
          omega]
      rw [run_branchZero_instruction
        (fuel := extraFuel) (by rfl) hpc]
      rw [hcursor, if_pos rfl]
      apply hcontinue
      · intro register hzeroReg hthree
        rfl
      · rfl
      · simpa using hnumerator
  | succ denominator inductionHypothesis =>
      have hnumeratorPredBits :
          natBitLength (denominator + remaining) ≤ maximumBits := by
        have hle :
            denominator + remaining ≤
              (denominator + 1) + remaining := by
          omega
        exact (natBitLength_mono hle).trans hnumeratorBits
      have hcursorPredBits :
          natBitLength denominator ≤ maximumBits :=
        (decrement_bits_le (denominator + 1)).trans hcursorBits
      rw [show
        binaryNatCeilDivFullChunkFuel (denominator + 1) + extraFuel =
          (4 +
            (binaryNatCeilDivFullChunkFuel denominator + extraFuel)) + 1 by
              unfold binaryNatCeilDivFullChunkFuel
              omega]
      rw [run_branchZero_instruction
        (fuel := 4 +
          (binaryNatCeilDivFullChunkFuel denominator + extraFuel))
        (by rfl) hpc]
      rw [hcursor, if_neg (Nat.succ_ne_zero denominator)]
      rw [show
        4 + (binaryNatCeilDivFullChunkFuel denominator + extraFuel) =
          (3 +
            (binaryNatCeilDivFullChunkFuel denominator + extraFuel)) + 1 by
              omega]
      rw [run_branchZero_instruction
        (fuel := 3 +
          (binaryNatCeilDivFullChunkFuel denominator + extraFuel))
        (by rfl) rfl]
      rw [show (state.jump 6).registers 0 =
          (denominator + 1) + remaining by exact hnumerator]
      rw [if_neg (by omega)]
      rw [show
        3 + (binaryNatCeilDivFullChunkFuel denominator + extraFuel) =
          (2 +
            (binaryNatCeilDivFullChunkFuel denominator + extraFuel)) + 1 by
              omega]
      rw [run_decrement_instruction
        (fuel := 2 +
          (binaryNatCeilDivFullChunkFuel denominator + extraFuel))
        (value := denominator + remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hnumerator])
        hnumeratorPredBits]
      rw [show
        2 + (binaryNatCeilDivFullChunkFuel denominator + extraFuel) =
          (1 +
            (binaryNatCeilDivFullChunkFuel denominator + extraFuel)) + 1 by
              omega]
      rw [run_decrement_instruction
        (fuel := 1 +
          (binaryNatCeilDivFullChunkFuel denominator + extraFuel))
        (value := denominator) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcursor])
        hcursorPredBits]
      rw [show
        1 + (binaryNatCeilDivFullChunkFuel denominator + extraFuel) =
          (binaryNatCeilDivFullChunkFuel denominator + extraFuel) + 1 by
            omega]
      rw [run_branchZero_instruction
        (fuel := binaryNatCeilDivFullChunkFuel denominator + extraFuel)
        (by rfl) rfl]
      simp only [NPOracleState.write, NPOracleState.jump, hzero]
      apply inductionHypothesis remaining _
      · rfl
      · simp
      · simp
      · simp [hzero]
      · exact hnumeratorPredBits
      · exact hcursorPredBits
      · intro finalState hpreserved hfinalPc hfinalNumerator
        apply hcontinue finalState
          (preservesOutside03_trans (by
            intro register hzeroReg hthree
            simp [hzeroReg, hthree]) hpreserved)
          hfinalPc hfinalNumerator

private def binaryNatCeilDivPartialChunkFuel (numerator : ℕ) : ℕ :=
  5 * numerator + 2

private theorem run_binaryNatCeilDivPartialChunk
    (numerator slack maximumBits extraFuel output : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 5)
    (hnumerator : state.registers 0 = numerator)
    (hcursor : state.registers 3 = numerator + (slack + 1))
    (hzero : state.registers 4 = 0)
    (hnumeratorBits : natBitLength numerator ≤ maximumBits)
    (hcursorBits :
      natBitLength (numerator + (slack + 1)) ≤ maximumBits)
    (hcontinue : ∀ nextState,
      PreservesOutside03 state nextState →
      nextState.pc = 10 →
      nextState.registers 0 = 0 →
      runNPOracleProgram binaryNatCeilDivProgram maximumBits
        extraFuel nextState = some output) :
    runNPOracleProgram binaryNatCeilDivProgram maximumBits
        (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) state =
      some output := by
  induction numerator generalizing state with
  | zero =>
      rw [show binaryNatCeilDivPartialChunkFuel 0 + extraFuel =
        (1 + extraFuel) + 1 by
          unfold binaryNatCeilDivPartialChunkFuel
          omega]
      rw [run_branchZero_instruction
        (fuel := 1 + extraFuel) (by rfl) hpc]
      rw [hcursor, if_neg (by omega)]
      rw [show 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (fuel := extraFuel) (by rfl) rfl]
      rw [show (state.jump 6).registers 0 = 0 by exact hnumerator]
      rw [if_pos rfl]
      apply hcontinue
      · intro register hzeroReg hthree
        rfl
      · rfl
      · exact hnumerator
  | succ numerator inductionHypothesis =>
      have hnumeratorPredBits :
          natBitLength numerator ≤ maximumBits :=
        (decrement_bits_le (numerator + 1)).trans hnumeratorBits
      have hcursorPredBits :
          natBitLength (numerator + (slack + 1)) ≤ maximumBits := by
        have hle :
            numerator + (slack + 1) ≤
              (numerator + 1) + (slack + 1) := by
          omega
        exact (natBitLength_mono hle).trans hcursorBits
      rw [show
        binaryNatCeilDivPartialChunkFuel (numerator + 1) + extraFuel =
          (4 +
            (binaryNatCeilDivPartialChunkFuel numerator + extraFuel)) + 1 by
              unfold binaryNatCeilDivPartialChunkFuel
              omega]
      rw [run_branchZero_instruction
        (fuel := 4 +
          (binaryNatCeilDivPartialChunkFuel numerator + extraFuel))
        (by rfl) hpc]
      rw [hcursor, if_neg (by omega)]
      rw [show
        4 + (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) =
          (3 +
            (binaryNatCeilDivPartialChunkFuel numerator + extraFuel)) + 1 by
              omega]
      rw [run_branchZero_instruction
        (fuel := 3 +
          (binaryNatCeilDivPartialChunkFuel numerator + extraFuel))
        (by rfl) rfl]
      rw [show (state.jump 6).registers 0 = numerator + 1 by
        exact hnumerator]
      rw [if_neg (Nat.succ_ne_zero numerator)]
      rw [show
        3 + (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) =
          (2 +
            (binaryNatCeilDivPartialChunkFuel numerator + extraFuel)) + 1 by
              omega]
      rw [run_decrement_instruction
        (fuel := 2 +
          (binaryNatCeilDivPartialChunkFuel numerator + extraFuel))
        (value := numerator) (by rfl) rfl
        (by simp [NPOracleState.jump, hnumerator])
        hnumeratorPredBits]
      rw [show
        2 + (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) =
          (1 +
            (binaryNatCeilDivPartialChunkFuel numerator + extraFuel)) + 1 by
              omega]
      rw [run_decrement_instruction
        (fuel := 1 +
          (binaryNatCeilDivPartialChunkFuel numerator + extraFuel))
        (value := numerator + (slack + 1)) (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, hcursor]
          omega)
        hcursorPredBits]
      rw [show
        1 + (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) =
          (binaryNatCeilDivPartialChunkFuel numerator + extraFuel) + 1 by
            omega]
      rw [run_branchZero_instruction
        (fuel := binaryNatCeilDivPartialChunkFuel numerator + extraFuel)
        (by rfl) rfl]
      simp only [NPOracleState.write, NPOracleState.jump, hzero]
      apply inductionHypothesis _
      · rfl
      · simp
      · simp
      · simp [hzero]
      · exact hnumeratorPredBits
      · exact hcursorPredBits
      · intro finalState hpreserved hfinalPc hfinalNumerator
        apply hcontinue finalState
          (preservesOutside03_trans (by
            intro register hzeroReg hthree
            simp [hzeroReg, hthree]) hpreserved)
          hfinalPc hfinalNumerator

private def binaryNatCeilDivResult
    (accumulator quotient remainder : ℕ) : ℕ :=
  accumulator + quotient + if remainder = 0 then 0 else 1

private def binaryNatCeilDivMainFuel
    (denominator remainder : ℕ) : ℕ → ℕ
  | 0 =>
      if remainder = 0 then 3
      else binaryNatCeilDivPartialChunkFuel remainder + 5
  | quotient + 1 =>
      binaryNatCeilDivFullChunkFuel denominator + 3 +
        binaryNatCeilDivMainFuel denominator remainder quotient

private theorem run_binaryNatCeilDivMain
    (denominator remainder quotient accumulator maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 2)
    (hnumerator :
      state.registers 0 = denominator * quotient + remainder)
    (hdenominator : state.registers 1 = denominator)
    (haccumulator : state.registers 2 = accumulator)
    (hzero : state.registers 4 = 0)
    (hdenominatorPos : 0 < denominator)
    (hremainderLt : remainder < denominator)
    (hnumeratorBits :
      natBitLength (denominator * quotient + remainder) ≤ maximumBits)
    (hdenominatorBits :
      natBitLength denominator ≤ maximumBits)
    (hresultBits :
      natBitLength
          (binaryNatCeilDivResult accumulator quotient remainder) ≤
        maximumBits) :
    runNPOracleProgram binaryNatCeilDivProgram maximumBits
        (binaryNatCeilDivMainFuel denominator remainder quotient) state =
      some (binaryNatCeilDivResult accumulator quotient remainder) := by
  induction quotient generalizing accumulator state with
  | zero =>
      cases remainder with
      | zero =>
          have haccumulatorBits :
              natBitLength accumulator ≤ maximumBits := by
            simpa [binaryNatCeilDivResult] using hresultBits
          rw [show binaryNatCeilDivMainFuel denominator 0 0 =
            2 + 1 by
              simp [binaryNatCeilDivMainFuel]]
          rw [run_branchZero_instruction (fuel := 2) (by rfl) hpc]
          rw [hnumerator, if_pos (by simp)]
          rw [show 2 = 1 + 1 by omega]
          rw [run_copy_instruction
            (fuel := 1) (value := accumulator) (by rfl) rfl
            (by exact haccumulator) haccumulatorBits]
          rw [show 1 = 0 + 1 by rfl]
          rw [run_halt_instruction
            (fuel := 0) (value := accumulator) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump])
            haccumulatorBits]
          simp [binaryNatCeilDivResult]
      | succ remainder =>
          obtain ⟨slack, hdenominatorRaw⟩ :=
            Nat.exists_eq_add_of_lt hremainderLt
          have hdenominatorEq :
              denominator = (remainder + 1) + (slack + 1) := by
            omega
          have hresultEq :
              binaryNatCeilDivResult accumulator 0 (remainder + 1) =
                accumulator + 1 := by
            simp [binaryNatCeilDivResult]
          have haccumulatorIncBits :
              natBitLength (accumulator + 1) ≤ maximumBits := by
            rw [← hresultEq]
            exact hresultBits
          rw [show
            binaryNatCeilDivMainFuel denominator (remainder + 1) 0 =
              (binaryNatCeilDivPartialChunkFuel (remainder + 1) + 4) + 1 by
                simp [binaryNatCeilDivMainFuel]]
          rw [run_branchZero_instruction
            (fuel :=
              binaryNatCeilDivPartialChunkFuel (remainder + 1) + 4)
            (by rfl) hpc]
          rw [hnumerator, if_neg (by omega)]
          rw [show
            binaryNatCeilDivPartialChunkFuel (remainder + 1) + 4 =
              (binaryNatCeilDivPartialChunkFuel (remainder + 1) + 3) + 1 by
                omega]
          rw [run_increment_instruction
            (fuel :=
              binaryNatCeilDivPartialChunkFuel (remainder + 1) + 3)
            (value := accumulator + 1) (by rfl) rfl
            (by exact congrArg (fun value => value + 1) haccumulator)
            haccumulatorIncBits]
          rw [show
            binaryNatCeilDivPartialChunkFuel (remainder + 1) + 3 =
              (binaryNatCeilDivPartialChunkFuel (remainder + 1) + 2) + 1 by
                omega]
          rw [run_copy_instruction
            (fuel :=
              binaryNatCeilDivPartialChunkFuel (remainder + 1) + 2)
            (value := denominator) (by rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump,
              hdenominator])
            hdenominatorBits]
          apply run_binaryNatCeilDivPartialChunk
            (remainder + 1) slack maximumBits 2 (accumulator + 1) _
          · rfl
          · simpa using hnumerator
          · simp [hdenominatorEq]
          · simp [hzero]
          · simpa using hnumeratorBits
          · rw [← hdenominatorEq]
            exact hdenominatorBits
          · intro haltState hpreserved hhaltPc hhaltNumerator
            have hhaltAccumulator :
                haltState.registers 2 = accumulator + 1 := by
              rw [hpreserved 2 (by omega) (by omega)]
              simp [NPOracleState.write, NPOracleState.jump]
            rw [show 2 = 1 + 1 by omega]
            rw [run_copy_instruction
              (fuel := 1) (value := accumulator + 1)
              (by rfl) hhaltPc hhaltAccumulator haccumulatorIncBits]
            rw [show 1 = 0 + 1 by rfl]
            rw [run_halt_instruction
              (fuel := 0) (value := accumulator + 1)
              (by rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump])
              haccumulatorIncBits]
  | succ quotient inductionHypothesis =>
      have hnumeratorPositive :
          denominator * (quotient + 1) + remainder ≠ 0 := by
        have : 0 < denominator * (quotient + 1) := by
          positivity
        omega
      have hremainingLe :
          denominator * quotient + remainder ≤
            denominator * (quotient + 1) + remainder := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left denominator (Nat.le_succ quotient)) remainder
      have hremainingBits :
          natBitLength (denominator * quotient + remainder) ≤
            maximumBits :=
        (natBitLength_mono hremainingLe).trans hnumeratorBits
      have hnextResult :
          binaryNatCeilDivResult (accumulator + 1) quotient remainder =
            binaryNatCeilDivResult accumulator (quotient + 1) remainder := by
        unfold binaryNatCeilDivResult
        omega
      have haccumulatorIncLe :
          accumulator + 1 ≤
            binaryNatCeilDivResult accumulator (quotient + 1) remainder := by
        unfold binaryNatCeilDivResult
        omega
      have haccumulatorIncBits :
          natBitLength (accumulator + 1) ≤ maximumBits :=
        (natBitLength_mono haccumulatorIncLe).trans hresultBits
      rw [show
        binaryNatCeilDivMainFuel denominator remainder (quotient + 1) =
          (binaryNatCeilDivFullChunkFuel denominator + 2 +
            binaryNatCeilDivMainFuel denominator remainder quotient) + 1 by
              simp only [binaryNatCeilDivMainFuel]
              omega]
      rw [run_branchZero_instruction
        (fuel := binaryNatCeilDivFullChunkFuel denominator + 2 +
          binaryNatCeilDivMainFuel denominator remainder quotient)
        (by rfl) hpc]
      rw [hnumerator, if_neg hnumeratorPositive]
      rw [show
        binaryNatCeilDivFullChunkFuel denominator + 2 +
            binaryNatCeilDivMainFuel denominator remainder quotient =
          (binaryNatCeilDivFullChunkFuel denominator + 1 +
            binaryNatCeilDivMainFuel denominator remainder quotient) + 1 by
              omega]
      rw [run_increment_instruction
        (fuel := binaryNatCeilDivFullChunkFuel denominator + 1 +
          binaryNatCeilDivMainFuel denominator remainder quotient)
        (value := accumulator + 1) (by rfl) rfl
        (by exact congrArg (fun value => value + 1) haccumulator)
        haccumulatorIncBits]
      rw [show
        binaryNatCeilDivFullChunkFuel denominator + 1 +
            binaryNatCeilDivMainFuel denominator remainder quotient =
          (binaryNatCeilDivFullChunkFuel denominator +
            binaryNatCeilDivMainFuel denominator remainder quotient) + 1 by
              omega]
      rw [run_copy_instruction
        (fuel := binaryNatCeilDivFullChunkFuel denominator +
          binaryNatCeilDivMainFuel denominator remainder quotient)
        (value := denominator) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hdenominator])
        hdenominatorBits]
      have hnumeratorSplit :
          denominator * (quotient + 1) + remainder =
            denominator + (denominator * quotient + remainder) := by
        ring
      apply run_binaryNatCeilDivFullChunk denominator
        (denominator * quotient + remainder) maximumBits
        (binaryNatCeilDivMainFuel denominator remainder quotient)
        (binaryNatCeilDivResult accumulator (quotient + 1) remainder) _
      · rfl
      · rw [← hnumeratorSplit]
        simpa [NPOracleState.write, NPOracleState.jump] using hnumerator
      · simp
      · simp [hzero]
      · rw [← hnumeratorSplit]
        exact hnumeratorBits
      · exact hdenominatorBits
      · intro nextMain hpreserved hnextPc hnextNumerator
        have hnextDenominator :
            nextMain.registers 1 = denominator := by
          rw [hpreserved 1 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hdenominator
        have hnextAccumulator :
            nextMain.registers 2 = accumulator + 1 := by
          rw [hpreserved 2 (by omega) (by omega)]
          simp [NPOracleState.write, NPOracleState.jump]
        have hnextZero : nextMain.registers 4 = 0 := by
          rw [hpreserved 4 (by omega) (by omega)]
          simpa [NPOracleState.write, NPOracleState.jump] using hzero
        rw [← hnextResult]
        apply inductionHypothesis (accumulator := accumulator + 1)
          nextMain hnextPc hnextNumerator hnextDenominator
          hnextAccumulator hnextZero hremainingBits
        rw [hnextResult]
        exact hresultBits

private theorem ceilDiv_eq_div_add_indicator
    (numerator denominator : ℕ) (hdenominator : 0 < denominator) :
    numerator ⌈/⌉ denominator =
      numerator / denominator +
        if numerator % denominator = 0 then 0 else 1 := by
  have hremainderLt :
      numerator % denominator < denominator :=
    Nat.mod_lt numerator hdenominator
  have hdecompose :
      numerator =
        denominator * (numerator / denominator) +
          numerator % denominator := by
    exact (Nat.div_add_mod numerator denominator).symm
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hdenominator).mpr
    split
    · rename_i hremainder
      simp only [Nat.add_zero]
      omega
    · rename_i hremainder
      have hproduct :
          denominator * (numerator / denominator + 1) =
            denominator * (numerator / denominator) + denominator := by
        ring
      rw [hproduct]
      omega
  · split
    · rename_i hremainder
      have hnumeratorLe :
          numerator ≤
            denominator * (numerator ⌈/⌉ denominator) :=
        (ceilDiv_le_iff_le_mul hdenominator).mp le_rfl
      apply Nat.div_le_of_le_mul
      simpa [mul_comm] using hnumeratorLe
    · rename_i hremainder
      by_contra hle
      have hceilLe :
          numerator ⌈/⌉ denominator ≤ numerator / denominator := by
        omega
      have hnumeratorLe :
          numerator ≤ denominator * (numerator / denominator) :=
        (ceilDiv_le_iff_le_mul hdenominator).mp hceilLe
      omega

def binaryNatCeilDivBits (numerator denominator : ℕ) : ℕ :=
  natBitLength <|
    max numerator <| max denominator (numerator ⌈/⌉ denominator)

def binaryNatCeilDivFuel (numerator denominator : ℕ) : ℕ :=
  2 + binaryNatCeilDivMainFuel denominator
    (numerator % denominator) (numerator / denominator)

theorem run_binaryNatCeilDivProgram
    (numerator denominator maximumBits : ℕ)
    (hdenominator : 0 < denominator)
    (hbits :
      binaryNatCeilDivBits numerator denominator ≤ maximumBits) :
    runNPOracleProgram binaryNatCeilDivProgram maximumBits
        (binaryNatCeilDivFuel numerator denominator)
        (initialNPOracleState denominator numerator) =
      some (numerator ⌈/⌉ denominator) := by
  have hnumeratorBits : natBitLength numerator ≤ maximumBits :=
    (natBitLength_mono
      (le_max_left numerator
        (max denominator (numerator ⌈/⌉ denominator)))).trans hbits
  have hdenominatorBits : natBitLength denominator ≤ maximumBits :=
    (natBitLength_mono
      ((le_max_left denominator (numerator ⌈/⌉ denominator)).trans
        (le_max_right numerator
          (max denominator (numerator ⌈/⌉ denominator))))).trans hbits
  have hresultBits :
      natBitLength (numerator ⌈/⌉ denominator) ≤ maximumBits :=
    (natBitLength_mono
      ((le_max_right denominator (numerator ⌈/⌉ denominator)).trans
        (le_max_right numerator
          (max denominator (numerator ⌈/⌉ denominator))))).trans hbits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le denominator)).trans hdenominatorBits
  have hremainderLt :
      numerator % denominator < denominator :=
    Nat.mod_lt numerator hdenominator
  have hdecompose :
      denominator * (numerator / denominator) +
          numerator % denominator =
        numerator := by
    exact Nat.div_add_mod numerator denominator
  have hresult :
      binaryNatCeilDivResult 0 (numerator / denominator)
          (numerator % denominator) =
        numerator ⌈/⌉ denominator := by
    rw [ceilDiv_eq_div_add_indicator numerator denominator hdenominator]
    simp [binaryNatCeilDivResult]
  rw [show binaryNatCeilDivFuel numerator denominator =
    (1 + binaryNatCeilDivMainFuel denominator
      (numerator % denominator) (numerator / denominator)) + 1 by
        unfold binaryNatCeilDivFuel
        omega]
  rw [run_set_instruction
    (fuel := 1 + binaryNatCeilDivMainFuel denominator
      (numerator % denominator) (numerator / denominator))
    (value := 0) (by rfl) rfl hzeroBits]
  rw [show
    1 + binaryNatCeilDivMainFuel denominator
        (numerator % denominator) (numerator / denominator) =
      binaryNatCeilDivMainFuel denominator
        (numerator % denominator) (numerator / denominator) + 1 by
          omega]
  rw [run_set_instruction
    (fuel := binaryNatCeilDivMainFuel denominator
      (numerator % denominator) (numerator / denominator))
    (value := 0) (by rfl) rfl hzeroBits]
  rw [← hresult]
  apply run_binaryNatCeilDivMain denominator
    (numerator % denominator) (numerator / denominator) 0 maximumBits _
  · rfl
  · simpa [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump] using hdecompose.symm
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]
  · exact hdenominator
  · exact hremainderLt
  · rw [hdecompose]
    exact hnumeratorBits
  · exact hdenominatorBits
  · rw [hresult]
    exact hresultBits

def symmetricFourfoldRowRequest
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    FourfoldRowRequest where
  mode := .symmetric
  q := request.q
  envelopeCode :=
    fourfoldRequestEnvelopeOutput symmetricCircuitFamilyTag
      CanonicalWitnessCodec.symmetricCircuitCodec.encode request
  rowIndex := rowIndex
  inputCode := encodeBitInput input

def thresholdFourfoldRowRequest
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    FourfoldRowRequest where
  mode := .threshold
  q := request.q
  envelopeCode :=
    fourfoldRequestEnvelopeOutput thresholdCircuitFamilyTag
      CanonicalWitnessCodec.thresholdCircuitCodec.encode request
  rowIndex := rowIndex
  inputCode := encodeBitInput input

/-! ## Total canonical finite-index decoders -/

/-- The small primitive shared by every row decoder.  Out-of-range naturals
are rejected rather than truncated or wrapped. -/
def decodeFinIndex (bound index : ℕ) : Option (Fin bound) :=
  if hindex : index < bound then some ⟨index, hindex⟩ else none

@[simp] theorem decodeFinIndex_of_lt
    {bound index : ℕ} (hindex : index < bound) :
    decodeFinIndex bound index = some ⟨index, hindex⟩ := by
  simp [decodeFinIndex, hindex]

theorem decodeFinIndex_eq_some_iff
    {bound index : ℕ} {decoded : Fin bound} :
    decodeFinIndex bound index = some decoded ↔ decoded.val = index := by
  constructor
  · intro hdecode
    unfold decodeFinIndex at hdecode
    split at hdecode
    · simpa using (congrArg (fun value => value.map Fin.val) hdecode).symm
    · simp at hdecode
  · intro hequal
    subst index
    simp [decodeFinIndex, decoded.isLt]

def encodeNormalizedOccurrenceListSeed
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (sample :
      NormalizedOccurrenceListSeed occurrences liveScale denominator) : ℕ :=
  (normalizedOccurrenceListSeedFinEquiv occurrences liveScale denominator
    sample).val

def decodeNormalizedOccurrenceListSeed
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator index : ℕ) :
    Option
      (NormalizedOccurrenceListSeed occurrences liveScale denominator) :=
  (decodeFinIndex
      (Fintype.card
        (NormalizedOccurrenceListSeed occurrences liveScale denominator))
      index).map
    (normalizedOccurrenceListSeedFinEquiv occurrences liveScale
      denominator).symm

@[simp] theorem decodeNormalizedOccurrenceListSeed_encode
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (sample :
      NormalizedOccurrenceListSeed occurrences liveScale denominator) :
    decodeNormalizedOccurrenceListSeed occurrences liveScale denominator
        (encodeNormalizedOccurrenceListSeed occurrences liveScale denominator
          sample) =
      some sample := by
  simp [decodeNormalizedOccurrenceListSeed,
    encodeNormalizedOccurrenceListSeed, decodeFinIndex]

theorem decodeNormalizedOccurrenceListSeed_eq_some_iff
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator index : ℕ)
    (sample :
      NormalizedOccurrenceListSeed occurrences liveScale denominator) :
    decodeNormalizedOccurrenceListSeed occurrences liveScale denominator
        index =
      some sample ↔
        encodeNormalizedOccurrenceListSeed occurrences liveScale denominator
          sample = index := by
  simp only [decodeNormalizedOccurrenceListSeed, Option.map_eq_some_iff]
  constructor
  · rintro ⟨finiteIndex, hdecode, hequal⟩
    subst sample
    have hvalue :=
      (decodeFinIndex_eq_some_iff.mp hdecode)
    simpa [encodeNormalizedOccurrenceListSeed] using hvalue
  · intro hencode
    let finiteIndex :=
      normalizedOccurrenceListSeedFinEquiv occurrences liveScale denominator
        sample
    refine ⟨finiteIndex, ?_, ?_⟩
    · apply decodeFinIndex_eq_some_iff.mpr
      simpa [finiteIndex, encodeNormalizedOccurrenceListSeed] using hencode
    · exact
        (normalizedOccurrenceListSeedFinEquiv occurrences liveScale
          denominator).symm_apply_apply sample

def encodePrimeListSample
    {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (sample :
      PrimeIndex cutoff ×
        NormalizedOccurrenceListSeed occurrences liveScale denominator) : ℕ :=
  (primeListSampleFinEquiv occurrences liveScale denominator sample).val

def decodePrimeListSample
    {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator index : ℕ) :
    Option
      (PrimeIndex cutoff ×
        NormalizedOccurrenceListSeed occurrences liveScale denominator) :=
  (decodeFinIndex
      (Fintype.card
        (PrimeIndex cutoff ×
          NormalizedOccurrenceListSeed occurrences liveScale denominator))
      index).map
    (primeListSampleFinEquiv occurrences liveScale denominator).symm

@[simp] theorem decodePrimeListSample_encode
    {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (sample :
      PrimeIndex cutoff ×
        NormalizedOccurrenceListSeed occurrences liveScale denominator) :
    decodePrimeListSample occurrences liveScale denominator
        (encodePrimeListSample occurrences liveScale denominator sample) =
      some sample := by
  let enumeration :
      (PrimeIndex cutoff ×
          NormalizedOccurrenceListSeed occurrences liveScale denominator) ≃
        Fin
          (Fintype.card
            (PrimeIndex cutoff ×
              NormalizedOccurrenceListSeed occurrences liveScale
                denominator)) :=
    primeListSampleFinEquiv (cutoff := cutoff) occurrences liveScale
      denominator
  let finiteIndex := enumeration sample
  have hdecode :
      decodeFinIndex
          (Fintype.card
            (PrimeIndex cutoff ×
              NormalizedOccurrenceListSeed occurrences liveScale
                denominator))
          finiteIndex.val =
        some finiteIndex :=
    decodeFinIndex_of_lt finiteIndex.isLt
  rw [decodePrimeListSample, encodePrimeListSample]
  change
    Option.map enumeration.symm
        (decodeFinIndex
          (Fintype.card
            (PrimeIndex cutoff ×
              NormalizedOccurrenceListSeed occurrences liveScale
                denominator))
          finiteIndex.val) =
      some sample
  rw [hdecode]
  simp [finiteIndex, enumeration]

theorem decodePrimeListSample_eq_some_iff
    {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator index : ℕ)
    (sample :
      PrimeIndex cutoff ×
        NormalizedOccurrenceListSeed occurrences liveScale denominator) :
    decodePrimeListSample occurrences liveScale denominator index =
        some sample ↔
      encodePrimeListSample occurrences liveScale denominator sample =
        index := by
  simp only [decodePrimeListSample, Option.map_eq_some_iff]
  constructor
  · rintro ⟨finiteIndex, hdecode, hequal⟩
    subst sample
    have hvalue := decodeFinIndex_eq_some_iff.mp hdecode
    simpa [encodePrimeListSample] using hvalue
  · intro hencode
    let finiteIndex :=
      primeListSampleFinEquiv occurrences liveScale denominator sample
    refine ⟨finiteIndex, ?_, ?_⟩
    · apply decodeFinIndex_eq_some_iff.mpr
      simpa [finiteIndex, encodePrimeListSample] using hencode
    · exact
        Equiv.symm_apply_apply
          (primeListSampleFinEquiv occurrences liveScale denominator)
          sample

/-! ## Canonical dependent child selections -/

/-- A threshold child tuple is encoded in circuit order.  The length and every
dependent child bound are recovered from the request, so the raw code cannot
smuggle a second circuit shape into the row evaluator. -/
def thresholdChildSelectionDigits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (selection : ThresholdChildSelection algorithm request) : List ℕ :=
  List.ofFn fun circuitIndex => (selection circuitIndex).val

private def thresholdChildSelectionFromDigits
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (digits : List ℕ)
    (hlength : digits.length = request.circuits.length)
    (hvalid : ∀ circuitIndex : Fin request.circuits.length,
      digits.get ⟨circuitIndex.val, by omega⟩ <
        (topChildren algorithm
          (request.circuits.get circuitIndex)).length) :
    ThresholdChildSelection algorithm request :=
  fun circuitIndex =>
    ⟨digits.get ⟨circuitIndex.val, by omega⟩, hvalid circuitIndex⟩

private theorem thresholdChildSelectionFromDigits_canonical
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (selection : ThresholdChildSelection algorithm request) :
    thresholdChildSelectionFromDigits algorithm request
        (thresholdChildSelectionDigits algorithm request selection)
        (by simp [thresholdChildSelectionDigits])
        (by
          intro circuitIndex
          simp [thresholdChildSelectionDigits]) =
      selection := by
  funext circuitIndex
  apply Fin.ext
  simp [thresholdChildSelectionFromDigits, thresholdChildSelectionDigits]

def encodeThresholdChildSelection
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (selection : ThresholdChildSelection algorithm request) : ℕ :=
  encodeBalancedList
    (thresholdChildSelectionDigits algorithm request selection)

private def decodeThresholdChildSelectionCandidate
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (code : ℕ) :
    Option (ThresholdChildSelection algorithm request) :=
  match decodeBalancedList code with
  | some digits =>
      if hlength : digits.length = request.circuits.length then
        if hvalid : ∀ circuitIndex : Fin request.circuits.length,
            digits.get ⟨circuitIndex.val, by omega⟩ <
              (topChildren algorithm
                (request.circuits.get circuitIndex)).length then
          some
            (thresholdChildSelectionFromDigits algorithm request digits
              hlength hvalid)
        else none
      else none
  | none => none

/-- Partial canonical parser for dependent child tuples. -/
def decodeThresholdChildSelection
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (code : ℕ) :
    Option (ThresholdChildSelection algorithm request) :=
  (decodeThresholdChildSelectionCandidate algorithm request code).bind
    fun selection =>
      if encodeThresholdChildSelection algorithm request selection = code then
        some selection
      else none

@[simp] theorem decodeThresholdChildSelection_encode
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (selection : ThresholdChildSelection algorithm request) :
    decodeThresholdChildSelection algorithm request
        (encodeThresholdChildSelection algorithm request selection) =
      some selection := by
  unfold decodeThresholdChildSelection
  unfold decodeThresholdChildSelectionCandidate
  unfold encodeThresholdChildSelection
  rw [decodeBalancedList_encode]
  dsimp only
  rw [dif_pos (by simp [thresholdChildSelectionDigits])]
  rw [dif_pos (by
    intro circuitIndex
    simp [thresholdChildSelectionDigits])]
  simp only [Option.bind_some]
  rw [thresholdChildSelectionFromDigits_canonical]
  simp

theorem encodeThresholdChildSelection_of_decode
    {algorithm : ExecutableExactDecompositionAlgorithm}
    {request : FourfoldRequest NormalizedThresholdThresholdCircuit}
    {code : ℕ}
    {selection : ThresholdChildSelection algorithm request}
    (hdecode :
      decodeThresholdChildSelection algorithm request code =
        some selection) :
    encodeThresholdChildSelection algorithm request selection = code := by
  unfold decodeThresholdChildSelection at hdecode
  generalize hcandidate :
    decodeThresholdChildSelectionCandidate algorithm request code =
      candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

/-! ## Canonical typed-envelope decoding -/

private def decodeCircuitCodeList
    {Circuit : CircuitFamily}
    (codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit)
    (q : ℕ) : List ℕ → Option (List (Circuit q))
  | [] => some []
  | code :: codes => do
      let circuit ← codec.decode q code
      let circuits ← decodeCircuitCodeList codec q codes
      pure (circuit :: circuits)

private theorem decodeCircuitCodeList_encode
    {Circuit : CircuitFamily}
    (codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit)
    {q : ℕ} (circuits : List (Circuit q)) :
    decodeCircuitCodeList codec q (circuits.map codec.encode) =
      some circuits := by
  induction circuits with
  | nil => rfl
  | cons circuit circuits ih =>
      simp [decodeCircuitCodeList, codec.decode_encode, ih]

private def decodeFourfoldEnvelopeCandidate
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit)
    (q code : ℕ) : Option (FourfoldRequest Circuit) :=
  let outer := Nat.unpair code
  let payload := Nat.unpair outer.2
  match decodeNat outer.1, decodeBalancedList payload.2 with
  | some decodedFamily, some circuitCodes =>
      if decodedFamily = familyTag then
        if payload.1 = q then
          (decodeCircuitCodeList codec q circuitCodes).map fun circuits =>
            ⟨q, circuits⟩
        else none
      else none
  | _, _ => none

/-- Decode precisely the typed handoff emitted by the fixed envelope program.
The final re-encoding check rejects alternate pair/list representations. -/
def decodeFourfoldEnvelope
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit)
    (q code : ℕ) : Option (FourfoldRequest Circuit) :=
  (decodeFourfoldEnvelopeCandidate familyTag codec q code).bind
    fun request =>
      if fourfoldRequestEnvelopeOutput familyTag codec.encode request = code then
        some request
      else none

@[simp] theorem decodeFourfoldEnvelope_output
    {Circuit : CircuitFamily}
    (familyTag : ℕ)
    (codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit)
    (request : FourfoldRequest Circuit) :
    decodeFourfoldEnvelope familyTag codec request.q
        (fourfoldRequestEnvelopeOutput familyTag codec.encode request) =
      some request := by
  cases request with
  | mk q circuits =>
      unfold decodeFourfoldEnvelope
      unfold decodeFourfoldEnvelopeCandidate
      unfold fourfoldRequestEnvelopeOutput
      simp [decodeCircuitCodeList_encode]

theorem fourfoldEnvelope_output_of_decode
    {Circuit : CircuitFamily}
    {familyTag q code : ℕ}
    {codec : CanonicalWitnessCodec.CanonicalCircuitCodec Circuit}
    {request : FourfoldRequest Circuit}
    (hdecode :
      decodeFourfoldEnvelope familyTag codec q code = some request) :
    fourfoldRequestEnvelopeOutput familyTag codec.encode request = code := by
  unfold decodeFourfoldEnvelope at hdecode
  generalize hcandidate :
    decodeFourfoldEnvelopeCandidate familyTag codec q code =
      candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

def decodeSymmetricFourfoldEnvelope (q code : ℕ) :
    Option (FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  decodeFourfoldEnvelope symmetricCircuitFamilyTag
    CanonicalWitnessCodec.symmetricCircuitCodec q code

def decodeThresholdFourfoldEnvelope (q code : ℕ) :
    Option (FourfoldRequest NormalizedThresholdThresholdCircuit) :=
  decodeFourfoldEnvelope thresholdCircuitFamilyTag
    CanonicalWitnessCodec.thresholdCircuitCodec q code

/-! ## One pure total row evaluator -/

/-- Low-to-high interpretation of the row ABI's input field.  The public call
builder always supplies an in-range canonical `encodeBitInput`; defining this
for every natural keeps malformed raw calls total. -/
def rowBitInputOfCode (q code : ℕ) : BitInput q :=
  fun bit => code.testBit bit.val

@[simp] theorem rowBitInputOfCode_encode
    {q : ℕ} (input : BitInput q) :
    rowBitInputOfCode q (encodeBitInput input) = input := by
  funext bit
  unfold rowBitInputOfCode
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt input bit.val bit.isLt

/-- Total executable symmetric row evaluation.  Out-of-range row indices map
to false; the proof theorem below identifies the structural compiler with the
canonical supplier specification on every production row. -/
def evaluateCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale targetDenominator rowIndex inputCode : ℕ) : Bool :=
  let denominator :=
    symmetricListDenominator request targetDenominator
  match
      decodeNormalizedOccurrenceListSeed
        (symmetricFourfoldOccurrences request) liveScale denominator
        rowIndex with
  | some sample =>
      executableCanonicalSymmetricFourfoldRow request liveScale denominator
        (rowBitInputOfCode request.q inputCode) sample
  | none => false

theorem evaluateCanonicalSymmetricFourfoldRow_refines
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale targetDenominator : ℕ)
    (index : Fin
      (Fintype.card
        (NormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request targetDenominator))))
    (input : BitInput request.q) :
    evaluateCanonicalSymmetricFourfoldRow request liveScale
        targetDenominator index.val (encodeBitInput input) =
      canonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request targetDenominator) input
        ((normalizedOccurrenceListSeedFinEquiv
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request targetDenominator)).symm
            index) := by
  let sample :=
    (normalizedOccurrenceListSeedFinEquiv
      (symmetricFourfoldOccurrences request) liveScale
      (symmetricListDenominator request targetDenominator)).symm index
  have hindex :
      encodeNormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request targetDenominator) sample =
        index.val := by
    simp [sample, encodeNormalizedOccurrenceListSeed]
  unfold evaluateCanonicalSymmetricFourfoldRow
  dsimp only
  rw [← hindex]
  rw [decodeNormalizedOccurrenceListSeed_encode]
  rw [rowBitInputOfCode_encode]
  exact executableCanonicalSymmetricFourfoldRow_refines request liveScale
    (symmetricListDenominator request targetDenominator) input sample

/-- Total executable threshold row over the single prime/list mixed-radix
index.  The child-selection disjunction remains inside the row and is derived
from the same exact-decomposition algorithm. -/
def evaluateCanonicalThresholdFourfoldRow
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale targetDenominator rowIndex inputCode : ℕ) : Bool :=
  let primeDenominator :=
    thresholdPrimeUnionDenominator algorithm request targetDenominator
  let listDenominator :=
    thresholdListUnionDenominator algorithm request targetDenominator
  let cutoff :=
    thresholdPrimeCutoff algorithm request primeDenominator
  match
      decodePrimeListSample (cutoff := cutoff)
        (thresholdFourfoldOccurrences request) liveScale listDenominator
        rowIndex with
  | some sample =>
      executableCanonicalThresholdFourfoldRow algorithm request liveScale
        primeDenominator listDenominator
        (rowBitInputOfCode request.q inputCode) sample
  | none => false

set_option maxHeartbeats 800000 in
-- The dependent mixed-radix threshold index needs extra elaboration budget.
theorem evaluateCanonicalThresholdFourfoldRow_refines
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (liveScale targetDenominator : ℕ)
    (index : Fin
      (Fintype.card
        (PrimeIndex
            (thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                targetDenominator)) ×
          NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences request) liveScale
            (thresholdListUnionDenominator algorithm request
              targetDenominator))))
    (input : BitInput request.q) :
    evaluateCanonicalThresholdFourfoldRow algorithm request liveScale
        targetDenominator index.val (encodeBitInput input) =
      canonicalThresholdFourfoldRow algorithm request liveScale
        (thresholdPrimeUnionDenominator algorithm request targetDenominator)
        (thresholdListUnionDenominator algorithm request targetDenominator)
        input
        ((primeListSampleFinEquiv
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                targetDenominator))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            targetDenominator)).symm index) := by
  let primeDenominator :=
    thresholdPrimeUnionDenominator algorithm request targetDenominator
  let listDenominator :=
    thresholdListUnionDenominator algorithm request targetDenominator
  let cutoff := thresholdPrimeCutoff algorithm request primeDenominator
  let sample :=
    (primeListSampleFinEquiv (cutoff := cutoff)
      (thresholdFourfoldOccurrences request) liveScale
      listDenominator).symm index
  have hindex :
      encodePrimeListSample (cutoff := cutoff)
          (thresholdFourfoldOccurrences request) liveScale listDenominator
          sample =
        index.val := by
    change
      ((primeListSampleFinEquiv (cutoff := cutoff)
        (thresholdFourfoldOccurrences request) liveScale listDenominator)
          sample).val = index.val
    rw [show
      (primeListSampleFinEquiv (cutoff := cutoff)
          (thresholdFourfoldOccurrences request) liveScale listDenominator)
          sample = index by
        exact (primeListSampleFinEquiv (cutoff := cutoff)
          (thresholdFourfoldOccurrences request) liveScale
          listDenominator).apply_symm_apply index]
  unfold evaluateCanonicalThresholdFourfoldRow
  dsimp only
  change
    (match
        decodePrimeListSample (cutoff := cutoff)
          (thresholdFourfoldOccurrences request) liveScale listDenominator
          index.val with
      | some decoded =>
          executableCanonicalThresholdFourfoldRow algorithm request liveScale
            primeDenominator listDenominator
            (rowBitInputOfCode request.q (encodeBitInput input)) decoded
      | none => false) =
      canonicalThresholdFourfoldRow algorithm request liveScale
        primeDenominator listDenominator input sample
  rw [← hindex]
  rw [decodePrimeListSample_encode]
  rw [rowBitInputOfCode_encode]
  exact executableCanonicalThresholdFourfoldRow_refines algorithm request
    liveScale primeDenominator listDenominator input sample

/-- One executable evaluator for the one row ABI.  Mode is the only branch;
typed envelope decoding, index validation, and malformed-call behavior are
otherwise shared. -/
def evaluateCanonicalFourfoldRow
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (raw : FourfoldRowRequest) : Bool :=
  match raw.mode with
  | .symmetric =>
      match decodeSymmetricFourfoldEnvelope raw.q raw.envelopeCode with
      | some request =>
          evaluateCanonicalSymmetricFourfoldRow request liveScale
            (fixedTargetDenominator accuracyExponent raw.q)
            raw.rowIndex raw.inputCode
      | none => false
  | .threshold =>
      match decodeThresholdFourfoldEnvelope raw.q raw.envelopeCode with
      | some request =>
          evaluateCanonicalThresholdFourfoldRow algorithm request liveScale
            (fixedTargetDenominator accuracyExponent raw.q)
            raw.rowIndex raw.inputCode
      | none => false

theorem evaluateCanonicalFourfoldRow_symmetric
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (symmetricFourfoldRowRequest request rowIndex input) =
      evaluateCanonicalSymmetricFourfoldRow request liveScale
        (fixedTargetDenominator accuracyExponent request.q)
        rowIndex (encodeBitInput input) := by
  unfold evaluateCanonicalFourfoldRow symmetricFourfoldRowRequest
  unfold decodeSymmetricFourfoldEnvelope
  rw [decodeFourfoldEnvelope_output]

theorem evaluateCanonicalFourfoldRow_threshold
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (rowIndex : ℕ) (input : BitInput request.q) :
    evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (thresholdFourfoldRowRequest request rowIndex input) =
      evaluateCanonicalThresholdFourfoldRow algorithm request liveScale
        (fixedTargetDenominator accuracyExponent request.q)
        rowIndex (encodeBitInput input) := by
  unfold evaluateCanonicalFourfoldRow thresholdFourfoldRowRequest
  unfold decodeThresholdFourfoldEnvelope
  rw [decodeFourfoldEnvelope_output]

theorem evaluateCanonicalFourfoldRow_symmetric_refines
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (index : Fin
      (Fintype.card
        (NormalizedOccurrenceListSeed
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q)))))
    (input : BitInput request.q) :
    evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (symmetricFourfoldRowRequest request index.val input) =
      canonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request
          (fixedTargetDenominator accuracyExponent request.q)) input
        ((normalizedOccurrenceListSeedFinEquiv
          (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (fixedTargetDenominator accuracyExponent request.q))).symm
              index) := by
  rw [evaluateCanonicalFourfoldRow_symmetric]
  exact evaluateCanonicalSymmetricFourfoldRow_refines request liveScale
    (fixedTargetDenominator accuracyExponent request.q) index input

set_option maxHeartbeats 800000 in
-- The dependent prime/list index makes this direct dispatch refinement kernel-heavy.
theorem evaluateCanonicalFourfoldRow_threshold_refines
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (index : Fin
      (Fintype.card
        (PrimeIndex
            (thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q))) ×
          NormalizedOccurrenceListSeed
            (thresholdFourfoldOccurrences request) liveScale
            (thresholdListUnionDenominator algorithm request
              (fixedTargetDenominator accuracyExponent request.q)))))
    (input : BitInput request.q) :
    evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (thresholdFourfoldRowRequest request index.val input) =
      canonicalThresholdFourfoldRow algorithm request liveScale
        (thresholdPrimeUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        (thresholdListUnionDenominator algorithm request
          (fixedTargetDenominator accuracyExponent request.q))
        input
        ((primeListSampleFinEquiv
          (cutoff :=
            thresholdPrimeCutoff algorithm request
              (thresholdPrimeUnionDenominator algorithm request
                (fixedTargetDenominator accuracyExponent request.q)))
          (thresholdFourfoldOccurrences request) liveScale
          (thresholdListUnionDenominator algorithm request
            (fixedTargetDenominator accuracyExponent request.q))).symm
              index) := by
  rw [evaluateCanonicalFourfoldRow_threshold]
  exact evaluateCanonicalThresholdFourfoldRow_refines algorithm request
    liveScale (fixedTargetDenominator accuracyExponent request.q) index input

/-! ## Executable rows at the aggregation boundary -/

/-- Replace only the row implementation of a proved preprocessor.  The
pointwise equality is discharged here once, so downstream aggregation consumes
the executable row directly and carries no semantic callback premise. -/
def withExtensionallyEqualFourfoldRow
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (specification : FourfoldRowPreprocessor Circuit evaluate)
    (replacement : (request : FourfoldRequest Circuit) →
      Fin (specification.rowCount request) → BitInput request.q → Bool)
    (hrefines : ∀ request index input,
      replacement request index input =
        specification.row request index input) :
    FourfoldRowPreprocessor Circuit evaluate where
  rowCount := specification.rowCount
  rowCountPositive := specification.rowCountPositive
  row := replacement
  failure := specification.failure
  failureNonnegative := specification.failureNonnegative
  pointwise := by
    intro request input
    simpa only [hrefines] using specification.pointwise request input

noncomputable def executableSymmetricFourfoldRows
    (spectrum : ExpanderSpectrumContract)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ) :
    FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval :=
  let specification :=
    symmetricFourfoldRows spectrum liveScale
      (fixedTargetDenominator accuracyExponent)
  withExtensionallyEqualFourfoldRow specification
    (fun request index input =>
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (symmetricFourfoldRowRequest request index.val input))
    (by
      intro request index input
      simpa [specification, symmetricFourfoldRows] using
        evaluateCanonicalFourfoldRow_symmetric_refines algorithm liveScale
          accuracyExponent request index input)

set_option maxHeartbeats 800000 in
-- Elaborating the dependent prime/list replacement against the specification is kernel-heavy.
noncomputable def executableThresholdFourfoldRows
    (spectrum : ExpanderSpectrumContract)
    (theta : PrimeThetaBoundContract)
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (liveScale accuracyExponent : ℕ) :
    FourfoldRowPreprocessor NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.eval :=
  let specification :=
    thresholdFourfoldRows spectrum theta algorithm liveScale
      (fixedTargetDenominator accuracyExponent)
  withExtensionallyEqualFourfoldRow specification
    (fun request index input =>
      evaluateCanonicalFourfoldRow algorithm liveScale accuracyExponent
        (thresholdFourfoldRowRequest request index.val input))
    (by
      intro request index input
      simpa [specification, thresholdFourfoldRows] using
        evaluateCanonicalFourfoldRow_threshold_refines algorithm liveScale
          accuracyExponent request index input)

end NearCubicWires.CanonicalFourfoldRowProgram
