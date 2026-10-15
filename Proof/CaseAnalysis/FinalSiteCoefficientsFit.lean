import Proof.CaseAnalysis.FinalSupplierCalls
import Proof.CaseAnalysis.FinalExactnessFamily

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteCoefficientsFit

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Rationals of bounded bit size -/

/-- A rational whose numerator magnitude and denominator are both at most
`2 ^ bits`. -/
def Fits (bits : ℕ) (q : ℚ) : Prop :=
  q.num.natAbs ≤ 2 ^ bits ∧ q.den ≤ 2 ^ bits

theorem Fits.mono {bits bits' : ℕ} {q : ℚ} (h : Fits bits q) (hle : bits ≤ bits') :
    Fits bits' q :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hle),
    h.2.trans (Nat.pow_le_pow_right (by norm_num) hle)⟩

/-- `n /. d` has numerator magnitude at most `|n|`. -/
theorem natAbs_num_divInt_le (n : ℤ) {d : ℤ} (hd : d ≠ 0) :
    (Rat.divInt n d).num.natAbs ≤ n.natAbs := by
  by_cases hn : n = 0
  · subst hn
    rw [Rat.zero_divInt]
    simp
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd n hd) hn

/-- `n /. d` has denominator at most `d`. -/
theorem den_divInt_le (n : ℤ) (d : ℕ) (hd : 0 < d) :
    (Rat.divInt n (d : ℤ)).den ≤ d :=
  Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp (Rat.den_dvd n d))

/-- Bit budgets add under multiplication. -/
theorem Fits.mul {a b : ℕ} {x y : ℚ} (hx : Fits a x) (hy : Fits b y) :
    Fits (a + b) (x * y) := by
  have hxy : x * y = Rat.divInt (x.num * y.num) ((x.den * y.den : ℕ) : ℤ) := by
    rw [Nat.cast_mul, ← Rat.divInt_mul_divInt, Rat.num_divInt_den, Rat.num_divInt_den]
  have hd : ((x.den * y.den : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero x.den_nz y.den_nz
  rw [hxy]
  constructor
  · calc (Rat.divInt (x.num * y.num) ((x.den * y.den : ℕ) : ℤ)).num.natAbs
        ≤ (x.num * y.num).natAbs := natAbs_num_divInt_le _ hd
      _ = x.num.natAbs * y.num.natAbs := Int.natAbs_mul _ _
      _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul hx.1 hy.1
      _ = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm
  · calc (Rat.divInt (x.num * y.num) ((x.den * y.den : ℕ) : ℤ)).den
        ≤ x.den * y.den := den_divInt_le _ _ (Nat.mul_pos x.den_pos y.den_pos)
      _ ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul hx.2 hy.2
      _ = 2 ^ (a + b) := (Nat.pow_add 2 a b).symm

theorem Fits.neg {bits : ℕ} {q : ℚ} (h : Fits bits q) : Fits bits (-q) := by
  refine ⟨?_, ?_⟩
  · rw [Rat.neg_num, Int.natAbs_neg]
    exact h.1
  · rw [Rat.neg_den]
    exact h.2

theorem fits_one : Fits 0 1 := by
  simp [Fits]

theorem fits_two : Fits 1 2 := by
  simp [Fits]

theorem fits_neg_one : Fits 0 (-1) := fits_one.neg

theorem fits_neg_two : Fits 1 (-2) := fits_two.neg

/-- `1 / 2 ^ k` costs exactly `k` bits (all in the denominator). -/
theorem fits_inv_two_pow (k : ℕ) : Fits k (1 / (2 ^ k : ℚ)) := by
  have h2 : (2 ^ k : ℚ) = ((2 ^ k : ℕ) : ℚ) := by push_cast; rfl
  rw [Fits, one_div, h2, Rat.inv_natCast_num_of_pos (Nat.two_pow_pos k),
    Rat.inv_natCast_den_of_pos (Nat.two_pow_pos k)]
  exact ⟨by rw [Int.natAbs_one]; exact Nat.one_le_two_pow, le_rfl⟩

theorem fits_half : Fits 1 (1 / 2) := by
  simpa using fits_inv_two_pow 1

/-! ## §2 Polynomials whose every coefficient fits -/

/-- Every monomial coefficient of `polynomial` fits in `bits` bits. -/
def PolynomialFits {Atom : Type} {degree : ℕ} (bits : ℕ)
    (polynomial : CircuitPolynomial Atom degree) : Prop :=
  ∀ monomial ∈ polynomial.monomials, Fits bits monomial.coefficient

theorem PolynomialFits.mono {Atom : Type} {degree : ℕ} {bits bits' : ℕ}
    {polynomial : CircuitPolynomial Atom degree}
    (h : PolynomialFits bits polynomial) (hle : bits ≤ bits') :
    PolynomialFits bits' polynomial :=
  fun monomial hmonomial => (h monomial hmonomial).mono hle

theorem PolynomialFits.weaken {Atom : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree) {bits : ℕ}
    {polynomial : CircuitPolynomial Atom sourceDegree}
    (h : PolynomialFits bits polynomial) :
    PolynomialFits bits (polynomial.weaken hdegree) := by
  intro monomial hmonomial
  rcases List.mem_map.mp hmonomial with ⟨monomial', hmonomial', rfl⟩
  exact h monomial' hmonomial'

theorem PolynomialFits.scale {Atom : Type} {degree : ℕ} {bits scalarBits : ℕ}
    {polynomial : CircuitPolynomial Atom degree} {scalar : ℚ}
    (h : PolynomialFits bits polynomial) (hscalar : Fits scalarBits scalar) :
    PolynomialFits (scalarBits + bits) (polynomial.scale scalar) := by
  intro monomial hmonomial
  rcases List.mem_map.mp hmonomial with ⟨monomial', hmonomial', rfl⟩
  exact hscalar.mul (h monomial' hmonomial')

theorem PolynomialFits.add {Atom : Type} {degree : ℕ} {bits : ℕ}
    {left right : CircuitPolynomial Atom degree}
    (hleft : PolynomialFits bits left) (hright : PolynomialFits bits right) :
    PolynomialFits bits (left.add right) := by
  intro monomial hmonomial
  rcases List.mem_append.mp hmonomial with hmonomial | hmonomial
  · exact hleft monomial hmonomial
  · exact hright monomial hmonomial

theorem PolynomialFits.mul {Atom : Type} {leftDegree rightDegree : ℕ}
    {leftBits rightBits : ℕ}
    {left : CircuitPolynomial Atom leftDegree}
    {right : CircuitPolynomial Atom rightDegree}
    (hleft : PolynomialFits leftBits left) (hright : PolynomialFits rightBits right) :
    PolynomialFits (leftBits + rightBits) (left.mul right) := by
  intro monomial hmonomial
  rcases List.mem_flatMap.mp hmonomial with ⟨leftMonomial, hleftMonomial, hmonomial⟩
  rcases List.mem_map.mp hmonomial with ⟨rightMonomial, hrightMonomial, rfl⟩
  exact (hleft leftMonomial hleftMonomial).mul (hright rightMonomial hrightMonomial)

theorem polynomialFits_constant {Atom : Type} (degree : ℕ) {bits : ℕ} {coefficient : ℚ}
    (h : Fits bits coefficient) :
    PolynomialFits bits (CircuitPolynomial.constant (Circuit := Atom) degree coefficient) := by
  intro monomial hmonomial
  rcases List.mem_singleton.mp hmonomial with rfl
  exact h

theorem polynomialFits_atomPolynomial {Atom : Type} (circuit : Atom) :
    PolynomialFits 0 (atomPolynomial circuit) := by
  intro monomial hmonomial
  rcases List.mem_singleton.mp hmonomial with rfl
  exact fits_one

theorem polynomialFits_linearPolynomial {Circuit : CircuitFamily} {q : ℕ} {bits : ℕ}
    (terms : List (LegalCircuitTerm Circuit q))
    (h : ∀ term ∈ terms, Fits bits term.coefficient) :
    PolynomialFits bits (linearPolynomial terms) := by
  intro monomial hmonomial
  rcases List.mem_map.mp hmonomial with ⟨term, hterm, rfl⟩
  exact h term hterm

/-! ## §3 The paper's expansions: `(Enc_s − T)^2`, `T^2 (1 − T)^2`, `T^2`, `Cons_i` -/

theorem polynomialFits_systematicValidityPolynomial {Atom : Type} (systematic : Atom)
    {bits : ℕ} {linear : CircuitPolynomial Atom 1} (h : PolynomialFits bits linear) :
    PolynomialFits (2 * bits + 1) (systematicValidityPolynomial systematic linear) := by
  dsimp only [systematicValidityPolynomial]
  refine PolynomialFits.add ?_ (PolynomialFits.add ?_ ?_)
  · exact ((polynomialFits_atomPolynomial systematic).weaken _).mono (by omega)
  · exact (((polynomialFits_atomPolynomial systematic).mul h).scale fits_neg_two).mono
      (by omega)
  · exact (h.mul h).mono (by omega)

theorem polynomialFits_auxiliaryValidityPolynomial {Atom : Type}
    {bits : ℕ} {linear : CircuitPolynomial Atom 1} (h : PolynomialFits bits linear) :
    PolynomialFits (4 * bits + 1) (auxiliaryValidityPolynomial linear) := by
  dsimp only [auxiliaryValidityPolynomial]
  refine PolynomialFits.add ?_ (PolynomialFits.add ?_ ?_)
  · exact ((h.mul h).weaken _).mono (by omega)
  · exact ((((h.mul h).mul h).weaken _).scale fits_neg_two).mono (by omega)
  · exact ((h.mul h).mul (h.mul h)).mono (by omega)

theorem polynomialFits_secondMomentPolynomial {Atom : Type}
    {bits : ℕ} {linear : CircuitPolynomial Atom 1} (h : PolynomialFits bits linear) :
    PolynomialFits (2 * bits) (secondMomentPolynomial linear) := by
  dsimp only [secondMomentPolynomial]
  exact (h.mul h).mono (by omega)

theorem polynomialFits_literalPolynomial {Atom : Type} (negative : Bool)
    {bits : ℕ} {linear : CircuitPolynomial Atom 1} (h : PolynomialFits bits linear) :
    PolynomialFits bits (literalPolynomial negative linear) := by
  cases negative with
  | false =>
      rw [literalPolynomial, if_neg Bool.false_ne_true]
      exact h
  | true =>
      rw [literalPolynomial, if_pos rfl]
      exact PolynomialFits.add ((polynomialFits_constant 1 fits_one).mono (by omega))
        ((h.scale fits_neg_one).mono (by omega))

theorem polynomialFits_clausePolynomial {Atom : Type} (leftNegative rightNegative : Bool)
    {bits : ℕ} {left right : CircuitPolynomial Atom 1}
    (hleft : PolynomialFits bits left) (hright : PolynomialFits bits right) :
    PolynomialFits (2 * bits) (clausePolynomial leftNegative rightNegative left right) := by
  dsimp only [clausePolynomial]
  have hleft' := polynomialFits_literalPolynomial leftNegative hleft
  have hright' := polynomialFits_literalPolynomial rightNegative hright
  refine PolynomialFits.add ?_ (PolynomialFits.add ?_ ?_)
  · exact (hleft'.weaken _).mono (by omega)
  · exact (hright'.weaken _).mono (by omega)
  · exact ((hleft'.mul hright').scale fits_neg_one).mono (by omega)

/-! ## §4 The sites and the site calls -/

theorem polynomialFits_coordinatePenalty {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {bits : ℕ}
    (hcoordinate : ∀ j, PolynomialFits bits (coordinate j))
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    PolynomialFits (4 * bits + 1) (coordinatePenalty pcpp coordinate systematicAtom j) := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    rw [coordinatePenalty, Fin.addCases_left]
    exact ((polynomialFits_systematicValidityPolynomial _ (hcoordinate _)).weaken _).mono
      (by omega)
  · intro index
    rw [coordinatePenalty, Fin.addCases_right]
    exact polynomialFits_auxiliaryValidityPolynomial (hcoordinate _)

theorem polynomialFits_sitePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {bits : ℕ}
    (hcoordinate : ∀ j, PolynomialFits bits (coordinate j))
    (i : Fin (2 ^ pcpp.clauseBits)) :
    PolynomialFits (4 * bits + 2) (sitePolynomial phase pcpp coordinate systematicAtom i) := by
  cases phase with
  | penalty =>
      show PolynomialFits _ (penaltySite pcpp coordinate systematicAtom i)
      unfold penaltySite
      exact ((PolynomialFits.add
        (polynomialFits_coordinatePenalty pcpp coordinate systematicAtom hcoordinate _)
        (polynomialFits_coordinatePenalty pcpp coordinate systematicAtom hcoordinate _)).scale
          fits_half).mono (by omega)
  | moment =>
      show PolynomialFits _ (momentSite pcpp coordinate i)
      unfold momentSite
      exact ((polynomialFits_secondMomentPolynomial (hcoordinate _)).weaken _).mono (by omega)
  | clause =>
      show PolynomialFits _ (clauseSite pcpp coordinate i)
      unfold clauseSite
      exact ((polynomialFits_clausePolynomial _ _ (hcoordinate _) (hcoordinate _)).weaken _).mono
        (by omega)

/-- The site calls carry `pcpp.clauseBits` more denominator bits than the site:
`siteCalls` scales by `1 / 2 ^ pcpp.clauseBits`. -/
theorem polynomialFits_siteCalls {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {bits : ℕ}
    (hcoordinate : ∀ j, PolynomialFits bits (coordinate j))
    (address : Fin (2 ^ pcpp.clauseBits)) :
    PolynomialFits (pcpp.clauseBits + 4 * bits + 2)
      (siteCalls phase pcpp coordinate systematicAtom address) := by
  unfold siteCalls
  exact ((polynomialFits_sitePolynomial phase pcpp coordinate systematicAtom hcoordinate
    address).scale (fits_inv_two_pow pcpp.clauseBits)).mono (by omega)

/-! ## §5 From a bit budget to `CoefficientsFit` -/

/-- A polynomial whose coefficients fit in `bits < entryWidth` bits satisfies the
consumer's `CoefficientsFit entryWidth`: both sign parts of the numerator are at
most its magnitude, and `≤ 2 ^ bits < 2 ^ entryWidth`. -/
theorem coefficientsFit_of_polynomialFits {Atom : Type} {entryWidth bits : ℕ}
    {polynomial : CircuitPolynomial Atom 4} (h : PolynomialFits bits polynomial)
    (hw : bits < entryWidth) : CoefficientsFit entryWidth polynomial := by
  unfold CoefficientsFit
  intro monomial hmonomial
  obtain ⟨hnum, hden⟩ := h monomial hmonomial
  have hpow : 2 ^ bits < 2 ^ entryWidth := Nat.pow_lt_pow_right (by norm_num) hw
  have hpositive : monomial.coefficient.num.toNat ≤ monomial.coefficient.num.natAbs :=
    Int.toNat_le.mpr Int.le_natAbs
  have hnegative : (-monomial.coefficient.num).toNat ≤ monomial.coefficient.num.natAbs := by
    rw [← Int.natAbs_neg monomial.coefficient.num]
    exact Int.toNat_le.mpr Int.le_natAbs
  refine ⟨?_, ?_, lt_of_le_of_lt hden hpow⟩
  · show monomial.coefficient.num.toNat < 2 ^ entryWidth
    exact lt_of_le_of_lt (hpositive.trans hnum) hpow
  · show (-monomial.coefficient.num).toNat < 2 ^ entryWidth
    exact lt_of_le_of_lt (hnegative.trans hnum) hpow

/-! ## §6 The decoded family's coefficients -/

/-- The decoder's bit cap, read as a bit budget. -/
theorem fits_of_natBitLength_le {bits : ℕ} {q : ℚ}
    (h : natBitLength q.num.natAbs ≤ bits ∧ natBitLength q.den ≤ bits) : Fits bits q := by
  obtain ⟨hnum, hden⟩ := h
  unfold natBitLength at hnum hden
  exact ⟨(Nat.lt_pow_of_log_lt (by norm_num) (by omega)).le,
    (Nat.lt_pow_of_log_lt (by norm_num) (by omega)).le⟩

/-- The arity transport does not touch coefficients. -/
theorem exists_coefficient_of_mem_transportTerms {Circuit : CircuitFamily}
    {source target : ℕ} (harity : source = target)
    (terms : List (LegalCircuitTerm Circuit source))
    (term : LegalCircuitTerm Circuit target) (hterm : term ∈ transportTerms harity terms) :
    ∃ original ∈ terms, original.coefficient = term.coefficient := by
  subst harity
  exact ⟨term, hterm, rfl⟩

/-- **Every coordinate of the decoded family fits in `limits.coefficientBitCap`
bits** — this is `CheckedLegalCircuitSum.coefficient_bits_le`, transported. -/
theorem polynomialFits_familyCoordinate {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (harity : limits.expectedArity = target)
    (family : SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    PolynomialFits limits.coefficientBitCap (familyCoordinate harity family i) := by
  unfold familyCoordinate
  refine polynomialFits_linearPolynomial _ ?_
  intro term hterm
  obtain ⟨original, horiginal, hcoefficient⟩ :=
    exists_coefficient_of_mem_transportTerms _ _ term hterm
  rw [← hcoefficient]
  exact fits_of_natBitLength_le ((family.getSum i).coefficient_bits_le original horiginal)

/-! ## §7 The bound, and `hcoefficients` -/

/-- **The floor on `entryWidth`** (see the header for the origin of each
summand): clause-address bits, four family coefficients, the constants `-2`
and `1 / 2`, and strictness. -/
def coefficientBound (limits : LegalSumLimits) {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) : ℕ :=
  pcpp.clauseBits + 4 * limits.coefficientBitCap + 3

/-- **`hcoefficients`.**  At the decoded family, every site call's coefficients
fit any bank width at or above `coefficientBound limits pcpp`. -/
theorem siteCoefficientsFit_of {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits}
    {circuit : BooleanCircuit limits.expectedArity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (family :
      SumFamily Circuit wires description limits
        (pcpp.systematicBits + pcpp.auxiliaryBits))
    (systematicAtom : Fin pcpp.systematicBits → Circuit limits.expectedArity)
    (entryWidth : ℕ) (h : coefficientBound limits pcpp ≤ entryWidth) :
    ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth
        (siteCalls phase pcpp (familyCoordinate rfl family) systematicAtom address) :=
  fun address =>
    coefficientsFit_of_polynomialFits
      (polynomialFits_siteCalls phase pcpp (familyCoordinate rfl family) systematicAtom
        (fun j => polynomialFits_familyCoordinate rfl family j) address)
      (by unfold coefficientBound at h; omega)

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteCoefficientsFit
