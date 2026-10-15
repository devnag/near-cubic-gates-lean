import Proof.CaseAnalysis.FinalSiteCoefficientsFit
import Proof.CaseAnalysis.FinalThresholdWidths
import Proof.CaseAnalysis.FinalSupplierAccuracy

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth

open NearCubicWires
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The external row count is a power of two

Paper A.8 (`paper.tex:2253-2255`) bounds "the logarithm of the number of
external rows".  For the production symmetric family that logarithm is an exact
natural number, because the rows ARE the walk seeds. -/

/-- The exponent of one canonical walk-seed space: `2 * sideBits` vertex bits
(`MargulisVertex m = ZMod m × ZMod m`) plus `160` bits per transition
(`card PoweredMargulisLabel = 16 ^ 40 = 2 ^ 160`), over the
`canonicalWalkLength denominator - 1 = 2 * Nat.clog 2 (denominator + 1)`
transitions of the canonical odd walk. -/
def walkExponent (sideBits denominator : ℕ) : ℕ :=
  2 * sideBits + 160 * (2 * Nat.clog 2 (denominator + 1))

/-- **The walk-seed space has exactly `2 ^ walkExponent` points.**  No estimate:
`card_positiveSample` splits the transcript, `card_poweredMargulisLabel` gives
the label alphabet, and `ZMod.card` gives the square vertex set. -/
theorem card_walkSample (sideBits denominator : ℕ) :
    Fintype.card (MargulisWalkSample (2 ^ sideBits) (canonicalWalkLength denominator))
      = 2 ^ walkExponent sideBits denominator := by
  have hlen : canonicalWalkLength denominator
      = (2 * Nat.clog 2 (denominator + 1)).succ := rfl
  rw [hlen, card_positiveSample, card_poweredMargulisLabel]
  have hvertex : Fintype.card (MargulisVertex (2 ^ sideBits))
      = 2 ^ sideBits * 2 ^ sideBits := by
    simp [MargulisVertex, Fintype.card_prod, ZMod.card]
  rw [hvertex, walkExponent]
  have h16 : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
  rw [h16, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  ring_nf

/-- **The request's power-of-two exponent** — the paper's `h_D L_q` for the
production symmetric family, in closed form: the walk seed space built on the
graded Toeplitz rank of the request's occurrence pool, at the list denominator
the requested accuracy fixes. -/
def seedExponent (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale targetDenominator : ℕ) : ℕ :=
  walkExponent
    (toeplitzWalkSideBits
      (canonicalGradedRank (symmetricFourfoldOccurrences request).length
        (touchingCost (occurrenceSupport (symmetricFourfoldOccurrences request))
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))))
    (symmetricListDenominator request targetDenominator)

/-- **`|\mathcal E| = 2 ^ seedExponent`** (paper A.13.9's `|\mathcal E|`, paper
A.8's external rows).  The production symmetric preprocessor's row count is a
power of two on the nose — which is what makes ONE uniform denominator possible
at all (§3). -/
theorem rowCount_eq_two_pow (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (symmetricFourfoldRows spectrum liveScale target).rowCount request
      = 2 ^ seedExponent request liveScale (target request.q) :=
  card_walkSample _ _

/-- **The bank width.**  `coefficientFloor n` is intended as
`coefficientBound (limits n) (pcpp n)` at the decoded family of input length
`n`; `arity n` is the supplier's circuit arity there and `scale n` the uniform
denominator's exponent.  Nothing numeric is chosen: every summand is a consumer
obligation. -/
def entryWidth (coefficientFloor arity scale : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) (n : ℕ) : ℕ :=
  max (max (coefficientFloor n) (C10ThresholdWidths.thresholdWidth constants))
    (arity n + scale n + 1)

/-- The answer channel's own floor, read straight off the `max`. -/
theorem entryWidth_floor_answer (coefficientFloor arity scale : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) (n : ℕ) :
    arity n + scale n + 1 ≤ entryWidth coefficientFloor arity scale constants n :=
  le_max_right _ _

theorem entryWidth_floor (limits : CanonicalWitnessCodec.LegalSumLimits) {m : ℕ}
    {circuit : BooleanCircuit m} (pcpp : PointwisePCPP circuit)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    (coefficientFloor arity scale : ℕ → ℕ) (n : ℕ)
    (hcoefficient : C10SiteCoefficientsFit.coefficientBound limits pcpp
      ≤ coefficientFloor n) :
    C10SiteCoefficientsFit.coefficientBound limits pcpp
        ≤ entryWidth coefficientFloor arity scale constants n ∧
      C10ThresholdWidths.thresholdWidth constants
        ≤ entryWidth coefficientFloor arity scale constants n ∧
      arity n + scale n + 1 ≤ entryWidth coefficientFloor arity scale constants n := by
  exact ⟨hcoefficient.trans (le_trans (le_max_left _ _) (le_max_left _ _)),
    le_trans (le_max_right _ _) (le_max_left _ _),
    entryWidth_floor_answer coefficientFloor arity scale constants n⟩

/-- **`hcoefficients` at `entryWidth`**, i.e. floor 1 discharged all the way to
the shape `realizes_of_stage` asks for. -/
theorem siteCoefficientsFit_at_entryWidth {Circuit : CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : CanonicalWitnessCodec.LegalSumLimits}
    {circuit : BooleanCircuit limits.expectedArity}
    (phase : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (family : RepairOrdinary.CloseoutWitness.SumFamily Circuit wires description limits
      (pcpp.systematicBits + pcpp.auxiliaryBits))
    (systematicAtom : Fin pcpp.systematicBits → Circuit limits.expectedArity)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    (coefficientFloor arity scale : ℕ → ℕ) (n : ℕ)
    (hcoefficient : C10SiteCoefficientsFit.coefficientBound limits pcpp
      ≤ coefficientFloor n) :
    ∀ address : Fin (2 ^ pcpp.clauseBits),
      RepairOrdinary.CloseoutFinalC10SupplierCalls.CoefficientsFit
        (entryWidth coefficientFloor arity scale constants n)
        (RepairOrdinary.CloseoutFinalC10SupplierCalls.siteCalls phase pcpp
          (RepairOrdinary.CloseoutFinalC10ExactnessFamily.familyCoordinate rfl family)
          systematicAtom address) :=
  C10SiteCoefficientsFit.siteCoefficientsFit_of phase pcpp family systematicAtom
    (entryWidth coefficientFloor arity scale constants n)
    (entryWidth_floor limits pcpp constants coefficientFloor arity scale n
      hcoefficient).1

/-! ## §3 The answer channel — one uniform denominator

`realizes_of_stage` takes ONE `denominator : ℕ`.  A.13.9's own denominator
`|\mathcal E| * 2 ^ q = rowDenominator` is per-call, so the count is rescaled to
the uniform one. -/

/-- **The uniform denominator** `2 ^ (arity + scale)`.  A.13.9's `|\mathcal E|2^q`
with `|\mathcal E|` replaced by the common power of two `2 ^ scale`. -/
def denominator (arity scale : ℕ) : ℕ := 2 ^ (arity + scale)

/-- **The rescaled acceptance count**: A.13.9's `∑_e ∑_z T_{e,F(z)}(z)` carried
to the uniform denominator.  Where `rowDenominator ∣ denominator` this is exactly
`rowAnswer * (denominator / rowDenominator)`; elsewhere it is the floor, whose
error `answer_div_denominator_error` bounds by `1 / denominator`. -/
def answer {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity)) : ℕ :=
  rowAnswer rows arity factors * denominator arity scale
    / rowDenominator rows arity factors

theorem denominator_pos (arity scale : ℕ) : 0 < denominator arity scale :=
  Nat.two_pow_pos _

/-- A.13.9's denominator is positive: `rowCountPositive` and `2 ^ q`. -/
theorem rowDenominator_pos {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (factors : List (Circuit arity)) :
    0 < rowDenominator rows arity factors :=
  Nat.mul_pos (rows.rowCountPositive _) (Nat.two_pow_pos _)

/-- The acceptance count never exceeds the sample count: one `∑_e ∑_z` of bits
over `|\mathcal E| * 2 ^ q` samples. -/
theorem rowAnswer_le_rowDenominator {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (factors : List (Circuit arity)) :
    rowAnswer rows arity factors ≤ rowDenominator rows arity factors := by
  have hrow : ∀ index : Fin (rows.rowCount ⟨arity, factors⟩),
      (∑ input : BitInput arity,
        ((rows.aggregation ⟨arity, factors⟩).row index input).toNat)
        ≤ 2 ^ arity := by
    intro index
    calc (∑ input : BitInput arity,
            ((rows.aggregation ⟨arity, factors⟩).row index input).toNat)
        ≤ ∑ _input : BitInput arity, 1 :=
          Finset.sum_le_sum (fun input _ => by
            cases (rows.aggregation ⟨arity, factors⟩).row index input <;> simp)
      _ = 2 ^ arity := by simp
  calc rowAnswer rows arity factors
      = ∑ index : Fin (rows.rowCount ⟨arity, factors⟩),
          ∑ input : BitInput arity,
            ((rows.aggregation ⟨arity, factors⟩).row index input).toNat := rfl
    _ ≤ ∑ _index : Fin (rows.rowCount ⟨arity, factors⟩), 2 ^ arity :=
        Finset.sum_le_sum (fun index _ => hrow index)
    _ = rowDenominator rows arity factors := by
        simp [Finset.sum_const, rowDenominator]

/-- **A.13.9 at the uniform denominator.**  On every call whose per-request
denominator `|\mathcal E| * 2 ^ q` divides the uniform one, the rescaled count
over the uniform denominator IS the supplier's rational answer — the paper's
`\widehat p_{\mathrm S}`, unchanged. -/
theorem answer_div_denominator {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity))
    (hdvd : rowDenominator rows arity factors ∣ denominator arity scale) :
    ((answer rows arity scale factors : ℚ) / (denominator arity scale : ℚ))
      = rowSupplier rows arity factors := by
  obtain ⟨c, hc⟩ := hdvd
  have hR : 0 < rowDenominator rows arity factors := rowDenominator_pos rows arity factors
  have hc0 : 0 < c := by
    by_contra hcon
    have hzero : c = 0 := by omega
    rw [hzero, Nat.mul_zero] at hc
    exact absurd hc (denominator_pos arity scale).ne'
  have hans : answer rows arity scale factors = rowAnswer rows arity factors * c := by
    unfold answer
    rw [hc, show rowAnswer rows arity factors *
      (rowDenominator rows arity factors * c)
        = rowDenominator rows arity factors * (rowAnswer rows arity factors * c) by ring,
      Nat.mul_div_cancel_left _ hR]
  rw [hans, hc, ← rowSupplier_eq_ratio rows arity factors]
  have hcQ : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0.ne'
  push_cast
  rw [mul_comm ((rowDenominator rows arity factors : ℚ)) (c : ℚ),
    mul_comm ((rowAnswer rows arity factors : ℚ)) (c : ℚ)]
  exact mul_div_mul_left _ _ hcQ

/-- **The fit condition for the production symmetric family.**  `rowCount` is
`2 ^ seedExponent` (§1), so the per-request denominator divides the uniform one
as soon as the uniform exponent dominates the request's. -/
theorem rowDenominator_dvd_denominator (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale) :
    rowDenominator (symmetricFourfoldRows spectrum liveScale target) arity factors
      ∣ denominator arity scale := by
  have hcount := rowCount_eq_two_pow spectrum liveScale target ⟨arity, factors⟩
  have hrow : rowDenominator (symmetricFourfoldRows spectrum liveScale target) arity factors
      = 2 ^ (seedExponent ⟨arity, factors⟩ liveScale (target arity) + arity) := by
    rw [rowDenominator, hcount, ← Nat.pow_add]
  rw [hrow, denominator]
  exact Nat.pow_dvd_pow 2 (by omega)

/-- **A.13.9 for the production symmetric family, under the fit condition.** -/
theorem answer_div_denominator_of_fit (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (hfit : seedExponent ⟨arity, factors⟩ liveScale (target arity) ≤ scale) :
    ((answer (symmetricFourfoldRows spectrum liveScale target) arity scale factors : ℚ)
        / (denominator arity scale : ℚ))
      = rowSupplier (symmetricFourfoldRows spectrum liveScale target) arity factors :=
  answer_div_denominator _ arity scale factors
    (rowDenominator_dvd_denominator spectrum liveScale target arity scale factors hfit)

/-- **The unconditional rescaling error.**  On a call whose per-request
denominator does NOT divide the uniform one, the rescaled count is the floor, so
it still tracks `\widehat p_{\mathrm S}` to within one ulp of the uniform
denominator.  This is what lets S0 answer EVERY `factors : List Atom` with one
`denominator`. -/
theorem answer_div_denominator_error {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity)) :
    |((answer rows arity scale factors : ℚ) / (denominator arity scale : ℚ))
        - rowSupplier rows arity factors| ≤ 1 / (denominator arity scale : ℚ) := by
  have hR : 0 < rowDenominator rows arity factors := rowDenominator_pos rows arity factors
  have hD : 0 < denominator arity scale := denominator_pos arity scale
  have hRQ : (0 : ℚ) < (rowDenominator rows arity factors : ℚ) := by exact_mod_cast hR
  have hDQ : (0 : ℚ) < (denominator arity scale : ℚ) := by exact_mod_cast hD
  have hlow : answer rows arity scale factors * rowDenominator rows arity factors
      ≤ rowAnswer rows arity factors * denominator arity scale :=
    Nat.div_mul_le_self _ _
  have hhigh : rowAnswer rows arity factors * denominator arity scale
      < (answer rows arity scale factors + 1) * rowDenominator rows arity factors := by
    have hmod := Nat.div_add_mod
      (rowAnswer rows arity factors * denominator arity scale)
      (rowDenominator rows arity factors)
    have hlt := Nat.mod_lt
      (rowAnswer rows arity factors * denominator arity scale) hR
    have hexpand : (answer rows arity scale factors + 1)
        * rowDenominator rows arity factors
        = rowDenominator rows arity factors
            * (rowAnswer rows arity factors * denominator arity scale
              / rowDenominator rows arity factors)
          + rowDenominator rows arity factors := by
      unfold answer; ring
    rw [hexpand]
    omega
  have hlowQ : (answer rows arity scale factors : ℚ)
      * (rowDenominator rows arity factors : ℚ)
      ≤ (rowAnswer rows arity factors : ℚ) * (denominator arity scale : ℚ) := by
    exact_mod_cast hlow
  have hhighQ : (rowAnswer rows arity factors : ℚ) * (denominator arity scale : ℚ)
      ≤ ((answer rows arity scale factors : ℚ) + 1)
        * (rowDenominator rows arity factors : ℚ) := by
    exact_mod_cast hhigh.le
  rw [← rowSupplier_eq_ratio rows arity factors]
  have hle : (answer rows arity scale factors : ℚ) / (denominator arity scale : ℚ)
      ≤ (rowAnswer rows arity factors : ℚ) / (rowDenominator rows arity factors : ℚ) :=
    (div_le_div_iff₀ hDQ hRQ).mpr hlowQ
  have hge : (rowAnswer rows arity factors : ℚ) / (rowDenominator rows arity factors : ℚ)
      ≤ ((answer rows arity scale factors : ℚ) + 1) / (denominator arity scale : ℚ) :=
    (div_le_div_iff₀ hRQ hDQ).mpr hhighQ
  have hsplit : ((answer rows arity scale factors : ℚ) + 1)
      / (denominator arity scale : ℚ)
      = (answer rows arity scale factors : ℚ) / (denominator arity scale : ℚ)
        + 1 / (denominator arity scale : ℚ) := by
    rw [add_div]
  have hpos : (0 : ℚ) ≤ 1 / (denominator arity scale : ℚ) := le_of_lt (by positivity)
  rw [abs_le]
  rw [hsplit] at hge
  exact ⟨by linarith, by linarith⟩

/-- The production symmetric family's failure, read off the definition: it
depends on the request only through its arity, so it is uniform in the call. -/
theorem symmetric_failure (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (symmetricFourfoldRows spectrum liveScale target).failure request
      = (1 : ℝ) / ((target request.q + 1 : ℕ) : ℝ) := rfl

/-- **`hpoint` for the uniform-denominator supplier, with NO side condition.**
This is the lemma that makes one `denominator` answer every
`factors : List Atom`: the rescaled count over the uniform denominator is within
the row family's own failure PLUS one ulp of that denominator of the paper's
conjunction probability.  S0 takes
`supplier := fun factors => (answer … factors : ℚ) / denominator` (so `hsupplier`
is `rfl`) and pays `hpoint` here. -/
theorem uniform_supplier_error_le (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (target : ℕ → ℕ) (arity scale : ℕ)
    (factors : List (NormalizedSymmetricThresholdCircuit arity)) :
    |(((answer (symmetricFourfoldRows spectrum liveScale target) arity scale factors : ℚ)
            / (denominator arity scale : ℚ) : ℚ) : ℝ)
        - conjunctionProbability NormalizedSymmetricThresholdCircuit.eval factors|
      ≤ (1 : ℝ) / ((target arity + 1 : ℕ) : ℝ)
        + 1 / ((denominator arity scale : ℕ) : ℝ) := by
  have herr := answer_div_denominator_error
    (symmetricFourfoldRows spectrum liveScale target) arity scale factors
  have hpt := rowSupplier_error_le
    (symmetricFourfoldRows spectrum liveScale target) arity factors
  rw [symmetric_failure spectrum liveScale target ⟨arity, factors⟩] at hpt
  have hcast : |(((answer (symmetricFourfoldRows spectrum liveScale target) arity scale
              factors : ℚ) / (denominator arity scale : ℚ) : ℚ) : ℝ)
        - ((rowSupplier (symmetricFourfoldRows spectrum liveScale target) arity
            factors : ℚ) : ℝ)|
      ≤ 1 / ((denominator arity scale : ℕ) : ℝ) := by
    have hR := (Rat.cast_le (K := ℝ)).mpr herr
    push_cast at hR ⊢
    exact hR
  calc |(((answer (symmetricFourfoldRows spectrum liveScale target) arity scale
              factors : ℚ) / (denominator arity scale : ℚ) : ℚ) : ℝ)
          - conjunctionProbability NormalizedSymmetricThresholdCircuit.eval factors|
      ≤ |(((answer (symmetricFourfoldRows spectrum liveScale target) arity scale
              factors : ℚ) / (denominator arity scale : ℚ) : ℚ) : ℝ)
            - ((rowSupplier (symmetricFourfoldRows spectrum liveScale target) arity
                factors : ℚ) : ℝ)|
          + |((rowSupplier (symmetricFourfoldRows spectrum liveScale target) arity
                factors : ℚ) : ℝ)
            - conjunctionProbability NormalizedSymmetricThresholdCircuit.eval factors| :=
        abs_sub_le _ _ _
    _ ≤ (1 : ℝ) / ((target arity + 1 : ℕ) : ℝ)
        + 1 / ((denominator arity scale : ℕ) : ℝ) := by
        have : (1 : ℝ) / ((target (⟨arity, factors⟩ :
            FourfoldRequest NormalizedSymmetricThresholdCircuit).q + 1 : ℕ) : ℝ)
            = (1 : ℝ) / ((target arity + 1 : ℕ) : ℝ) := rfl
        rw [this] at hpt
        linarith

/-- **`hcount`.**  The rescaled count never reaches the bank's word bound — with
no side condition, because the floor is at most the uniform denominator. -/
theorem answer_lt {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate)
    (coefficientFloor arity scale : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) (n : ℕ)
    (factors : List (Circuit (arity n))) :
    answer rows (arity n) (scale n) factors
      < 2 ^ entryWidth coefficientFloor arity scale constants n := by
  have hR : 0 < rowDenominator rows (arity n) factors :=
    rowDenominator_pos rows (arity n) factors
  have hle : answer rows (arity n) (scale n) factors ≤ denominator (arity n) (scale n) := by
    unfold answer
    calc rowAnswer rows (arity n) factors * denominator (arity n) (scale n)
            / rowDenominator rows (arity n) factors
        ≤ rowDenominator rows (arity n) factors * denominator (arity n) (scale n)
            / rowDenominator rows (arity n) factors :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _
            (rowAnswer_le_rowDenominator rows (arity n) factors))
      _ = denominator (arity n) (scale n) := Nat.mul_div_cancel_left _ hR
  refine lt_of_le_of_lt hle ?_
  refine lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num)
    (Nat.lt_succ_self (arity n + scale n))) ?_
  exact Nat.pow_le_pow_right (by norm_num)
    ((entryWidth_floor_answer coefficientFloor arity scale constants n))

/-- **`hdenominator`.**  The uniform denominator fits the same word. -/
theorem denominator_lt (coefficientFloor arity scale : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) (n : ℕ) :
    denominator (arity n) (scale n)
      < 2 ^ entryWidth coefficientFloor arity scale constants n := by
  refine lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num)
    (Nat.lt_succ_self (arity n + scale n))) ?_
  exact Nat.pow_le_pow_right (by norm_num)
    ((entryWidth_floor_answer coefficientFloor arity scale constants n))

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
