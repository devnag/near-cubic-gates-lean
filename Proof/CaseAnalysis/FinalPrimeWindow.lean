import Proof.CaseAnalysis.FinalWireEnvelope
import Proof.CaseAnalysis.RawRowsThresholdAccuracy

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (primeCutoff primeDenominator
  listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf decompositionOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutRawRows (sourceChildBound sourceChildBound_polynomial
  thresholdMagnitudeExponent thresholdMagnitudeExponent_polynomial selection_count
  canonical_stack_magnitude top_child_magnitude descriptionEnvelope
  descriptionEnvelope_polynomial thresholdFamilyBound thresholdPrimeDen thresholdCutoff
  thresholdListDen threshold_parameters_polynomial primeCutoff_polynomial)
open NearCubicWires.RepairSource.CloseoutWitnessResources (bits_polynomial)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo equationMagnitudeBound familyMagnitudeBound
  familyMagnitudeExponent canonicalPrimeScale canonicalPrimeCutoff)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The per-atom DESCRIPTION envelope, as a number

`paper.tex:4292-4302`'s rejection rule lists FOUR caps -- "exceeds its declared
term, coefficient-bit, coefficient-mass, or per-atom wire envelope" -- and
`CheckedLegalCircuitSum` (`Proof/Circuits/CanonicalWitnessCodec.lean`) carries
all of them, `wires_le` (`:1561`) and `description_le` (`:1563`) side by side.
`atomWires` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) is the Lean quantity
for the wire cap; `atomDescription` below is its exact sibling for the
description cap, charged through the SAME `atomToUnion`
(`Proof/CaseAnalysis/FinalUnionSupplier.lean`) so the systematic constructor
is charged for the native parity circuit it compiles into and nothing is charged
twice. -/

/-- The description-bit count of a decode-union circuit, either branch. -/
def unionDescription {N : ℕ} : DecodeUnion N → ℕ
  | Sum.inl circuit => circuit.descriptionBits
  | Sum.inr circuit => circuit.descriptionBits

/-- **The per-atom description envelope.**  `Proof/CaseAnalysis/FinalTotalDecode.lean`
instantiates `SumFamily`'s `description` parameter at
`NormalizedThresholdThresholdCircuit.descriptionBits`
(`Proof/Foundations/SupplierPipeline.lean`), so on the threshold branch this is
literally the number the decoder's `description_le` bounds. -/
def atomDescription {N : ℕ} {circuit : BooleanCircuit N} {pcpp : PointwisePCPP circuit}
    (atom : Atom pcpp) : ℕ :=
  unionDescription (atomToUnion atom)

/-- Every right-branch circuit of a mixed list came from a `Sum.inr` member. -/
theorem mem_of_mem_rightCircuits {N : ℕ} (c : NormalizedThresholdThresholdCircuit N) :
    ∀ us : List (DecodeUnion N), c ∈ rightCircuits us →
      (Sum.inr c : DecodeUnion N) ∈ us := by
  intro us
  induction us with
  | nil => intro h; simp [rightCircuits] at h
  | cons u rest ih =>
      intro h
      cases u with
      | inl circuit =>
          exact List.mem_cons_of_mem _ (ih (by simpa [rightCircuits] using h))
      | inr d =>
          have h' : c ∈ d :: rightCircuits rest := h
          rcases List.mem_cons.mp h' with hrfl | hmem
          · subst hrfl
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih hmem)

/-- `2 ^ K * 2 ^ M` and one more fits in `2 ^ (K + M + 1)`, so a total bounded by
`count * 2 ^ M` with `count ≤ 2 ^ K` has `clog`-successor at most `K + M + 1`. -/
private theorem clog_succ_le (total count K M : ℕ) (hcount : count ≤ 2 ^ K)
    (htotal : total ≤ count * 2 ^ M) :
    Nat.clog 2 (total + 1) ≤ K + M + 1 := by
  have h1 : total ≤ 2 ^ K * 2 ^ M :=
    htotal.trans (Nat.mul_le_mul_right _ hcount)
  have hpos : (1 : ℕ) ≤ 2 ^ K * 2 ^ M := by
    rw [← pow_add]
    exact Nat.one_le_two_pow
  have hrw : (2 : ℕ) ^ (K + M + 1) = 2 ^ K * 2 ^ M + 2 ^ K * 2 ^ M := by
    rw [pow_succ, pow_add]
    ring
  have h2 : total + 1 ≤ 2 ^ (K + M + 1) := by
    rw [hrw]
    exact Nat.add_le_add h1 hpos
  calc Nat.clog 2 (total + 1) ≤ Nat.clog 2 (2 ^ (K + M + 1)) := Nat.clog_mono_right 2 h2
    _ = K + M + 1 := Nat.clog_pow 2 _ (by norm_num)

/-- **One child tuple's stacked equation has bounded magnitude.**  This is
`actual_threshold_difference` (`Proof/CaseAnalysis/RawRowsThresholdSize.lean`)
stopped one step earlier: at the MAGNITUDE BOUND rather than at one
difference, because `familyMagnitudeBound` sums the bound, not the difference. -/
theorem equation_magnitudeBound_lt (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc)
    (sel : ThresholdRows.Selection a r) :
    equationMagnitudeBound (ThresholdRows.equation a r sel) <
      2 ^ thresholdMagnitudeExponent a desc := by
  apply canonical_stack_magnitude (ThresholdRows.equations a r sel) (sourceChildBound a desc)
  · simpa only [ThresholdRows.equations, List.length_ofFn] using hfour
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rw [thresholdChildEquation_magnitudeBound]
    exact top_child_magnitude a _ desc (hd _ (List.get_mem _ _)) (sel i)

/-- The family magnitude exponent's envelope: `4 c_0` bits of tuple count on top
of the per-tuple magnitude exponent, plus one. -/
def tupleExponentBound (a : DecompositionAlgorithm) (desc : ℕ) : ℕ :=
  4 * Nat.clog 2 (sourceChildBound a desc + 1) + thresholdMagnitudeExponent a desc + 1

/-- **THE GAP, CLOSED.**  `familyMagnitudeExponent` at the child-tuple family is
bounded by a closed form in the source child bound alone. -/
theorem familyMagnitudeExponent_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    familyMagnitudeExponent (ThresholdRows.equation a r) ≤ tupleExponentBound a desc := by
  classical
  have hcard : Fintype.card (ThresholdRows.Selection a r) ≤
      2 ^ (4 * Nat.clog 2 (sourceChildBound a desc + 1)) := by
    refine (selection_count a r desc hfour hd).trans ?_
    calc (sourceChildBound a desc + 1) ^ 4
        ≤ (2 ^ Nat.clog 2 (sourceChildBound a desc + 1)) ^ 4 :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) 4
      _ = 2 ^ (4 * Nat.clog 2 (sourceChildBound a desc + 1)) := by
          rw [← pow_mul, Nat.mul_comm]
  have hterm : ∀ sel ∈ (Finset.univ : Finset (ThresholdRows.Selection a r)),
      equationMagnitudeBound (ThresholdRows.equation a r sel) ≤
        2 ^ thresholdMagnitudeExponent a desc :=
    fun sel _ => (equation_magnitudeBound_lt a r desc hfour hd sel).le
  have hsum : familyMagnitudeBound (ThresholdRows.equation a r) ≤
      Fintype.card (ThresholdRows.Selection a r) * 2 ^ thresholdMagnitudeExponent a desc := by
    have hle := Finset.sum_le_card_nsmul (Finset.univ : Finset (ThresholdRows.Selection a r))
      (fun sel => equationMagnitudeBound (ThresholdRows.equation a r sel))
      (2 ^ thresholdMagnitudeExponent a desc) hterm
    simpa [familyMagnitudeBound, Finset.card_univ, smul_eq_mul] using hle
  exact clog_succ_le _ _ _ _ hcard hsum

/-! ## §3 The prime window and the list denominator, in closed form

`canonicalPrimeCutoff` (`Proof/Foundations/SupplierPrime.lean`) is monotone in both
arguments and `reciprocalUnionDenominator`
(`Proof/Supplier/SupplierEstimator.lean`) is monotone in the family size, so §2
plus `selection_count` bound the cutoff, and `primesUpTo_card_le`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) turns that into the window's
cardinality.  `listDenominator` (`Proof/CaseAnalysis/FinalThresholdRows.lean`)
is `modulusDigitCount (primeCutoff …) * (primeDenominator … + 1)`, so it falls
out of the SAME two bounds -- which is why `hprime` and `hthrden` are one
obligation and not two. -/

theorem canonicalPrimeCutoff_mono {e e' d d' : ℕ} (he : e ≤ e') (hd : d ≤ d') :
    canonicalPrimeCutoff e d ≤ canonicalPrimeCutoff e' d' := by
  unfold canonicalPrimeCutoff canonicalPrimeScale
  exact Nat.pow_le_pow_left
    (max_le_max le_rfl
      (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.succ_le_succ he)) (Nat.succ_le_succ hd))) 2

theorem reciprocalUnionDenominator_mono {f f' t : ℕ} (h : f ≤ f') :
    reciprocalUnionDenominator f t ≤ reciprocalUnionDenominator f' t := by
  unfold reciprocalUnionDenominator
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl h) le_rfl

theorem modulusDigitCount_mono {m m' : ℕ} (h : m ≤ m') :
    modulusDigitCount m ≤ modulusDigitCount m' :=
  Nat.succ_le_succ (Nat.log_mono_right h)

def tupleCutoffBound (a : DecompositionAlgorithm) (desc target : ℕ) : ℕ :=
  canonicalPrimeCutoff (tupleExponentBound a desc) (thresholdPrimeDen a desc target)

def tupleListDenominatorBound (a : DecompositionAlgorithm) (desc target : ℕ) : ℕ :=
  modulusDigitCount (tupleCutoffBound a desc target) * (thresholdPrimeDen a desc target + 1)

theorem primeDenominator_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    primeDenominator a r target ≤ thresholdPrimeDen a desc target :=
  reciprocalUnionDenominator_mono (selection_count a r desc hfour hd)

theorem primeCutoff_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    primeCutoff a r target ≤ tupleCutoffBound a desc target :=
  canonicalPrimeCutoff_mono (familyMagnitudeExponent_le a r desc hfour hd)
    (primeDenominator_le a r desc target hfour hd)

/-- **`hprime`'S CONTENT, AT ONE REQUEST.**  The prime window is bounded by the
child-tuple envelope. -/
theorem primesUpTo_primeCutoff_card_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    (primesUpTo (primeCutoff a r target)).card ≤ tupleCutoffBound a desc target + 1 :=
  (primesUpTo_card_le _).trans (Nat.succ_le_succ (primeCutoff_le a r desc target hfour hd))

/-- **`hthrden`'S CONTENT, AT ONE REQUEST.** -/
theorem listDenominator_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    listDenominator a r target ≤ tupleListDenominatorBound a desc target :=
  Nat.mul_le_mul (modulusDigitCount_mono (primeCutoff_le a r desc target hfour hd))
    (Nat.succ_le_succ (primeDenominator_le a r desc target hfour hd))

/-! ## §4 The request at one monomial

`unionRequestOf` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) is
`⟨stageArity …, monomial.factors.map atomToUnion⟩`, so the threshold request
`rightRequest (unionRequestOf …)` has exactly the monomial's threshold atoms as
its circuits.  `hfour` is then `CircuitMonomial.degree_le` and the description
cap transports through `atomToUnion` unchanged. -/

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

theorem rightRequest_circuits_length_le {n : ℕ} (x : BitInput n) (bits : List Bool)
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4) :
    (rightRequest (unionRequestOf sources k p x bits monomial)).circuits.length ≤ 4 := by
  refine le_trans (rightCircuits_length_le _) ?_
  simp only [unionRequestOf, List.length_map]
  exact monomial.degree_le

theorem rightRequest_descriptionBits_le {n : ℕ} (x : BitInput n) (bits : List Bool)
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4) (cap : ℕ)
    (hdesc : ∀ atom ∈ monomial.factors, atomDescription atom ≤ cap) :
    ∀ c ∈ (rightRequest (unionRequestOf sources k p x bits monomial)).circuits,
      c.descriptionBits ≤ cap := by
  have hus : ∀ u ∈ (unionRequestOf sources k p x bits monomial).circuits,
      unionDescription u ≤ cap := by
    intro u hu
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hu
    exact hdesc atom hatom
  intro c hc
  exact hus (Sum.inr c) (mem_of_mem_rightCircuits c _ hc)

/-! ## §5 `hprime` and `hthrden`, at A.8's two summands

`stageSeedEnvelope` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) spends
exactly two numbers on the threshold branch: `primeBits n` (A.8's "primes") and
`thrDenBound n` (A.8's "stacked-equation labels").  §5 names both, as functions
of a per-atom DESCRIPTION cap, and discharges the two binders. -/

/-- A.8:2253's "primes" summand: the bit budget of the prime window. -/
def stagePrimeBits (descCap : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.clog 2 (tupleCutoffBound (decompositionOf sources) (descCap n)
    (unionTarget (stageTarget sources p) (stageArity sources k n)) + 1)

/-- A.8:2253's "stacked-equation labels" summand. -/
def stageThrDenBound (descCap : ℕ → ℕ) (n : ℕ) : ℕ :=
  tupleListDenominatorBound (decompositionOf sources) (descCap n)
    (unionTarget (stageTarget sources p) (stageArity sources k n))

/-- **`hprime`, DISCHARGED from the per-atom description envelope.** -/
theorem hprime_of_descriptions (descCap : ℕ → ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hdesc : ∀ atom ∈ monomial.factors, atomDescription atom ≤ descCap n) :
    (primesUpTo (primeCutoff (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)))).card ≤
      2 ^ stagePrimeBits sources k p descCap n := by
  refine le_trans (primesUpTo_primeCutoff_card_le _ _ (descCap n) _
    (rightRequest_circuits_length_le sources k p x bits monomial)
    (rightRequest_descriptionBits_le sources k p x bits monomial (descCap n) hdesc)) ?_
  unfold stagePrimeBits
  exact Nat.le_pow_clog (by norm_num) _

/-- **`hthrden`, DISCHARGED from the per-atom description envelope.** -/
theorem hthrden_of_descriptions (descCap : ℕ → ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hdesc : ∀ atom ∈ monomial.factors, atomDescription atom ≤ descCap n) :
    listDenominator (decompositionOf sources)
      (rightRequest (unionRequestOf sources k p x bits monomial))
      (unionTarget (stageTarget sources p) (stageArity sources k n)) ≤
      stageThrDenBound sources k p descCap n :=
  listDenominator_le _ _ (descCap n) _
    (rightRequest_circuits_length_le sources k p x bits monomial)
    (rightRequest_descriptionBits_le sources k p x bits monomial (descCap n) hdesc)

theorem siteDenFits_of_envelopes (liveScale : ℕ)
    (coefficientFloor wireCap descCap : ℕ → ℕ)
    (hfloor : ∀ n, stageArity sources k n +
      stageSeedEnvelope sources k p wireCap (stagePrimeBits sources k p descCap)
        (stageThrDenBound sources k p descCap) n + 1 ≤
      stageEntryWidth sources k p coefficientFloor n)
    (henv : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase)
      (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
      ∀ atom ∈ monomial.factors, atomWires atom ≤ wireCap n)
    (hdesc : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase)
      (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
      (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
      ∀ atom ∈ monomial.factors, atomDescription atom ≤ descCap n) :
    SiteDenFits sources k p liveScale coefficientFloor :=
  fun n x bits _hn ph address monomial hmonomial =>
    stageDen_lt_of_wireEnvelope sources k p liveScale coefficientFloor wireCap
      (stagePrimeBits sources k p descCap) (stageThrDenBound sources k p descCap)
      hfloor x bits address monomial
      (henv n x bits ph address monomial hmonomial)
      (hprime_of_descriptions sources k p descCap x bits monomial
        (hdesc n x bits ph address monomial hmonomial))
      (hthrden_of_descriptions sources k p descCap x bits monomial
        (hdesc n x bits ph address monomial hmonomial))

/-- **Anti-vacuity receipt.**  The description premise has witnesses at every
cap, so §5 is not vacuous. -/
theorem description_satisfiable {n : ℕ} {x : BitInput n} {bits : List Bool} (cap : ℕ) :
    ∃ monomial : CircuitMonomial (Atoms sources k p x bits) 4,
      ∀ atom ∈ monomial.factors, atomDescription atom ≤ cap :=
  ⟨⟨1, [], by simp⟩, by simp⟩

/-- **`hfloor` is still FREE.**  `envelopeFloor`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) at §5's two caps discharges the
composer's `hfloor` binder with no new obligation. -/
theorem hfloor_at_envelopeFloor_descriptions (wireCap descCap : ℕ → ℕ) (n : ℕ) :
    stageArity sources k n +
      stageSeedEnvelope sources k p wireCap (stagePrimeBits sources k p descCap)
        (stageThrDenBound sources k p descCap) n + 1 ≤
      stageEntryWidth sources k p (envelopeFloor sources k p wireCap
        (stagePrimeBits sources k p descCap) (stageThrDenBound sources k p descCap)) n :=
  hfloor_at_envelopeFloor sources k p wireCap (stagePrimeBits sources k p descCap)
    (stageThrDenBound sources k p descCap) n

/-- The canonical prime cutoff is at most a fixed power of two in the BIT
LENGTHS of its two arguments.  Stated on raw naturals so the stage terms never
enter the arithmetic. -/
private theorem canonicalPrimeCutoff_le_two_pow (e d eb db : ℕ)
    (he : e + 1 ≤ 2 ^ eb) (hd : d + 1 ≤ 2 ^ db) :
    canonicalPrimeCutoff e d + 1 ≤ 2 ^ (2 * (eb + db + 8) + 1) := by
  have hscale : canonicalPrimeScale e d ≤ 2 ^ (eb + db + 8) := by
    unfold canonicalPrimeScale
    refine max_le ?_ ?_
    · calc (24 : ℕ) ≤ 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (eb + db + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · calc 6 * (e + 1) * (d + 1) ≤ 2 ^ 3 * 2 ^ eb * 2 ^ db :=
            Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) he) hd
        _ = 2 ^ (eb + db + 3) := by
            rw [show eb + db + 3 = 3 + eb + db by omega, pow_add, pow_add]
        _ ≤ 2 ^ (eb + db + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcut : canonicalPrimeCutoff e d ≤ 2 ^ (2 * (eb + db + 8)) := by
    unfold canonicalPrimeCutoff
    calc canonicalPrimeScale e d ^ 2 ≤ (2 ^ (eb + db + 8)) ^ 2 :=
          Nat.pow_le_pow_left hscale 2
      _ = 2 ^ (2 * (eb + db + 8)) := by rw [← pow_mul, Nat.mul_comm]
  have hone : (1 : ℕ) ≤ 2 ^ (2 * (eb + db + 8)) := Nat.one_le_two_pow
  have hrw : (2 : ℕ) ^ (2 * (eb + db + 8) + 1) =
      2 ^ (2 * (eb + db + 8)) + 2 ^ (2 * (eb + db + 8)) := by
    rw [pow_succ]
    ring
  rw [hrw]
  exact Nat.add_le_add hcut hone

/-- The list denominator's `clog` is linear in the same two bit lengths.
Stated on raw naturals for the same reason. -/
private theorem listDenominator_clog_le (cut den eb db : ℕ)
    (hcut : cut + 1 ≤ 2 ^ (2 * (eb + db + 8) + 1)) (hden : den + 1 ≤ 2 ^ db) :
    Nat.clog 2 (modulusDigitCount cut * (den + 1) + 1) ≤ 2 * (eb + db + 8) + db + 3 := by
  have hlog : Nat.log 2 cut ≤ 2 * (eb + db + 8) + 1 := by
    have hmono := Nat.log_mono_right (b := 2)
      (show cut ≤ 2 ^ (2 * (eb + db + 8) + 1) by omega)
    rwa [Nat.log_pow (by norm_num)] at hmono
  have hdigits : modulusDigitCount cut ≤ 2 * (eb + db + 8) + 2 := by
    unfold modulusDigitCount
    omega
  have hpow : modulusDigitCount cut ≤ 2 ^ (2 * (eb + db + 8) + 2) :=
    hdigits.trans (le_of_lt Nat.lt_two_pow_self)
  have hfinal := clog_succ_le (modulusDigitCount cut * (den + 1)) (modulusDigitCount cut)
    (2 * (eb + db + 8) + 2) db hpow (Nat.mul_le_mul le_rfl hden)
  omega

/-- **RESOURCE RECEIPT, prime window.**  A.8's "primes" summand is a fixed
LINEAR function of the BIT LENGTHS of the family magnitude exponent and the
requested reciprocal accuracy -- never of the quantities themselves. -/
theorem stagePrimeBits_le_of_bits (descCap : ℕ → ℕ) (n expBits denBits : ℕ)
    (hexp : tupleExponentBound (decompositionOf sources) (descCap n) + 1 ≤ 2 ^ expBits)
    (hden : thresholdPrimeDen (decompositionOf sources) (descCap n)
      (unionTarget (stageTarget sources p) (stageArity sources k n)) + 1 ≤ 2 ^ denBits) :
    stagePrimeBits sources k p descCap n ≤ 2 * (expBits + denBits + 8) + 1 := by
  unfold stagePrimeBits tupleCutoffBound
  refine le_trans (Nat.clog_mono_right 2
    (canonicalPrimeCutoff_le_two_pow _ _ expBits denBits hexp hden)) ?_
  exact le_of_eq (Nat.clog_pow 2 _ (by norm_num))

/-- **RESOURCE RECEIPT, stacked-equation labels.**  A.8's second threshold
summand enters `stageSeedEnvelope` only through `Nat.clog 2 (· + 1)`, and that
`clog` is a fixed LINEAR function of the same two bit lengths.  So the list
denominator itself may be polynomial -- it is -- while its CONTRIBUTION stays
polylog, which is the whole content of A.8's "logarithm of the number of
external rows". -/
theorem stageThrDenBound_bits_le_of_bits (descCap : ℕ → ℕ) (n expBits denBits : ℕ)
    (hexp : tupleExponentBound (decompositionOf sources) (descCap n) + 1 ≤ 2 ^ expBits)
    (hden : thresholdPrimeDen (decompositionOf sources) (descCap n)
      (unionTarget (stageTarget sources p) (stageArity sources k n)) + 1 ≤ 2 ^ denBits) :
    Nat.clog 2 (stageThrDenBound sources k p descCap n + 1) ≤
      2 * (expBits + denBits + 8) + denBits + 3 := by
  unfold stageThrDenBound tupleListDenominatorBound tupleCutoffBound
  exact listDenominator_clog_le _ _ expBits denBits
    (canonicalPrimeCutoff_le_two_pow _ _ expBits denBits hexp hden) hden

-- the three `private` arithmetic cores, by their in-file names

theorem tupleExponentBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (fun q => tupleExponentBound a (descriptionEnvelope degree q)) := by
  refine polynomiallyBounded_mono (fun q => ?_)
    (polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
          (sourceChildBound_polynomial a (descriptionEnvelope_polynomial degree)))
        (thresholdMagnitudeExponent_polynomial a degree))
      (polynomiallyBounded_constant 1))
  have hclog : Nat.clog 2 (sourceChildBound a (descriptionEnvelope degree q) + 1) ≤
      sourceChildBound a (descriptionEnvelope degree q) :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  unfold tupleExponentBound
  omega

/-- **The prime window is polynomial**, at the cutoff `primeCutoff` actually
uses -- which `threshold_parameters_polynomial` does not cover. -/
theorem tupleCutoffBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded
      (fun q => tupleCutoffBound a (descriptionEnvelope degree q) (target q)) :=
  primeCutoff_polynomial (tupleExponentBound_polynomial a degree)
    (threshold_parameters_polynomial a degree target ht).1

/-- **The stacked-equation list denominator is polynomial**, at the same cutoff. -/
theorem tupleListDenominatorBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded
      (fun q => tupleListDenominatorBound a (descriptionEnvelope degree q) (target q)) :=
  polynomiallyBounded_mul (bits_polynomial (tupleCutoffBound_polynomial a degree target ht))
    (polynomiallyBounded_add (threshold_parameters_polynomial a degree target ht).1
      (polynomiallyBounded_constant 1))

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
