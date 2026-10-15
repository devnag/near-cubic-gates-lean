import Proof.CaseAnalysis.FinalModeNativeStageFields
import Proof.CaseAnalysis.FinalPrimeWindow

/-!
Native-mode denominator bounds, from admitted wire and description envelopes.
The THR denominator counts primes and walk seeds, never child labels. One
native request has one occurrence pool. All stage bounds retain membership.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope

open NearCubicWires NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parityDescCap (q : ℕ) : ℕ := thresholdDescriptionCap q q

/-- Reuse the existing normalized-circuit bound on the actual native parity.
This is the short F2 proof at the C10 circuit, without importing the F2 graph. -/
theorem nativeThresholdParity_description {q : ℕ} (support : Finset (Fin q)) :
    (CloseoutRowsEstimatorParity.normalizedThresholdParityCircuit support).descriptionBits ≤
      parityDescCap q := by
  have hcard : support.card ≤ q := by simpa using Finset.card_le_univ support
  apply normalizedThreshold_descriptionBits_le
  · exact hcard
  · intro index
    have hi : index.val < support.card := index.isLt
    have hq : 0 < q := by omega
    have hpow : q ≤ q ^ q := by
      calc q = q ^ 1 := by simp
        _ ≤ q ^ q := Nat.pow_le_pow_right hq (by omega)
    constructor
    · intro coordinate
      change (if coordinate ∈ support then (1 : ℤ) else 0).natAbs ≤ q ^ q
      split <;> norm_num
      exact (by omega)
    · change index.val + 1 ≤ q ^ q
      exact ((Nat.succ_le_iff.mpr index.isLt).trans hcard).trans hpow
  · have hone : 1 ≤ support.card ^ support.card := by
      by_cases hz : support.card = 0
      · simp [hz]
      · have hp := Nat.pow_pos (Nat.pos_of_ne_zero hz) (n := support.card)
        omega
    constructor
    · intro index
      change (if Even index.val then (1 : ℤ) else -1).natAbs ≤ support.card ^ support.card
      split <;> norm_num
      all_goals exact hone
    · change (1 : ℤ).natAbs ≤ support.card ^ support.card
      norm_num
      exact hone

private theorem population_le {Circuit Gate : Type} (occ : Circuit → List Gate)
    (circuits : List Circuit) (wireCap : ℕ)
    (h : ∀ circuit ∈ circuits, (occ circuit).length ≤ wireCap) :
    (circuits.flatMap occ).length ≤ circuits.length * wireCap := by
  induction circuits with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
    have ht := ih (fun circuit hc => h circuit (by simp [hc]))
    have hh := h head (by simp)
    omega

def symSeedBits (wireCap target : ℕ) : ℕ :=
  seedEnvelope (4 * wireCap) (4 * wireCap) (4 * (target + 1))

def thrSeedBits (a : DecompositionAlgorithm) (wireCap descCap target : ℕ) : ℕ :=
  Nat.clog 2 (tupleCutoffBound a descCap target + 1) +
    seedEnvelope (4 * wireCap) (4 * wireCap) (tupleListDenominatorBound a descCap target)

variable (sources : EightSources) (liveScale target : ℕ)

theorem symmetric_den_le (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (wireCap : ℕ) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ circuit ∈ r.circuits, circuit.wireCount ≤ wireCap) :
    (symmetricEstimate sources liveScale target r).den ≤
      2 ^ (r.q + symSeedBits wireCap target) := by
  have hpop : (symmetricFourfoldOccurrences r).length ≤ 4 * wireCap :=
    (population_le symmetricCircuitOccurrences r.circuits wireCap
      (fun circuit hc => (symmetricCircuitOccurrences_length_le circuit).trans
        (hw circuit hc))).trans (Nat.mul_le_mul_right wireCap hfour)
  have hseed : seedExponent r liveScale target ≤ symSeedBits wireCap target := by
    unfold seedExponent symSeedBits
    exact walkExponent_le_seedEnvelope hpop
      ((touchingCost_le_length _ _).trans hpop)
      (Nat.mul_le_mul_right (target + 1) hfour)
  change rowDenominator _ r.q r.circuits ≤ _
  rw [rowDenominator, rowCount_eq_two_pow, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  change seedExponent r liveScale target + r.q ≤ _
  omega

theorem threshold_den_le (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (wireCap descCap : ℕ) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ circuit ∈ r.circuits, circuit.wireCount ≤ wireCap)
    (hd : ∀ circuit ∈ r.circuits, circuit.descriptionBits ≤ descCap) :
    (thresholdEstimate sources liveScale target r).den ≤
      2 ^ (r.q + thrSeedBits (decompositionOf sources) wireCap descCap target) := by
  have hpop : (thresholdFourfoldOccurrences r).length ≤ 4 * wireCap :=
    (population_le thresholdCircuitOccurrences r.circuits wireCap
      (fun circuit hc => (thresholdCircuitOccurrences_length_le circuit).trans
        (hw circuit hc))).trans (Nat.mul_le_mul_right wireCap hfour)
  have hp : Fintype.card (PrimeIndex (primeCutoff (decompositionOf sources) r target)) ≤
      2 ^ Nat.clog 2 (tupleCutoffBound (decompositionOf sources) descCap target + 1) := by
    rw [Fintype.card_coe]
    exact (primesUpTo_primeCutoff_card_le _ r descCap target hfour hd).trans
      (Nat.le_pow_clog (by decide) _)
  have hs : Fintype.card (NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale
      (listDenominator (decompositionOf sources) r target)) ≤
      2 ^ seedEnvelope (4 * wireCap) (4 * wireCap)
        (tupleListDenominatorBound (decompositionOf sources) descCap target) := by
    rw [card_walkSample]
    exact Nat.pow_le_pow_right (by decide)
      (walkExponent_le_seedEnvelope hpop ((touchingCost_le_length _ _).trans hpop)
        (listDenominator_le _ r descCap target hfour hd))
  change _ * _ * 2 ^ r.q ≤ _
  apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul hp hs)).trans_eq
  unfold thrSeedBits
  rw [← pow_add, ← pow_add, Nat.add_comm]

/-- Only carried THR descriptions enter the prime/list bound. -/
def CarriedDescription {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (cap : ℕ) : Atom pcpp → Prop
  | .threshold atom => atom.descriptionBits ≤ cap
  | _ => True

theorem familyCoordinate_description {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ} {limits : LegalSumLimits}
    {variableCount arity : ℕ} (harity : limits.expectedArity = arity)
    (family : SumFamily Circuit wires description limits variableCount) (i : Fin variableCount) :
    (familyCoordinate harity family i).FactorsSatisfy
      (fun circuit => description circuit ≤ limits.descriptionCap) := by
  unfold familyCoordinate
  refine linearPolynomial_factorsSatisfy _ _ ?_
  intro term hterm
  exact wires_le_of_mem_transportTerms description _ (family.getSum i).value.terms
    limits.descriptionCap (family.getSum i).description_le term hterm

variable (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- The exact decoder's existing THR description cap, evaluated at canonical
input/oracle values; its value depends only on their arities. -/
def carriedDescCap (n : ℕ) : ℕ :=
  (thrLimits sources k (PolynomialClock.ordinaryClock k) p (fun _ : Fin n => false)
    (trivialCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n))).descriptionCap

theorem actual_carried_description {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)) :
    (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
      Atom.systematic address).FactorsSatisfy (CarriedDescription (carriedDescCap sources k p n)) := by
  apply siteCalls_factorsSatisfy
  · intro j
    change (decodeCoordinate sources k (PolynomialClock.ordinaryClock k) p x
      (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits j).FactorsSatisfy _
    by_cases hs : BoundedFields.symmetric bits = true
    · rw [decodeCoordinate_sym sources k (PolynomialClock.ordinaryClock k) p x
        (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits hs j]
      refine mapPolynomial_factorsSatisfy _ _ _ ?_
      intro monomial hmonomial atom hatom
      trivial
    · rw [decodeCoordinate_thr sources k (PolynomialClock.ordinaryClock k) p x
        (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits hs j]
      refine mapPolynomial_factorsSatisfy _ _ _ ?_
      exact familyCoordinate_description rfl
        (thrFamilyOf sources k (PolynomialClock.ordinaryClock k) p x
          (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) j
  · intro j
    trivial

def nativeWireCap (n : ℕ) : ℕ :=
  max (stageArity sources k n * (stageArity sources k n + 1)) (envelopeCap sources k n)

def nativeDescCap (n : ℕ) : ℕ :=
  max (parityDescCap (stageArity sources k n)) (carriedDescCap sources k p n)

theorem nativeSymmetric_wire {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atom : Atom pcpp) (hmode : ModeAtom true atom) :
    (nativeSymmetricAtom atom).wireCount = atomWires atom := by
  cases atom with
  | systematic _ => rfl
  | symmetric _ => rfl
  | threshold _ => cases hmode

theorem nativeThreshold_wire {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atom : Atom pcpp) (hmode : ModeAtom false atom) (cap : ℕ) (hw : atomWires atom ≤ cap) :
    (nativeThresholdAtom atom).wireCount ≤ max (q * (q + 1)) cap := by
  cases atom with
  | systematic index => exact (nativeThresholdParity_wires_le _).trans (le_max_left _ _)
  | threshold atom => exact hw.trans (le_max_right _ _)
  | symmetric _ => cases hmode

theorem nativeThreshold_description {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atom : Atom pcpp) (hmode : ModeAtom false atom) (cap : ℕ)
    (hd : CarriedDescription cap atom) :
    (nativeThresholdAtom atom).descriptionBits ≤ max (parityDescCap q) cap := by
  cases atom with
  | systematic index => exact (nativeThresholdParity_description _).trans (le_max_left _ _)
  | threshold atom => exact hd.trans (le_max_right _ _)
  | symmetric _ => cases hmode

/-- The selected class takes the maximum of its two alternative seed bounds;
these are alternatives, not a product of separately split row populations. -/
def nativeDenBits (n : ℕ) : ℕ :=
  stageArity sources k n +
    max (symSeedBits (nativeWireCap sources k n) (stageTarget sources p (stageArity sources k n)))
      (thrSeedBits (decompositionOf sources) (nativeWireCap sources k n)
        (nativeDescCap sources k p n) (stageTarget sources p (stageArity sources k n)))

/-- The actual selected denominator bound has no remaining wire/description premise:
the decoder owns carried caps and native parity owns its explicit polynomial cap. -/
theorem stage_den_le {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hmem : monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
      (stageCoordinate sources k p n x bits) Atom.systematic address).monomials) :
    (stageEstimate sources liveScale k p n x bits monomial.factors).den ≤
      2 ^ nativeDenBits sources k p n := by
  have hn := congrArg Prod.snd (stageEstimate_native sources liveScale k p x bits ph address
    monomial hmem)
  have hm := actual_site_mode sources k p x bits ph address monomial hmem
  have hw := henv_at_envelopeCap sources k p n x bits ph address monomial hmem
  have hd := actual_carried_description sources k p x bits ph address monomial hmem
  have hfourS : (monomial.factors.map nativeSymmetricAtom).length ≤ 4 := by
    rw [List.length_map]
    exact monomial.degree_le
  have hfourT : (monomial.factors.map nativeThresholdAtom).length ≤ 4 := by
    rw [List.length_map]
    exact monomial.degree_le
  cases hs : BoundedFields.symmetric bits
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hn
    rw [hs] at hm
    rw [hn]
    have hbound := threshold_den_le sources liveScale (stageTarget sources p (stageArity sources k n))
      ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
      (nativeWireCap sources k n) (nativeDescCap sources k p n) hfourT
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        exact nativeThreshold_wire atom (hm atom ha) _ (hw atom ha))
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        exact nativeThreshold_description atom (hm atom ha) _ (hd atom ha))
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_right _ _) _))
  · simp only [hs, ↓reduceIte] at hn
    rw [hs] at hm
    rw [hn]
    have hbound := symmetric_den_le sources liveScale (stageTarget sources p (stageArity sources k n))
      ⟨stageArity sources k n, monomial.factors.map nativeSymmetricAtom⟩
      (nativeWireCap sources k n) hfourS
      (by
        intro circuit hc
        obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hc
        rw [nativeSymmetric_wire atom (hm atom ha)]
        exact (hw atom ha).trans (le_max_right _ _))
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_left _ _) _))

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
