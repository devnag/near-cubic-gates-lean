import Proof.SourceAssembly.AdmissionLayout
import Proof.CaseAnalysis.FiveRowKeys
import Proof.CaseAnalysis.FinalSupplierWidth

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalk
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  sourceChildBound sourceChildBound_polynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow (tupleCutoffBound
  tupleListDenominatorBound primeCutoff_le listDenominator_le
  tupleCutoffBound_polynomial tupleListDenominatorBound_polynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope (seedEnvelope seedEnvelope_le_of_bits
  walkExponent_le_seedEnvelope touchingCost_le_length primesUpTo_card_le)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (walkExponent card_walkSample)
open FixedLivePackets PacketProduction

noncomputable section

/-! ## 1. The admitted runtime request -/

/-- `Admitted` at the runtime `Request`: every native circuit inside the carried wire envelope and the
description envelope, and the source's fixed accuracy target. The terminal sentinel carries nothing. -/
def RequestAdmitted (den degree target : ℕ) : Request → Prop
  | .terminal => True
  | .sym r _ _ t => t = target ∧ ∀ c ∈ r.circuits,
      c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 5 r.q) ∧
        c.descriptionBits ≤ symDescCap degree r.q
  | .thr r _ _ t => t = target ∧ ∀ c ∈ r.circuits,
      c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 9 r.q) ∧
        c.descriptionBits ≤ descriptionEnvelope degree r.q

/-- The runtime request the source makes from admitted atoms (`Packets.request` in `Request` form). -/
def admittedRequest : (mode : Bool) → {q : ℕ} → {circuit : BooleanCircuit q} →
    {pcpp : PointwisePCPP circuit} → (atoms : List (Atom pcpp)) → atoms.length ≤ 4 → ℕ → ℕ → Request
  | true, q, _, _, atoms, hfour, L, target =>
      .sym ⟨q, atoms.map nativeSymmetricAtom⟩ (by simpa using hfour) L target
  | false, q, _, _, atoms, hfour, L, target =>
      .thr ⟨q, atoms.map nativeThresholdAtom⟩ (by simpa using hfour) L target

theorem admittedRequest_family_sym (sources : EightSources) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hfour : atoms.length ≤ 4) (L target : ℕ) :
    (admittedRequest true atoms hfour L target).family (decompositionOf sources) =
      Packets.request sources L target true atoms := rfl

theorem admittedRequest_family_thr (sources : EightSources) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hfour : atoms.length ≤ 4) (L target : ℕ) :
    (admittedRequest false atoms hfour L target).family (decompositionOf sources) =
      Packets.request sources L target false atoms := rfl

theorem admittedRequest_q (mode : Bool) {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp)) (hfour : atoms.length ≤ 4)
    (L target : ℕ) : (admittedRequest mode atoms hfour L target).q = q := by
  cases mode <;> rfl

theorem admittedRequest_liveScale (mode : Bool) {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp)) (hfour : atoms.length ≤ 4)
    (L target : ℕ) : (admittedRequest mode atoms hfour L target).liveScale = L := by
  cases mode <;> rfl

/-- **The bridge**: admitted atoms give an admitted runtime request (either mode). -/
theorem Admitted.requestAdmitted {den degree : ℕ} (hden : 1 ≤ den) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) (mode : Bool) (L target : ℕ) :
    RequestAdmitted den degree target (admittedRequest mode atoms h.four L target) := by
  cases mode with
  | true => exact ⟨rfl, fun c hc => ⟨h.sym_wires c hc, h.sym_descriptions hden c hc⟩⟩
  | false => exact ⟨rfl, fun c hc => ⟨h.thr_wires c hc, h.thr_descriptions hden c hc⟩⟩

/-! ## 2. Logarithms as polynomials -/

theorem two_pow_logScale_le (q : ℕ) : 2^logScale q ≤ 4*(q+1) := by
  unfold logScale
  have h : 1 < q+2 := by omega
  have hlt := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
  have hpos : 0 < Nat.clog 2 (q+2) := Nat.clog_pos (by decide) h
  rw [Nat.pred_eq_sub_one] at hlt
  have hs : 2^Nat.clog 2 (q+2) = 2*2^(Nat.clog 2 (q+2)-1) := by
    rw [← pow_succ']
    congr 1
  omega

theorem two_pow_mul_logScale_poly (k : ℕ) : PolynomiallyBounded (fun q => 2^(k*logScale q)) := by
  refine ⟨4^k, k, by positivity, fun q => ?_⟩
  calc 2^(k*logScale q) = (2^logScale q)^k := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (4*(q+1))^k := Nat.pow_le_pow_left (two_pow_logScale_le q) k
    _ = 4^k*(q+1)^k := by rw [mul_pow]

theorem two_pow_natBitLength_le (n : ℕ) : 2^natBitLength n ≤ 2*n+2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    rw [pow_succ]
    omega

theorem polynomiallyBounded_two_pow_bits {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun q => 2^(k*natBitLength (f q))) := by
  refine polynomiallyBounded_mono (fun q => ?_)
    (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_mul
      (polynomiallyBounded_constant 2) hf) (polynomiallyBounded_constant 2)) k)
  calc 2^(k*natBitLength (f q)) = (2^natBitLength (f q))^k := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2*f q+2)^k := Nat.pow_le_pow_left (two_pow_natBitLength_le _) k

theorem two_pow_bits_succ_poly {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun q => 2^(natBitLength (f q) + 1)) := by
  refine polynomiallyBounded_mono (fun q => ?_)
    (polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 4) hf)
      (polynomiallyBounded_constant 4))
  have h := two_pow_natBitLength_le (f q)
  rw [pow_succ]
  omega

/-! ## 3. The walk-seed count -/

theorem seedList_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ) :
    (Packets.seedList occ I den).length =
      2^walkExponent (toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I))) den := by
  unfold Packets.seedList
  rw [List.length_ofFn, card_walkSample]

/-- Walk seeds of a population `≤ 8(q+1)^3` at list denominator `den` are at most
`2^(18 L_q + 43 + 320 (natBitLength den + 1))`. -/
theorem seedList_length_le {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (den : ℕ) (hpop : occ.length ≤ 8*(q+1)^3) :
    (Packets.seedList occ I den).length ≤
      2^(18*logScale q + 43 + 320*(natBitLength den + 1)) := by
  rw [seedList_length]
  have hq : 8*(q+1)^3 ≤ 2^(3*logScale q+3) := by
    have h := Nat.pow_le_pow_left (succ_le_two_pow_logScale' q) 3
    rw [← pow_mul, Nat.mul_comm] at h
    rw [pow_add]
    omega
  have hden : den + 1 ≤ 2^(natBitLength den + 1) := by
    have h := lt_two_pow_natBitLength den
    rw [pow_succ]
    omega
  have hw := walkExponent_le_seedEnvelope (le_refl occ.length)
    (touchingCost_le_length occ I) (le_refl den)
  have he := seedEnvelope_le_of_bits (popBits := 3*logScale q+3) (touchBits := 3*logScale q+3)
    (hpop.trans hq) (hpop.trans hq) hden
  apply Nat.pow_le_pow_right (by decide)
  unfold LiveRows.bound at *
  omega

/-! ## 4. `h_rows` -/

/-- The SYM external rows are the walk seeds times the offset tuples. -/
theorem sym_rows_le (den target : ℕ) (hden : 1 ≤ den)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 5 r.q)) (L : ℕ) :
    (Packets.symFamily r L target).rows.length ≤
      2^(18*logScale r.q) * 2^(43 + 320*(natBitLength (4*(target+1)) + 1)) * (2*(r.q+1)^3+1)^4 := by
  have hpop := sym_population hden 5 r hfour hw
  rw [← RCFive.RowKeys.sym_rows_eq, List.length_map, RCFive.RowKeys.sym_count]
  apply Nat.mul_le_mul
  · rw [← pow_add]
    refine (seedList_length_le _ _ _ hpop).trans (Nat.pow_le_pow_right (by decide) ?_)
    have hd : symmetricListDenominator r target ≤ 4*(target+1) := by
      unfold symmetricListDenominator
      exact Nat.mul_le_mul_right _ hfour
    have hb := PolynomialClock.natBitLength_mono hd
    omega
  · have hb : ∀ i ∈ (Finset.univ : Finset (Fin r.circuits.length)),
        (r.circuits.get i).bottomCount + 1 ≤ 2*(r.q+1)^3+1 := by
      intro i _
      have h1 := symmetric_bottomCount_le_wireCount (r.circuits.get i)
      have h2 := wires_le_cube_max hden 5 r.q (r.circuits.get i).wireCount
        (hw (r.circuits.get i) (List.get_mem _ _))
      omega
    calc (∏ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount+1))
        ≤ (2*(r.q+1)^3+1)^(Finset.univ : Finset (Fin r.circuits.length)).card :=
          Finset.prod_le_pow_card _ _ _ hb
      _ ≤ (2*(r.q+1)^3+1)^4 := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact Nat.pow_le_pow_right (by omega) hfour

/-- The THR external rows: child selections × primes × walk seeds × residues. -/
theorem thr_rows_le (a : DecompositionAlgorithm) (den degree target : ℕ) (hden : 1 ≤ den)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 9 r.q))
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ descriptionEnvelope degree r.q) (L : ℕ) :
    (Packets.thrFamily a r L target).rows.length ≤
      (sourceChildBound a (descriptionEnvelope degree r.q)+1)^4 *
        ((tupleCutoffBound a (descriptionEnvelope degree r.q) target + 1) *
          (2^(18*logScale r.q) * 2^43 * ((2^(natBitLength
            (tupleListDenominatorBound a (descriptionEnvelope degree r.q) target) + 1))^20)^16 *
           tupleCutoffBound a (descriptionEnvelope degree r.q) target)) := by
  have hpop := thr_population hden 9 r hfour hw
  set D := descriptionEnvelope degree r.q
  set cutoff := RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target
  set lden := RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target
  have hcut : cutoff ≤ tupleCutoffBound a D target := primeCutoff_le a r D target hfour hd
  have hlden : lden ≤ tupleListDenominatorBound a D target := listDenominator_le a r D target hfour hd
  rw [← RCFive.RowKeys.thr_rows_eq, List.length_map, RCFive.RowKeys.thr_count]
  apply Nat.mul_le_mul
  · have hsel := RepairSource.CloseoutRawRows.selection_count a r D hfour hd
    have hcard : (Packets.thrSelectionList a r).length =
        Fintype.card (RepairOrdinary.ThresholdRows.Selection a r) := by
      unfold Packets.thrSelectionList
      rw [RCFive.RowKeys.finiteProduct_length]
      simp only [RepairOrdinary.ThresholdRows.Selection, Fintype.card_pi, Fintype.card_fin]
    rw [hcard]
    exact hsel
  · set S := (Packets.seedList (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L) lden).length
    have hS : S ≤ 2^(18*logScale r.q) * 2^43 * ((2^(natBitLength
        (tupleListDenominatorBound a D target) + 1))^20)^16 := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      exact (seedList_length_le _ _ _ hpop).trans (Nat.pow_le_pow_right (by decide)
        (by have := PolynomialClock.natBitLength_mono hlden; omega))
    have helem : ∀ x ∈ (List.ofFn (primeIndexFinEquiv cutoff).symm).map (fun prime => S * prime.val),
        x ≤ S * tupleCutoffBound a D target := by
      intro x hx
      obtain ⟨prime, _, rfl⟩ := List.mem_map.mp hx
      exact Nat.mul_le_mul_left S ((mem_primesUpTo.mp prime.property).2.trans hcut)
    have hsum := List.sum_le_card_nsmul _ _ helem
    rw [List.length_map, List.length_ofFn, smul_eq_mul] at hsum
    have hprimes : Fintype.card (PrimeIndex cutoff) ≤ tupleCutoffBound a D target + 1 := by
      rw [Fintype.card_coe]
      exact (primesUpTo_card_le cutoff).trans (by omega)
    calc ((List.ofFn (primeIndexFinEquiv cutoff).symm).map (fun prime => S * prime.val)).sum
        ≤ Fintype.card (PrimeIndex cutoff) * (S * tupleCutoffBound a D target) := hsum
      _ ≤ (tupleCutoffBound a D target + 1) * (2^(18*logScale r.q) * 2^43 * ((2^(natBitLength
            (tupleListDenominatorBound a D target) + 1))^20)^16 * tupleCutoffBound a D target) :=
          Nat.mul_le_mul hprimes (Nat.mul_le_mul_right _ hS)

/-- **`h_rows`.** One pair `(rowsC, rowsE)`, chosen from `a degree target` alone, bounds the external
rows of every admitted runtime request at every live scale and every `den ≥ 1`. -/
theorem rows_poly (a : DecompositionAlgorithm) (degree target : ℕ) :
    ∃ rowsC rowsE : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      (r.family a).rows.length + 1 ≤ rowsC*(r.q+1)^rowsE := by
  have hS : PolynomiallyBounded (fun q =>
      2^(18*logScale q) * 2^(43 + 320*(natBitLength (4*(target+1)) + 1)) * (2*(q+1)^3+1)^4) :=
    polynomiallyBounded_mul (polynomiallyBounded_mul (two_pow_mul_logScale_poly 18)
      (polynomiallyBounded_constant _)) (polynomiallyBounded_pow (polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_pow
        (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 3))
      (polynomiallyBounded_constant 1)) 4)
  have hD := descriptionEnvelope_polynomial degree
  have htarget : PolynomiallyBounded (fun _ : ℕ => target) := polynomiallyBounded_constant target
  have hTC := tupleCutoffBound_polynomial a degree _ htarget
  have hTL := tupleListDenominatorBound_polynomial a degree _ htarget
  have hT : PolynomiallyBounded (fun q =>
      (sourceChildBound a (descriptionEnvelope degree q)+1)^4 *
        ((tupleCutoffBound a (descriptionEnvelope degree q) target + 1) *
          (2^(18*logScale q) * 2^43 * ((2^(natBitLength
            (tupleListDenominatorBound a (descriptionEnvelope degree q) target) + 1))^20)^16 *
           tupleCutoffBound a (descriptionEnvelope degree q) target))) :=
    polynomiallyBounded_mul (polynomiallyBounded_pow (polynomiallyBounded_add
      (sourceChildBound_polynomial a hD) (polynomiallyBounded_constant 1)) 4)
      (polynomiallyBounded_mul (polynomiallyBounded_add hTC (polynomiallyBounded_constant 1))
        (polynomiallyBounded_mul (polynomiallyBounded_mul (polynomiallyBounded_mul
          (two_pow_mul_logScale_poly 18) (polynomiallyBounded_constant _))
          (polynomiallyBounded_pow (polynomiallyBounded_pow (two_pow_bits_succ_poly hTL) 20) 16)) hTC))
  obtain ⟨C, E, _, hC⟩ := polynomiallyBounded_add (polynomiallyBounded_add hS hT)
    (polynomiallyBounded_constant 1)
  refine ⟨C, E, ?_⟩
  intro den hden r hr
  refine le_trans ?_ (hC r.q)
  cases r with
  | terminal => simp [Request.family]
  | sym r0 four L t =>
    obtain ⟨rfl, hc⟩ := hr
    have h := sym_rows_le den t hden r0 four (fun c hc' => (hc c hc').1) L
    exact Nat.add_le_add_right (h.trans (Nat.le_add_right _ _)) 1
  | thr r0 four L t =>
    obtain ⟨rfl, hc⟩ := hr
    have h := thr_rows_le a den degree t hden r0 four (fun c hc' => (hc c hc').1)
      (fun c hc' => (hc c hc').2) L
    exact Nat.add_le_add_right (h.trans (Nat.le_add_left _ _)) 1

end
end NearCubicWires.Admission
