import Proof.SourceAssembly.AdmissionPredicate
import Proof.SourceAssembly.RawFamily
import Proof.CaseAnalysis.FinalPrimeWindow
import Proof.CaseAnalysis.RowsUniversalResources
import Proof.CaseAnalysis.FinalModeNativeEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutRowsRawLogShape
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  actual_description_envelope symmetric_occurrences_description threshold_occurrences_description
  polynomial_walk_log polynomial_bits_log wire_le_cube bits_two_pow rowDepthAt windowSumAt)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow (tupleCutoffBound
  tupleListDenominatorBound primeCutoff_le listDenominator_le modulusDigitCount_mono
  tupleCutoffBound_polynomial tupleListDenominatorBound_polynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope (parityDescCap
  nativeThresholdParity_description)
open FixedLivePackets

noncomputable section

/-! ## 1. The carried cap is at most cubic -/

theorem carriedWireCap_le_cube {den : ℕ} (hden : 1 ≤ den) (e q : ℕ) :
    carriedWireCap den e q ≤ q^3 := by
  have hd : (1 : ℝ) ≤ den := by exact_mod_cast hden
  have ha : 1 / (den : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hd
  apply wire_le_cube ha
  apply Nat.floor_le
  unfold wireScale
  positivity

theorem wires_le_cube_max {den : ℕ} (hden : 1 ≤ den) (e q w : ℕ)
    (hw : w ≤ max (q*(q+1)) (carriedWireCap den e q)) : w ≤ 2*(q+1)^3 := by
  have hc := carriedWireCap_le_cube hden e q
  have h1 : q*(q+1) ≤ (q+1)^3 := by nlinarith
  have h2 : q^3 ≤ (q+1)^3 := Nat.pow_le_pow_left (Nat.le_succ q) 3
  rcases le_max_iff.mp hw with h | h <;> omega

/-! ## 2. Descriptions of the native circuits -/

theorem normalizedGateDescriptionCap_mono {a b : ℕ} (h : a ≤ b) :
    normalizedGateDescriptionCap a ≤ normalizedGateDescriptionCap b := by
  unfold normalizedGateDescriptionCap
  have h2 : a*a ≤ b*b := Nat.mul_le_mul h h
  have h3 : (a+1)*(a*a+1) ≤ (b+1)*(b*b+1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem parityDescCap_le_envelope (degree q : ℕ) :
    parityDescCap q ≤ descriptionEnvelope degree q := by
  have hq : q ≤ q^3 := Nat.le_self_pow (by norm_num) q
  have hn : q ≤ q + CloseoutLanguage.clauseWidth degree q + 1 := by omega
  have hcap : thresholdDescriptionCap q q ≤
      thresholdDescriptionCap (q + CloseoutLanguage.clauseWidth degree q + 1) (q^3) := by
    unfold thresholdDescriptionCap
    exact Nat.add_le_add (normalizedGateDescriptionCap_mono hq)
      (Nat.mul_le_mul hq (normalizedGateDescriptionCap_mono hn))
  unfold parityDescCap descriptionEnvelope
  refine le_trans hcap (le_trans ?_ (le_max_right _ _))
  unfold CloseoutRawRows.thresholdDescription ComponentwiseCircuitRestriction.restrictedThresholdDescriptionCap
  exact le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

theorem carried_descriptions_le_envelope {den : ℕ} (hden : 1 ≤ den) (degree q : ℕ) :
    carriedSymDescription den degree q ≤ descriptionEnvelope degree q ∧
      carriedThrDescription den degree q ≤ descriptionEnvelope degree q :=
  ⟨(actual_description_envelope degree q _ (carriedWireCap_le_cube hden 5 q)).1,
   (actual_description_envelope degree q _ (carriedWireCap_le_cube hden 9 q)).2⟩

/-- THR mode: every native circuit is under `descriptionEnvelope degree q`. -/
theorem Admitted.thr_descriptions {den degree : ℕ} (hden : 1 ≤ den) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) :
    ∀ c ∈ atoms.map nativeThresholdAtom, c.descriptionBits ≤ descriptionEnvelope degree q := by
  intro c hc
  obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hc
  have he := h.envelope atom hatom
  cases atom with
  | systematic index =>
    exact (nativeThresholdParity_description _).trans (parityDescCap_le_envelope degree q)
  | threshold c => exact he.2.trans (carried_descriptions_le_envelope hden degree q).2
  | symmetric c => exact (nativeThresholdParity_description _).trans (parityDescCap_le_envelope degree q)

def symDescCap (degree q : ℕ) : ℕ :=
  descriptionEnvelope degree q + symmetricDescriptionCap q (q*(q+1))

theorem symDescCap_polynomial (degree : ℕ) : PolynomiallyBounded (symDescCap degree) := by
  have hs : PolynomiallyBounded (fun q => symmetricDescriptionCap q (q*(q+1))) := by
    refine ⟨4, 5, by norm_num, fun q => ?_⟩
    have hg : normalizedGateDescriptionCap q + 1 ≤ 4*(q+1)^3 := by
      unfold normalizedGateDescriptionCap
      nlinarith
    have hw : q*(q+1) + 1 ≤ (q+1)^2 := by nlinarith
    unfold symmetricDescriptionCap
    calc (q*(q+1) + 1)*(normalizedGateDescriptionCap q + 1) ≤ (q+1)^2*(4*(q+1)^3) :=
          Nat.mul_le_mul hw hg
      _ = 4*(q+1)^5 := by ring
  exact polynomiallyBounded_add (descriptionEnvelope_polynomial degree) hs

theorem parity_sym_description {q : ℕ} (S : Finset (Fin q)) :
    (normalizedParityCircuit S).descriptionBits ≤ symmetricDescriptionCap q (q*(q+1)) := by
  apply normalizedSymmetric_descriptionBits_le
  · exact parity_sym_wires S
  · intro index
    have hq : 0 < q := Nat.pos_of_ne_zero (fun h => by subst h; exact (supportCoordinate S index).elim0)
    have hone : 1 ≤ q^q := Nat.one_le_pow _ _ hq
    constructor
    · intro i
      change (if i = supportCoordinate S index then (1 : ℤ) else 0).natAbs ≤ q^q
      split <;> simp [hone]
    · change (1 : ℤ).natAbs ≤ q^q
      simpa using hone

/-- SYM mode: every native circuit is under `symDescCap degree q`. -/
theorem Admitted.sym_descriptions {den degree : ℕ} (hden : 1 ≤ den) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {atoms : List (Atom pcpp)}
    (h : Admitted den degree atoms) :
    ∀ c ∈ atoms.map nativeSymmetricAtom, c.descriptionBits ≤ symDescCap degree q := by
  intro c hc
  obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hc
  have he := h.envelope atom hatom
  unfold symDescCap
  cases atom with
  | systematic index => exact (parity_sym_description _).trans (Nat.le_add_left _ _)
  | symmetric c =>
    exact (he.2.trans (carried_descriptions_le_envelope hden degree q).1).trans (Nat.le_add_right _ _)
  | threshold c => exact (parity_sym_description _).trans (Nat.le_add_left _ _)

/-! ## 3. The child alphabet is `2^{O(L_q)}` -/

theorem succ_le_two_pow_logScale' (q : ℕ) : q+1 ≤ 2^logScale q := by
  unfold logScale
  have h := Nat.le_pow_clog (by decide : 1 < 2) (q+2)
  omega

/-- The pooled child list is at most `|pool|` times the per-gate child bound. -/
theorem GS_length_le (a : DecompositionAlgorithm) {q : ℕ} (xs : List (SupportedNormalizedGate q))
    (B : ℕ) (hB : ∀ g ∈ xs, (ExtDecompositionBatch.children a g).length ≤ B) :
    (ExtDecompositionBatch.GS a xs).length ≤ xs.length * B := by
  induction xs with
  | nil => simp [ExtDecompositionBatch.GS]
  | cons g xs ih =>
    rw [ExtDecompositionBatch.GS_cons, List.length_append, List.length_cons]
    have h1 := hB g (by simp)
    have h2 := ih (fun g' hg' => hB g' (by simp [hg']))
    rw [Nat.succ_mul]
    omega

/-- **The alphabet bound.**  For a description cap polynomial in `q`, one constant `ce` makes the
packet alphabet of every family whose occurrences are admitted (population `≤ 8(q+1)^3`,
descriptions `≤ cap q`) at most `2^ell` with `ell+1 ≤ (ce+1)·L_q`. -/
theorem alphabet_log (a : DecompositionAlgorithm) {cap : ℕ → ℕ} (hcap : PolynomiallyBounded cap) :
    ∃ ce : ℕ, ∀ {q L : ℕ} (F : Packets.Family q L),
      F.occurrences.length ≤ 8*(q+1)^3 →
      (∀ i : Fin F.occurrences.length, (F.occurrences.get i).descriptionBits ≤ cap q) →
      natBitLength (Packets.alphabet a F) + 1 ≤ (ce+1)*logScale q := by
  obtain ⟨c, _, hc⟩ := CloseoutRowsUniversal.pooled_child_log a hcap
  refine ⟨c+9, ?_⟩
  intro q L F hpop hdesc
  have hchild : ∀ g ∈ CloseoutRowsUniversal.pool (Packets.live F) F.occurrences,
      (ExtDecompositionBatch.children a g).length ≤ 2^(c*logScale q) := by
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    exact (hc q (Packets.live F) F.occurrences hdesc i).le
  have hGS := GS_length_le a _ _ hchild
  rw [CloseoutRowsUniversal.pool_length] at hGS
  have hl := succ_le_two_pow_logScale' q
  have hl3 : (q+1)^3 ≤ 2^(3*logScale q) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left hl 3
  have hpos : 1 ≤ 2^((c+3)*logScale q) := Nat.one_le_two_pow
  have halph : Packets.alphabet a F ≤ 2^((c+3)*logScale q + 5) := by
    unfold Packets.alphabet
    change (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)).length
      + 2 ≤ _
    have hsplit : 2^((c+3)*logScale q + 5) = 32 * (2^(3*logScale q) * 2^(c*logScale q)) := by
      rw [← pow_add, show (c+3)*logScale q + 5 = (3*logScale q + c*logScale q) + 5 by ring,
        pow_add]
      ring
    rw [hsplit]
    have hm : 2*F.occurrences.length*2^(c*logScale q) ≤
        2*(8*2^(3*logScale q))*2^(c*logScale q) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hpop.trans (Nat.mul_le_mul_left 8 hl3)))
    have hp2 : 1 ≤ 2^(3*logScale q) * 2^(c*logScale q) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hb := PolynomialClock.natBitLength_mono halph
  rw [bits_two_pow] at hb
  have hlog : 1 ≤ logScale q := logScale_pos q
  nlinarith

/-! ## 4. The THR prime-digit and walk factors are `O(L_q)` -/

theorem thr_factor_logs (a : DecompositionAlgorithm) (degree target : ℕ) :
    ∃ cz ct : ℕ, ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit),
      r.circuits.length ≤ 4 →
      (∀ c ∈ r.circuits, c.descriptionBits ≤ descriptionEnvelope degree r.q) →
      modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target)+1 ≤
          (cz+1)*logScale r.q ∧
        canonicalWalkLength (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target)+1 ≤
          (ct+1)*logScale r.q := by
  have ht : PolynomiallyBounded (fun _ : ℕ => target) := polynomiallyBounded_constant target
  obtain ⟨cz, _, hz⟩ := polynomial_bits_log (tupleCutoffBound_polynomial a degree _ ht)
  obtain ⟨ct, _, hw⟩ := polynomial_walk_log (tupleListDenominatorBound_polynomial a degree _ ht)
  refine ⟨cz, ct, ?_⟩
  intro r hfour hd
  have hlog : 1 ≤ logScale r.q := logScale_pos r.q
  constructor
  · have hm := modulusDigitCount_mono (primeCutoff_le a r (descriptionEnvelope degree r.q) target hfour hd)
    have h1 := hz r.q
    change modulusDigitCount _ + 1 ≤ cz*logScale r.q at h1
    nlinarith
  · have hle := listDenominator_le a r (descriptionEnvelope degree r.q) target hfour hd
    have hc := Nat.clog_mono_right 2 (Nat.add_le_add_right hle 1)
    have h1 := hw r.q
    unfold canonicalWalkLength at h1 ⊢
    nlinarith

/-! ## 5. Layout existence -/

/-- The explicit packet width of the admitted request (`rowWidth` of the family's own factors at
`ell = natBitLength alphabet`). -/
def admittedWidth (sources : EightSources) (L target : ℕ) (mode : Bool) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp)) : ℕ :=
  let F := Packets.request sources L target mode atoms
  let ell := natBitLength (Packets.alphabet (decompositionOf sources) F)
  if mode then
    rowWidth (atoms.map nativeSymmetricAtom).length
      (canonicalWalkLength (symmetricListDenominator ⟨q, atoms.map nativeSymmetricAtom⟩ target))
      (windowSumAt F.occurrences (Packets.live F)) (rowDepthAt F.occurrences (Packets.live F)) ell ell
  else
    rowWidth (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff
        (decompositionOf sources) ⟨q, atoms.map nativeThresholdAtom⟩ target))
      (canonicalWalkLength (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator
        (decompositionOf sources) ⟨q, atoms.map nativeThresholdAtom⟩ target))
      (windowSumAt F.occurrences (Packets.live F)) (rowDepthAt F.occurrences (Packets.live F)) ell ell

theorem sym_population {den : ℕ} (hden : 1 ≤ den) (e : ℕ)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den e r.q)) :
    (symmetricFourfoldOccurrences r).length ≤ 8*(r.q+1)^3 := by
  have hsum := batchDescription_le_card_mul NormalizedSymmetricThresholdCircuit.wireCount
    r.circuits (2*(r.q+1)^3) (fun c hc => wires_le_cube_max hden e r.q _ (hw c hc))
  have he := symmetricFourfoldOccurrences_wireCount r
  have hm := Nat.mul_le_mul_right (2*(r.q+1)^3) hfour
  omega

theorem thr_population {den : ℕ} (hden : 1 ≤ den) (e : ℕ)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (hfour : r.circuits.length ≤ 4)
    (hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den e r.q)) :
    (thresholdFourfoldOccurrences r).length ≤ 8*(r.q+1)^3 := by
  have hsum := batchDescription_le_card_mul NormalizedThresholdThresholdCircuit.wireCount
    r.circuits (2*(r.q+1)^3) (fun c hc => wires_le_cube_max hden e r.q _ (hw c hc))
  have he := thresholdFourfoldOccurrences_wireCount r
  have hm := Nat.mul_le_mul_right (2*(r.q+1)^3) hfour
  omega

theorem lt_two_pow_natBitLength (n : ℕ) : n < 2^natBitLength n := by
  simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by decide) n

theorem layout_admission (sources : EightSources) (degree target L : ℕ) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den →
      ∀ (mode : Bool) {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
        (atoms : List (Atom pcpp)), onset ≤ q → Admitted den degree atoms →
        ∀ (g : Packets.Geometry (Packets.request sources L target mode atoms)) (C : ℕ),
          ∃ layout : Packets.Layout (decompositionOf sources)
              (Packets.request sources L target mode atoms) g,
            layout.C = C ∧ layout.w = admittedWidth sources L target mode atoms := by
  let a := decompositionOf sources
  obtain ⟨ceS, hceS⟩ := alphabet_log a (symDescCap_polynomial degree)
  obtain ⟨ceT, hceT⟩ := alphabet_log a (descriptionEnvelope_polynomial degree)
  obtain ⟨cz, ct, hzt⟩ := thr_factor_logs a degree target
  obtain ⟨d1, o1, hS⟩ := Raw.admitted_symLayout target ceS L 1 (by norm_num)
  obtain ⟨d2, o2, hT⟩ := Raw.admitted_thrLayout cz ct ceT L 1 (by norm_num)
  refine ⟨max 1 (max d1 d2), max o1 o2, ?_⟩
  intro den hden mode q circuit pcpp atoms hq h g C
  have hden1 : 1 ≤ den := (le_max_left _ _).trans hden
  have hd1 : d1 ≤ den := ((le_max_left _ _).trans (le_max_right _ _)).trans hden
  have hd2 : d2 ≤ den := ((le_max_right _ _).trans (le_max_right _ _)).trans hden
  have ho1 : o1 ≤ q := (le_max_left _ _).trans hq
  have ho2 : o2 ≤ q := (le_max_right _ _).trans hq
  cases mode with
  | true =>
    let r : FourfoldRequest NormalizedSymmetricThresholdCircuit := ⟨q, atoms.map nativeSymmetricAtom⟩
    have hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (1*⌊wireScale (1/(den : ℝ)) 5 r.q⌋₊) := by
      intro c hc
      rw [one_mul]
      exact h.sym_wires c hc
    have hw' : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 5 r.q) :=
      h.sym_wires
    have hpop := sym_population hden1 5 r h.four_sym hw'
    have hocc := symmetric_occurrences_description r (symDescCap degree q) (h.sym_descriptions hden1)
    have hell := hceS (Packets.symFamily r L target) hpop hocc
    obtain ⟨layout, hC, hW⟩ := hS den hd1 a r
      (natBitLength (Packets.alphabet a (Packets.symFamily r L target))) C g ho1 h.four_sym
      (lt_two_pow_natBitLength _).le hell hw
    exact ⟨layout, hC, hW⟩
  | false =>
    let r : FourfoldRequest NormalizedThresholdThresholdCircuit := ⟨q, atoms.map nativeThresholdAtom⟩
    have hw : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (1*⌊wireScale (1/(den : ℝ)) 9 r.q⌋₊) := by
      intro c hc
      rw [one_mul]
      exact h.thr_wires c hc
    have hw' : ∀ c ∈ r.circuits, c.wireCount ≤ max (r.q*(r.q+1)) (carriedWireCap den 9 r.q) :=
      h.thr_wires
    have hpop := thr_population hden1 9 r h.four_thr hw'
    have hdesc := h.thr_descriptions hden1
    have hocc := threshold_occurrences_description r (descriptionEnvelope degree q) hdesc
    have hell := hceT (Packets.thrFamily a r L target) hpop hocc
    obtain ⟨hz, ht⟩ := hzt r h.four_thr hdesc
    obtain ⟨layout, hC, hW⟩ := hT den hd2 a r target
      (natBitLength (Packets.alphabet a (Packets.thrFamily a r L target))) C g ho2 h.four_thr hz ht
      (lt_two_pow_natBitLength _).le hell hw
    exact ⟨layout, hC, hW⟩

end
end NearCubicWires.Admission
