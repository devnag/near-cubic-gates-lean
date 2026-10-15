import Proof.SourceAssembly.AdmissionRequest

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CompilerSemantics
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  sourceChildBound sourceChildBound_polynomial symmetric_occurrences_description
  threshold_occurrences_description)
open FixedLivePackets PacketProduction
open scoped BigOperators

noncomputable section

/-! ## 1. Word lengths -/

theorem natBitLength_le_succ (n : ℕ) : natBitLength n ≤ n+1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem natWord_le (n : ℕ) : (natWord n).length ≤ 2*n+3 := by
  rw [RepairOrdinary.DecompositionSource.natWord_length]
  have := natBitLength_le_succ n
  omega

theorem bottomWord_le {q : ℕ} (g : SupportedNormalizedGate q) :
    (bottomWord g).length ≤ 2*q + 2*g.descriptionBits + 7 := by
  unfold bottomWord
  rw [RepairOrdinary.DecompositionSource.thresholdWord_length]
  have hs := CloseoutRawRows.strict_gate_bits g.gate
  have hb := natBitLength_le_succ q
  unfold SupportedNormalizedGate.descriptionBits
  omega

theorem flatMap_frame_length {α : Type} (xs : List α) (f : α → List Bool) :
    (xs.flatMap (fun x => RepairOrdinary.frame (f x))).length =
      (xs.map (fun x => 2*(f x).length+1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, RepairOrdinary.frame_length, List.map_cons,
      List.sum_cons, ih]

theorem flatMap_frame_le {α : Type} (xs : List α) (f : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap (fun x => RepairOrdinary.frame (f x))).length ≤ xs.length * (2*B+1) := by
  rw [flatMap_frame_length]
  have hm : ∀ y ∈ xs.map (fun x => 2*(f x).length+1), y ≤ 2*B+1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := h x hx
    omega
  simpa using List.sum_le_card_nsmul _ _ hm

theorem symWord_le {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    (symWord c).length ≤ (4*q+23)*(c.descriptionBits+1) := by
  have hdesc : c.descriptionBits = c.bottomCount + 1 + ∑ i, (c.bottom i).descriptionBits := rfl
  have hsum : ((List.ofFn c.bottom).flatMap (fun g => RepairOrdinary.frame (bottomWord g))).length ≤
      c.bottomCount*(4*q+15) + 4*∑ i, (c.bottom i).descriptionBits := by
    rw [flatMap_frame_length, List.map_ofFn, List.sum_ofFn]
    calc (∑ i : Fin c.bottomCount, ((fun x => 2*(bottomWord x).length+1) ∘ c.bottom) i)
        ≤ ∑ i : Fin c.bottomCount, (4*q+15 + 4*(c.bottom i).descriptionBits) := by
          apply Finset.sum_le_sum
          intro i _
          have := bottomWord_le (c.bottom i)
          simp only [Function.comp]
          omega
      _ = c.bottomCount*(4*q+15) + 4*∑ i, (c.bottom i).descriptionBits := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  unfold symWord
  simp only [List.length_append, RepairOrdinary.frame_length, List.length_ofFn]
  have hn := natWord_le c.bottomCount
  set S := ∑ i, (c.bottom i).descriptionBits
  rw [hdesc]
  nlinarith [Nat.zero_le (q*S), Nat.zero_le (q*c.bottomCount)]

theorem thrWord_le {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    (thrWord c).length ≤ (4*q+4*c.descriptionBits+60)*(c.descriptionBits+1) := by
  have hdesc : c.descriptionBits = c.top.gate.encodingBits + c.bottomCount +
      ∑ i, (c.bottom i).descriptionBits := rfl
  set S := ∑ i, (c.bottom i).descriptionBits with hS
  have hcard : c.top.support.card ≤ c.bottomCount := by
    simpa using Finset.card_le_univ c.top.support
  have hwire : c.top.wireCount ≤ c.bottomCount := hcard
  have hone : ∀ j : Fin c.bottomCount, (c.bottom j).descriptionBits ≤ S :=
    fun j => Finset.single_le_sum (fun i _ => Nat.zero_le ((c.bottom i).descriptionBits))
      (Finset.mem_univ j)
  have hflat : ((List.ofFn (fun i => c.bottom (retainedTopIndex c i))).flatMap
      (fun g => RepairOrdinary.frame (bottomWord g))).length ≤
      c.top.support.card*(2*(2*q+2*S+7)+1) := by
    have h := flatMap_frame_le (List.ofFn (fun i => c.bottom (retainedTopIndex c i))) bottomWord
      (2*q+2*S+7) (by
        intro g hg
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
        have := bottomWord_le (c.bottom (retainedTopIndex c i))
        have := hone (retainedTopIndex c i)
        omega)
    simpa using h
  have htop := RepairOrdinary.DecompositionSource.thresholdWord_bound
    (nonStrictAsStrict (retainedTopGate c))
  have hs := CloseoutRawRows.strict_gate_bits (retainedTopGate c)
  have hr := CloseoutRawRows.retained_top_bits c
  have hn := natWord_le c.top.wireCount
  unfold thrWord
  simp only [List.length_append, RepairOrdinary.frame_length]
  rw [hdesc]
  nlinarith [Nat.zero_le (q*S), Nat.zero_le (q*c.bottomCount), Nat.zero_le (S*S),
    Nat.zero_le (c.bottomCount*c.bottomCount), Nat.zero_le (c.top.gate.encodingBits*S),
    Nat.zero_le (q*c.top.gate.encodingBits), Nat.zero_le (c.bottomCount*S),
    Nat.zero_le (c.top.gate.encodingBits*c.bottomCount),
    Nat.zero_le (c.top.gate.encodingBits*c.top.gate.encodingBits)]

theorem flatMap_le {α : Type} (xs : List α) (f : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-! ## 2. The five framed fields of `Request.input` -/

theorem sym_nativeWord_le (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L t D : ℕ) (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ D) :
    (Request.sym r four L t).nativeWord.length ≤
      2*L + 2*t + 2*r.q + 25 + 4*(2*((4*r.q+4*D+60)*(D+1))+1) := by
  have hf := flatMap_frame_le r.circuits symWord ((4*r.q+4*D+60)*(D+1)) (by
    intro c hc
    exact (symWord_le c).trans (Nat.mul_le_mul (by omega) (by have := hd c hc; omega)))
  have hm := Nat.mul_le_mul_right (2*((4*r.q+4*D+60)*(D+1))+1) four
  have h1 := natWord_le 0
  have h2 := natWord_le r.q
  have h3 := natWord_le L
  have h4 := natWord_le t
  have h5 := natWord_le r.circuits.length
  unfold Request.nativeWord
  simp only [List.length_append]
  omega

theorem thr_nativeWord_le (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L t D : ℕ) (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ D) :
    (Request.thr r four L t).nativeWord.length ≤
      2*L + 2*t + 2*r.q + 25 + 4*(2*((4*r.q+4*D+60)*(D+1))+1) := by
  have hf := flatMap_frame_le r.circuits thrWord ((4*r.q+4*D+60)*(D+1)) (by
    intro c hc
    have := hd c hc
    exact (thrWord_le c).trans (Nat.mul_le_mul (by omega) (by omega)))
  have hm := Nat.mul_le_mul_right (2*((4*r.q+4*D+60)*(D+1))+1) four
  have h1 := natWord_le 1
  have h2 := natWord_le r.q
  have h3 := natWord_le L
  have h4 := natWord_le t
  have h5 := natWord_le r.circuits.length
  unfold Request.nativeWord
  simp only [List.length_append]
  omega

theorem supportWord_le (a : DecompositionAlgorithm) (r : Request) :
    (r.supportWord a).length ≤ (r.family a).occurrences.length * (2*r.q+1) := by
  unfold Request.supportWord
  exact flatMap_frame_le _ _ r.q (fun g _ => by simp)

theorem mask_length {q : ℕ} (occ : List (SupportedNormalizedGate q)) (L : ℕ) :
    (CyclicChoice.mask occ L).length = q := by
  unfold CyclicChoice.mask
  simp

theorem natListWord_le (xs : List ℕ) (B : ℕ) (h : ∀ x ∈ xs, x ≤ B) :
    (natListWord xs).length ≤ 2*xs.length + 3 + xs.length*(2*B+3) := by
  have hf := flatMap_le xs natWord (2*B+3) (by
    intro x hx
    have := h x hx
    have := natWord_le x
    omega)
  have hn := natWord_le xs.length
  unfold natListWord
  simp only [List.length_append]
  omega

theorem indexWord_le (a : DecompositionAlgorithm) (r : Request) (B : ℕ)
    (hB : ∀ g ∈ CloseoutRowsUniversal.pool (Packets.live (r.family a)) (r.family a).occurrences,
      (ExtDecompositionBatch.children a g).length ≤ B) :
    (r.indexWord a).length ≤ 4*(r.family a).occurrences.length + 3 +
      2*(r.family a).occurrences.length*(2*B+3) := by
  have h := natListWord_le (ExtDecompositionBatch.counts a
    (CloseoutRowsUniversal.pool (Packets.live (r.family a)) (r.family a).occurrences)) B (by
      intro x hx
      unfold ExtDecompositionBatch.counts at hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact hB g hg)
  rw [ExtDecompositionBatch.counts_length, CloseoutRowsUniversal.pool_length] at h
  unfold Request.indexWord
  exact h.trans (le_of_eq (by ring))

theorem thr_topWord_le (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L t D : ℕ) (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ D) :
    ((Request.thr r four L t).topWord a).length ≤ 4*(2*(2*D+3+sourceChildBound a D)+1) := by
  show (r.circuits.flatMap (fun c => RepairOrdinary.frame (natWord c.top.support.card ++
    exactListWord (RepairOrdinary.ThresholdRows.children a c)))).length ≤ _
  have hf := flatMap_frame_le r.circuits
    (fun c => natWord c.top.support.card ++ exactListWord (RepairOrdinary.ThresholdRows.children a c))
    (2*D+3+sourceChildBound a D) (by
      intro c hc
      have hb := CloseoutRawRows.top_output_bytes a c D (hd c hc)
      have hcard : c.top.support.card ≤ c.bottomCount := by
        simpa using Finset.card_le_univ c.top.support
      have hbc := ComponentwiseCircuitRestriction.threshold_bottomCount_le_descriptionBits c
      have hn := natWord_le c.top.support.card
      have := hd c hc
      simp only [List.length_append]
      omega)
  beta_reduce at hf
  have hm := Nat.mul_le_mul_right (2*(2*D+3+sourceChildBound a D)+1) four
  omega

theorem input_length (a : DecompositionAlgorithm) (r : Request) :
    (r.input a).length = 2*r.nativeWord.length + 2*(r.supportWord a).length +
      2*(CyclicChoice.mask (r.family a).occurrences r.liveScale).length +
      2*(r.indexWord a).length + 2*(r.topWord a).length + 5 := by
  unfold Request.input
  simp only [List.length_append, RepairOrdinary.frame_length]
  omega

/-! ## 3. `h_input` -/

/-- The unified description cap of every native circuit of an admitted request (either mode). -/
def uCap (degree q : ℕ) : ℕ := symDescCap degree q + descriptionEnvelope degree q

theorem uCap_polynomial (degree : ℕ) : PolynomiallyBounded (uCap degree) :=
  polynomiallyBounded_add (symDescCap_polynomial degree) (descriptionEnvelope_polynomial degree)

/-- The explicit polynomial (in `q`, for fixed `a degree target` and child exponent `c`) that bounds
every admitted request's input apart from the `4*L` of its `natWord L` field. -/
def inputPoly (a : DecompositionAlgorithm) (degree target c q : ℕ) : ℕ :=
  5 + 2*((2*q + 25 + 2*target) + 4*(2*((4*q+4*uCap degree q+60)*(uCap degree q+1))+1)) +
    2*(8*(q+1)^3*(2*q+1)) + 2*q +
    2*(4*(8*(q+1)^3) + 3 + 2*(8*(q+1)^3)*(2*2^(c*logScale q)+3)) +
    2*(4*(2*(2*uCap degree q+3+sourceChildBound a (uCap degree q))+1))

theorem inputPoly_polynomial (a : DecompositionAlgorithm) (degree target c : ℕ) :
    PolynomiallyBounded (inputPoly a degree target c) := by
  have hq := polynomiallyBounded_id
  have hU := uCap_polynomial degree
  have k := fun (n : ℕ) => polynomiallyBounded_constant n
  have hcube : PolynomiallyBounded (fun q : ℕ => (q+1)^3) :=
    polynomiallyBounded_pow (polynomiallyBounded_add hq (k 1)) 3
  have h1 : PolynomiallyBounded (fun q : ℕ => (2*q + 25 + 2*target) +
      4*(2*((4*q+4*uCap degree q+60)*(uCap degree q+1))+1)) :=
    polynomiallyBounded_add
      (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul (k 2) hq) (k 25))
        (k (2*target)))
      (polynomiallyBounded_mul (k 4) (polynomiallyBounded_add (polynomiallyBounded_mul (k 2)
        (polynomiallyBounded_mul (polynomiallyBounded_add (polynomiallyBounded_add
          (polynomiallyBounded_mul (k 4) hq) (polynomiallyBounded_mul (k 4) hU)) (k 60))
          (polynomiallyBounded_add hU (k 1)))) (k 1)))
  have h3 : PolynomiallyBounded (fun q : ℕ => 8*(q+1)^3*(2*q+1)) :=
    polynomiallyBounded_mul (polynomiallyBounded_mul (k 8) hcube)
      (polynomiallyBounded_add (polynomiallyBounded_mul (k 2) hq) (k 1))
  have h5 : PolynomiallyBounded (fun q : ℕ => 4*(8*(q+1)^3) + 3 +
      2*(8*(q+1)^3)*(2*2^(c*logScale q)+3)) :=
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul (k 4)
      (polynomiallyBounded_mul (k 8) hcube)) (k 3))
      (polynomiallyBounded_mul (polynomiallyBounded_mul (k 2) (polynomiallyBounded_mul (k 8) hcube))
        (polynomiallyBounded_add (polynomiallyBounded_mul (k 2) (two_pow_mul_logScale_poly c)) (k 3)))
  have h6 : PolynomiallyBounded (fun q : ℕ =>
      4*(2*(2*uCap degree q+3+sourceChildBound a (uCap degree q))+1)) :=
    polynomiallyBounded_mul (k 4) (polynomiallyBounded_add (polynomiallyBounded_mul (k 2)
      (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_mul (k 2) hU) (k 3))
        (sourceChildBound_polynomial a hU))) (k 1))
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (polynomiallyBounded_add (k 5) (polynomiallyBounded_mul (k 2) h1))
      (polynomiallyBounded_mul (k 2) h3)) (polynomiallyBounded_mul (k 2) hq))
    (polynomiallyBounded_mul (k 2) h5)) (polynomiallyBounded_mul (k 2) h6)

/-- Per-request form: the input is at most `4*L + inputPoly`. -/
theorem input_le (a : DecompositionAlgorithm) (degree target c : ℕ) (hc : ∀ q
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)),
      (∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ uCap degree q) →
      ∀ i : Fin (CloseoutRowsUniversal.pool live occ).length,
        (ExtDecompositionBatch.children a ((CloseoutRowsUniversal.pool live occ).get i)).length <
          2^(c*logScale q))
    (den : ℕ) (hden : 1 ≤ den) (r : Request) (hr : RequestAdmitted den degree target r) :
    (r.input a).length ≤ 4*r.liveScale + inputPoly a degree target c r.q := by
  -- pooled child counts, from occurrence descriptions
  have hpool : ∀ {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)),
      (∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ uCap degree q) →
      ∀ g ∈ CloseoutRowsUniversal.pool live occ,
        (ExtDecompositionBatch.children a g).length ≤ 2^(c*logScale q) := by
    intro q live occ hd g hg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    exact (hc q live occ hd i).le
  rw [input_length]
  have hmask := mask_length (r.family a).occurrences r.liveScale
  have hsupp := supportWord_le a r
  unfold inputPoly
  cases r with
  | terminal =>
    have hn : (Request.terminal).nativeWord.length ≤ 7 := natWord_le 2
    have hi := indexWord_le a Request.terminal 0 (by intro g hg; simp [Request.family,
      CloseoutRowsUniversal.pool] at hg)
    have ht : (Request.terminal.topWord a).length = 0 := rfl
    have hocc : (Request.terminal.family a).occurrences.length = 0 := rfl
    rw [hocc] at hsupp hi
    simp only [Request.q, Request.liveScale] at *
    omega
  | sym r0 four L t =>
    obtain ⟨rfl, hcirc⟩ := hr
    have hU : ∀ c ∈ r0.circuits, c.descriptionBits ≤ uCap degree r0.q :=
      fun c hc' => (hcirc c hc').2.trans (Nat.le_add_right _ _)
    have hn := sym_nativeWord_le r0 four L t (uCap degree r0.q) hU
    have hpop := sym_population hden 5 r0 four (fun c hc' => (hcirc c hc').1)
    have hocc := symmetric_occurrences_description r0 (uCap degree r0.q) hU
    have hi := indexWord_le a (Request.sym r0 four L t) (2^(c*logScale r0.q))
      (hpool _ (symmetricFourfoldOccurrences r0) hocc)
    have ht : ((Request.sym r0 four L t).topWord a).length = 0 := rfl
    change (symmetricFourfoldOccurrences r0).length*(2*r0.q+1) ≥ _ at hsupp
    change _ ≤ 4*(symmetricFourfoldOccurrences r0).length + 3 +
      2*(symmetricFourfoldOccurrences r0).length*(2*2^(c*logScale r0.q)+3) at hi
    have h1 := Nat.mul_le_mul_right (2*r0.q+1) hpop
    have h2 := Nat.mul_le_mul_right (2*2^(c*logScale r0.q)+3) (Nat.mul_le_mul_left 2 hpop)
    simp only [Request.q, Request.liveScale] at *
    omega
  | thr r0 four L t =>
    obtain ⟨rfl, hcirc⟩ := hr
    have hU : ∀ c ∈ r0.circuits, c.descriptionBits ≤ uCap degree r0.q :=
      fun c hc' => (hcirc c hc').2.trans (Nat.le_add_left _ _)
    have hn := thr_nativeWord_le r0 four L t (uCap degree r0.q) hU
    have hpop := thr_population hden 9 r0 four (fun c hc' => (hcirc c hc').1)
    have hocc := threshold_occurrences_description r0 (uCap degree r0.q) hU
    have hi := indexWord_le a (Request.thr r0 four L t) (2^(c*logScale r0.q))
      (hpool _ (thresholdFourfoldOccurrences r0) hocc)
    have ht := thr_topWord_le a r0 four L t (uCap degree r0.q) hU
    change (thresholdFourfoldOccurrences r0).length*(2*r0.q+1) ≥ _ at hsupp
    change _ ≤ 4*(thresholdFourfoldOccurrences r0).length + 3 +
      2*(thresholdFourfoldOccurrences r0).length*(2*2^(c*logScale r0.q)+3) at hi
    have h1 := Nat.mul_le_mul_right (2*r0.q+1) hpop
    have h2 := Nat.mul_le_mul_right (2*2^(c*logScale r0.q)+3) (Nat.mul_le_mul_left 2 hpop)
    simp only [Request.q, Request.liveScale] at *
    omega

/-- **`h_input`.** One pair `(C, E)`, chosen from `a degree target` alone, bounds the input of every
admitted runtime request at every live scale `L` and every `den ≥ 1` by `(C + 4L)*(q+1)^E`. -/
theorem input_poly (a : DecompositionAlgorithm) (degree target : ℕ) :
    ∃ C E : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      (r.input a).length ≤ (C + 4*r.liveScale)*(r.q+1)^E := by
  obtain ⟨c, _, hc⟩ := CloseoutRowsUniversal.pooled_child_log a (uCap_polynomial degree)
  obtain ⟨C, E, _, hC⟩ := inputPoly_polynomial a degree target c
  refine ⟨C, E, ?_⟩
  intro den hden r hr
  have h := input_le a degree target c hc den hden r hr
  have hP := hC r.q
  have hpos : 1 ≤ (r.q+1)^E := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hL : 4*r.liveScale ≤ 4*r.liveScale*(r.q+1)^E := Nat.le_mul_of_pos_right _ hpos
  calc (r.input a).length ≤ 4*r.liveScale + inputPoly a degree target c r.q := h
    _ ≤ 4*r.liveScale*(r.q+1)^E + C*(r.q+1)^E := Nat.add_le_add hL hP
    _ = (C + 4*r.liveScale)*(r.q+1)^E := by ring

end
end NearCubicWires.Admission
