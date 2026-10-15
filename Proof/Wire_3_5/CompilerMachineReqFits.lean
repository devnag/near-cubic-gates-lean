import Proof.Wire_3_5.CompilerMachineReqRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut)
open NearCubicWires.ThresholdCompiler (bitInt)

/-! ## Labels in a mask -/

/-- The number of labels below `P` in the mask `U`. -/
def cnt (P U : ℕ) : ℕ := ((List.range P).filter fun c => U.testBit c).length

theorem filter_or_le (f g : ℕ → Bool) : ∀ l : List ℕ,
    (l.filter fun c => f c || g c).length ≤ (l.filter f).length + (l.filter g).length
  | [] => by simp
  | a :: l => by
    have ih := filter_or_le f g l
    simp only [List.filter_cons]
    cases hf : f a <;> cases hg : g a <;> simp <;> omega

theorem cnt_or (P U V : ℕ) : cnt P (U ||| V) ≤ cnt P U + cnt P V := by
  unfold cnt
  simp only [Nat.testBit_or]
  exact filter_or_le _ _ _

theorem cnt_zero (P : ℕ) : cnt P 0 = 0 := by simp [cnt]

theorem cnt_pow (P c : ℕ) : cnt P (2 ^ c) ≤ 1 := by
  unfold cnt
  simp only [Nat.testBit_two_pow]
  have hn : ((List.range P).filter fun i => decide (c = i)).Nodup := (List.nodup_range).filter _
  have hsub : ∀ x ∈ (List.range P).filter (fun i => decide (c = i)), x = c := by
    intro x hx
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2.symm
  rcases h : (List.range P).filter (fun i => decide (c = i)) with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp
  · simp
  · rw [h] at hn hsub
    have hx := hsub x List.mem_cons_self
    have hy := hsub y (List.mem_cons_of_mem x List.mem_cons_self)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    exact absurd (hx.trans hy.symm) hn.1.1

theorem monoMasks_cnt (pool : List (List SynEq)) (P : ℕ) :
    ∀ (mono : List ℕ), ∀ u ∈ monoMasks pool mono, cnt P u ≤ mono.length
  | [], u, hu => by
    simp only [monoMasks, List.mem_singleton] at hu
    subst hu
    simp [cnt_zero]
  | a :: as, u, hu => by
    simp only [monoMasks, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, _, u', hu', rfl⟩ := hu
    have h0 := monoMasks_cnt pool P as u' hu'
    have h1 := cnt_or P (2 ^ c) u'
    have h2 := cnt_pow P c
    simp only [List.length_cons]
    omega

theorem oddMasksM_cnt (pool : List (List SynEq)) (P d : ℕ) (p : F2Poly ℕ) (hp : ∀ mono ∈ p, mono.length ≤ d) :
    ∀ g ∈ oddMasksM pool p, cnt P g ≤ d := by
  intro g hg
  rw [mem_oddMasksM] at hg
  have hpos : 0 < (p.flatMap (monoMasks pool)).count g := by omega
  obtain ⟨mono, hmono, hgm⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp hpos)
  exact (monoMasks_cnt pool P mono g hgm).trans (hp mono hmono)

theorem unionsM_cnt (P Q d : ℕ) (G : List ℕ) (hG : ∀ g ∈ G, cnt P g ≤ d) :
    ∀ e ∈ unionsM Q G, e.1 ≤ Q ∧ cnt P e.2 ≤ e.1 * d := by
  have key : ∀ (G : List ℕ) (E : List (ℕ × ℕ)), (∀ g ∈ G, cnt P g ≤ d) →
      (∀ e ∈ E, e.1 ≤ Q ∧ cnt P e.2 ≤ e.1 * d) → ∀ e ∈ G.foldl (liftStep Q) E, e.1 ≤ Q ∧ cnt P e.2 ≤ e.1 * d := by
    intro G
    induction G with
    | nil =>
      intro E _ hE
      simpa using hE
    | cons g G ih =>
      intro E hG hE
      rw [List.foldl_cons]
      apply ih _ (fun g' hg' => hG g' (List.mem_cons_of_mem g hg'))
      intro e he
      have hg := hG g List.mem_cons_self
      unfold liftStep at he
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
      rcases he with (he | ⟨e', ⟨he', hlt⟩, rfl⟩) | he
      · exact hE e he
      · obtain ⟨_, h2⟩ := hE e' he'
        have h3 := cnt_or P e'.2 g
        refine ⟨show e'.1 + 1 ≤ Q by omega, ?_⟩
        show cnt P (e'.2 ||| g) ≤ (e'.1 + 1) * d
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · split_ifs at he with hq
        · simp only [List.mem_singleton] at he
          subst he
          exact ⟨by omega, by simpa using hg⟩
        · simp at he
  exact key G [] hG (by simp)

theorem zipIdx_filter_length {α : Type} (p : ℕ → Bool) : ∀ (l : List α) (n : ℕ),
    ((l.zipIdx n).filter fun ec => p ec.2).length = ((List.range' n l.length).filter p).length
  | [], _ => rfl
  | a :: l, n => by
    simp only [List.zipIdx_cons, List.filter_cons, List.length_cons, List.range'_succ]
    split_ifs <;> simp [zipIdx_filter_length p l (n + 1)]

theorem denseLabels_length {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (U : ℕ) :
    (denseLabels D U).length = cnt D.flatten.length U := by
  unfold denseLabels cnt
  rw [List.length_map, zipIdx_filter_length, List.range_eq_range']

/-! ## Magnitudes -/

/-- Every dense child has magnitude `Σ|w_i| + |t|` below `2^h`. -/
def DenseFit {w : ℕ} (h : ℕ) (D : List (List (ExactThresholdGate (w + w)))) : Prop :=
  ∀ e ∈ D.flatten, (∑ i, |e.weight i|) + |e.target| < 2 ^ h

theorem eqOf_bound {w : ℕ} (h : ℕ) (e : ExactThresholdGate (w + w)) (he : (∑ i, |e.weight i|) + |e.target| < 2 ^ h) :
    (∀ i, |(eqOf e).weights i| ≤ 2 ^ h - 1) ∧ |(eqOf e).target| ≤ 2 ^ h - 1 := by
  have hs : ∀ j, |e.weight j| ≤ ∑ i, |e.weight i| := fun j =>
    Finset.single_le_sum (f := fun i => |e.weight i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hs0 : 0 ≤ ∑ i, |e.weight i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨fun i => ?_, ?_⟩
  · rcases i with i | i
    · have := hs (Fin.castAdd w i)
      have := abs_nonneg e.target
      show |e.weight (Fin.castAdd w i)| ≤ _
      omega
    · have := hs (Fin.natAdd w i)
      have := abs_nonneg e.target
      show |e.weight (Fin.natAdd w i)| ≤ _
      omega
  · show |e.target| ≤ _
    omega

/-- **Every child's value is below `H = 2^h`** at every center assignment (alg:stack's hypothesis). -/
theorem synOf_abs_le {w : ℕ} (h : ℕ) (e : ExactThresholdGate (w + w))
    (he : (∑ i, |e.weight i|) + |e.target| < 2 ^ h) (aL aR : ℕ) :
    |(synOf e).value aL aR| ≤ 2 ^ h - 1 := by
  rw [synOf_value]
  unfold LabelledEquation.difference LabelledEquation.score
  have h1 : |∑ index, (eqOf e).weights index * bitInt (RowBinLift.assignment aL aR index)| ≤
      ∑ index, |(eqOf e).weights index| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    cases RowBinLift.assignment aL aR i <;> simp [bitInt]
  have h2 : ∑ index, |(eqOf e).weights index| = ∑ i, |e.weight i| := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_add]
    rfl
  have h3 := abs_sub (∑ index, (eqOf e).weights index * bitInt (RowBinLift.assignment aL aR index)) (eqOf e).target
  have h4 : |(eqOf e).target| = |e.target| := rfl
  omega

/-- A stack of `t` equations with fields below `H` has fields of magnitude at most `H^t − 1`. -/
theorem stack_bound {w : ℕ} (H : ℤ) (hH : 1 ≤ H) : ∀ es : List (RowBinLift.Equation w w),
    (∀ e ∈ es, (∀ i, |e.weights i| ≤ H - 1) ∧ |e.target| ≤ H - 1) →
      (∀ i, |(SupplierPipeline.stackEquations H es).weights i| ≤ H ^ es.length - 1) ∧
        |(SupplierPipeline.stackEquations H es).target| ≤ H ^ es.length - 1
  | [], _ => by simp [SupplierPipeline.stackEquations]
  | e :: es, h => by
    obtain ⟨ih1, ih2⟩ := stack_bound H hH es (fun e' he' => h e' (List.mem_cons_of_mem e he'))
    obtain ⟨he1, he2⟩ := h e List.mem_cons_self
    have key : ∀ a b : ℤ, |a| ≤ H - 1 → |b| ≤ H ^ es.length - 1 → |a + H * b| ≤ H ^ (e :: es).length - 1 := by
      intro a b ha hb
      have hHb : |H * b| = H * |b| := by rw [abs_mul, abs_of_nonneg (by omega)]
      have hmul : H * |b| ≤ H * (H ^ es.length - 1) := mul_le_mul_of_nonneg_left hb (by omega)
      have := abs_add_le a (H * b)
      rw [List.length_cons, pow_succ]
      nlinarith
    exact ⟨fun i => key _ _ (he1 i) (ih1 i), key _ _ he2 ih2⟩

theorem occCut_fits {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (h Q d p : ℕ) (hQ : 1 ≤ Q)
    (hD : DenseFit h D) (hp : h * Q * d ≤ p) (c : ℤ) (s : ℤ) (hs : s.natAbs = 1) (hc : c.natAbs * 2 ^ Q ≤ 2 ^ p)
    (poly : F2Poly ℕ) (hpoly : ∀ mono ∈ poly, mono.length ≤ d) (e : ℕ × ℕ)
    (he : e ∈ unionsM Q (oddMasksM (shapeOf D) poly)) :
    EquationRow.Fits p (occCut D (2 ^ h) (c * s) e) := by
  obtain ⟨hk, hcnt⟩ := unionsM_cnt D.flatten.length Q d _
    (oddMasksM_cnt (shapeOf D) D.flatten.length d poly hpoly) e he
  set es := (denseLabels D e.2).map eqOf
  have hlen : es.length ≤ Q * d := by
    simp only [es, List.length_map, denseLabels_length]
    exact hcnt.trans (Nat.mul_le_mul_right d hk)
  have hb := stack_bound (w := w) (2 ^ h) (one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)) es (by
    intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    refine eqOf_bound h x (hD x ?_)
    simp only [denseLabels] at hx
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hx
    exact List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hec).1)
  have hpow : ((2 : ℤ) ^ h) ^ es.length ≤ 2 ^ p := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) ((Nat.mul_le_mul_left h hlen).trans (by rw [← Nat.mul_assoc]; exact hp))
  have fit : ∀ x : ℤ, |x| ≤ ((2 : ℤ) ^ h) ^ es.length - 1 → x.natAbs < 2 ^ p := by
    intro x hx
    have : (x.natAbs : ℤ) < ((2 ^ p : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat]
      omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [occCut, RowBinLift.split, List.mem_append, List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact fit _ (hb.1 _)
    · exact fit _ (hb.1 _)
  · exact fit _ hb.2
  · show (c * s * (-2) ^ (e.1 - 1)).natAbs < 2 ^ p
    have h2abs : (-2 : ℤ).natAbs = 2 := rfl
    rw [Int.natAbs_mul, Int.natAbs_mul, hs, Int.natAbs_pow, h2abs, Nat.mul_one]
    by_cases hc0 : c.natAbs = 0
    · rw [hc0, Nat.zero_mul]
      exact Nat.two_pow_pos p
    · have h2 : 2 ^ (e.1 - 1) < 2 ^ Q := Nat.pow_lt_pow_right (by norm_num) (by omega)
      calc c.natAbs * 2 ^ (e.1 - 1) < c.natAbs * 2 ^ Q := Nat.mul_lt_mul_of_pos_left h2 (by omega)
        _ ≤ 2 ^ p := hc

end NearCubicWires.WireExponent3_5.CompilerMachine.Req
