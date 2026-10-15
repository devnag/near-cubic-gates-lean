import Proof.Wire_3_5.GFRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial NearCubicWires.WireExponent3_5.GF2

/-! ## Carry-less multiply and reduce -/

/-- One step of the carry-less multiplier `clmul`. -/
def clStep (x y : ℕ) (acc i : ℕ) : ℕ := if y.testBit i then acc ^^^ (x <<< i) else acc

theorem clmul_eq (x y w : ℕ) : clmul x y w = (List.range w).foldl (clStep x y) 0 := rfl

theorem shiftLeft_lt (x ℓ i : ℕ) (hx : x < 2 ^ ℓ) : x <<< i < 2 ^ (ℓ + i) := by
  rw [Nat.shiftLeft_eq, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos i)

/-- **Carry-less multiplication is the polynomial product** (of `x` and the low `w` bits of `y`). -/
theorem clmul_spec (x y ℓ : ℕ) (hx : x < 2 ^ ℓ) :
    ∀ w, clmul x y w < 2 ^ (ℓ + w) ∧ toPoly (clmul x y w) = toPoly x * toPoly (y % 2 ^ w)
  | 0 => by simp [clmul_eq, Nat.mod_one]
  | w + 1 => by
    obtain ⟨h1, h2⟩ := clmul_spec x y ℓ hx w
    rw [clmul_eq] at h1 h2 ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hmono : 2 ^ (ℓ + w) ≤ 2 ^ (ℓ + (w + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set acc := List.foldl (clStep x y) 0 (List.range w) with hacc
    rw [show clStep x y acc w = if y.testBit w then acc ^^^ (x <<< w) else acc from rfl]
    split_ifs with hb
    · refine ⟨Nat.xor_lt_two_pow (lt_of_lt_of_le h1 hmono) (lt_of_lt_of_le (shiftLeft_lt x ℓ w hx) hmono), ?_⟩
      rw [toPoly_xor, h2, toPoly_shiftLeft, toPoly_mod_two_pow_succ, if_pos hb]
      ring
    · refine ⟨lt_of_lt_of_le h1 hmono, ?_⟩
      rw [h2, toPoly_mod_two_pow_succ, if_neg hb, add_zero]

/-- One step of the reduction `reduce`. -/
def redStep (p ℓ : ℕ) (acc i : ℕ) : ℕ := if acc.testBit (i + ℓ) then acc ^^^ (p <<< i) else acc

theorem reduce_eq (p ℓ x : ℕ) : reduce p ℓ x = (List.range ℓ).reverse.foldl (redStep p ℓ) x := rfl

theorem reduce_gen (p ℓ : ℕ) (hp : ModulusOk p ℓ) :
    ∀ n acc, acc < 2 ^ (n + ℓ) →
      (List.range n).reverse.foldl (redStep p ℓ) acc < 2 ^ ℓ ∧
        rep p ((List.range n).reverse.foldl (redStep p ℓ) acc) = rep p acc
  | 0, acc, h => by simpa using h
  | n + 1, acc, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
    have h' : acc < 2 ^ (n + ℓ + 1) := by rwa [show n + ℓ + 1 = n + 1 + ℓ by omega]
    have hstep : redStep p ℓ acc n < 2 ^ (n + ℓ) ∧ rep p (redStep p ℓ acc n) = rep p acc := by
      unfold redStep
      split_ifs with hb
      · have hps : p <<< n < 2 ^ (n + ℓ + 1) := by
          have := shiftLeft_lt p (ℓ + 1) n hp.2
          rwa [show ℓ + 1 + n = n + ℓ + 1 by omega] at this
        have hbit : (p <<< n).testBit (n + ℓ) = true := by
          rw [Nat.testBit_shiftLeft]
          simp [show n + ℓ - n = ℓ by omega, hp.1]
        refine ⟨lt_two_pow_of_testBit_eq _ _ _ h' hps (by rw [hb, hbit]), ?_⟩
        rw [rep_xor]
        have : rep p (p <<< n) = 0 := by
          rw [rep, toPoly_shiftLeft, map_mul, AdjoinRoot.mk_self, mul_zero]
        rw [this, add_zero]
      · exact ⟨lt_of_testBit_false _ _ h' (by simpa using hb), rfl⟩
    obtain ⟨h1, h2⟩ := reduce_gen p ℓ hp n _ hstep.1
    exact ⟨h1, h2.trans hstep.2⟩

/-- **The reduction keeps the class and returns `ℓ` bits** (on inputs below `2^{2ℓ}`). -/
theorem reduce_spec (p ℓ x : ℕ) (hp : ModulusOk p ℓ) (hx : x < 2 ^ (ℓ + ℓ)) :
    reduce p ℓ x < 2 ^ ℓ ∧ rep p (reduce p ℓ x) = rep p x := by
  rw [reduce_eq]; exact reduce_gen p ℓ hp ℓ x hx

/-- **`fmul` is the field product.** -/
theorem fmul_spec (p ℓ x y : ℕ) (hp : ModulusOk p ℓ) (hx : x < 2 ^ ℓ) (hy : y < 2 ^ ℓ) :
    fmul p ℓ x y < 2 ^ ℓ ∧ rep p (fmul p ℓ x y) = rep p x * rep p y := by
  obtain ⟨h1, h2⟩ := clmul_spec x y ℓ hx ℓ
  obtain ⟨h3, h4⟩ := reduce_spec p ℓ _ hp h1
  unfold fmul
  refine ⟨h3, ?_⟩
  rw [h4, rep, h2, Nat.mod_eq_of_lt hy, map_mul]
  rfl

/-! ## The trace -/

/-- One step of the ref trace (accumulate, then square). -/
def trStep (p ℓ : ℕ) (st : ℕ × ℕ) (_i : ℕ) : ℕ × ℕ := (st.1 ^^^ st.2, fmul p ℓ st.2 st.2)

theorem trace_eq (p ℓ a : ℕ) : GF2.trace p ℓ a = ((List.range ℓ).foldl (trStep p ℓ) (0, a)).1 := rfl

theorem trace_fold (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) :
    ∀ n, ((List.range n).foldl (trStep p ℓ) (0, a)).1 < 2 ^ ℓ ∧
      ((List.range n).foldl (trStep p ℓ) (0, a)).2 < 2 ^ ℓ ∧
      rep p ((List.range n).foldl (trStep p ℓ) (0, a)).1 = ∑ i ∈ Finset.range n, rep p a ^ (2 ^ i) ∧
      rep p ((List.range n).foldl (trStep p ℓ) (0, a)).2 = rep p a ^ (2 ^ n)
  | 0 => by simp [ha]
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := trace_fold p ℓ a hp ha n
    obtain ⟨h5, h6⟩ := fmul_spec p ℓ _ _ hp h2 h2
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨Nat.xor_lt_two_pow h1 h2, h5, ?_, ?_⟩
    · show rep p (_ ^^^ _) = _
      rw [rep_xor, h3, h4, Finset.sum_range_succ]
    · show rep p (fmul p ℓ _ _) = _
      rw [h6, h4, ← pow_add, pow_succ]
      congr 1
      ring

theorem finrank_ref (p ℓ : ℕ) (hp : ModulusOk p ℓ) : Module.finrank (ZMod 2) (AdjoinRoot (toPoly p)) = ℓ := by
  rw [(AdjoinRoot.powerBasis' (toPoly_monic p ℓ hp)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_toPoly p ℓ hp]

/-- **The ref trace is the algebra trace**: `trace p ℓ a` represents `Σ_{i<ℓ} a^{2^i} = Tr(a)`. -/
theorem traceRef_spec (p ℓ a : ℕ) (hc : PrimitiveCert p ℓ) (ha : a < 2 ^ ℓ) :
    rep p (GF2.trace p ℓ a) = algebraMap (ZMod 2) _ (Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p)) (rep p a)) := by
  haveI := fact_irreducible p ℓ hc
  haveI : Finite (AdjoinRoot (toPoly p)) := Finite.of_equiv _ (encEquiv p ℓ hc.2.1)
  rw [FiniteField.algebraMap_trace_eq_sum_pow, finrank_ref p ℓ hc.2.1, Nat.card_zmod, trace_eq]
  exact (trace_fold p ℓ a hc.2.1 ha ℓ).2.2.1

theorem rep_val (p : ℕ) (t : ZMod 2) : rep p t.val = algebraMap (ZMod 2) (AdjoinRoot (toPoly p)) t := by
  fin_cases t
  · exact (rep_zero p).trans (map_zero _).symm
  · exact (rep_one p).trans (map_one _).symm

/-- The ref trace is the value of the algebra trace. -/
theorem traceRef_val (p ℓ a : ℕ) (hc : PrimitiveCert p ℓ) (ha : a < 2 ^ ℓ) :
    GF2.trace p ℓ a = (Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p)) (rep p a)).val := by
  have hp := hc.2.1
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hc.1
  have hb1 : GF2.trace p ℓ a < 2 ^ ℓ := by rw [trace_eq]; exact (trace_fold p ℓ a hp ha ℓ).1
  apply rep_injOn p ℓ _ _ hp hb1
  · have := ZMod.val_lt (Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p)) (rep p a)); omega
  · rw [traceRef_spec p ℓ a hc ha, rep_val]

/-! ## The masked parity -/

theorem testBit_tau_fold (p ℓ : ℕ) :
    ∀ n b, ((List.range n).foldl (fun m b => if GF2.trace p ℓ (2 ^ b) = 1 then m ||| 2 ^ b else m) 0).testBit b =
      decide (b < n ∧ GF2.trace p ℓ (2 ^ b) = 1)
  | 0, b => by simp
  | n + 1, b => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := testBit_tau_fold p ℓ n b
    split_ifs with h
    · rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
      by_cases hb : b = n
      · subst hb; simp [h]
      · have : n ≠ b := fun e => hb e.symm
        simp only [this, decide_false, Bool.or_false]
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rw [ih]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
        · exact h1
        · exact absurd h2 h

/-- The trace mask: bit `b` of `τ` is `Tr(x^b)`. -/
theorem testBit_tau (p ℓ b : ℕ) : (tau p ℓ).testBit b = decide (b < ℓ ∧ GF2.trace p ℓ (2 ^ b) = 1) :=
  testBit_tau_fold p ℓ ℓ b

theorem length_filter_cast (f : ℕ → Bool) :
    ∀ n, ((((List.range n).filter f).length : ℕ) : ZMod 2) = ∑ b ∈ Finset.range n, bitF (f b)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, Nat.cast_add, length_filter_cast f n,
      Finset.sum_range_succ]
    congr 1
    rw [List.filter_cons, List.filter_nil]
    unfold bitF
    cases h : f n <;> simp

/-- The masked parity as an element of `𝔽₂`. -/
theorem parityMasked_cast (mask a ℓ : ℕ) :
    (parityMasked mask a ℓ : ZMod 2) = ∑ b ∈ Finset.range ℓ, bitF (mask.testBit b && a.testBit b) := by
  unfold parityMasked
  rw [ZMod.natCast_mod, length_filter_cast]

theorem toPoly_eq_sum (a ℓ : ℕ) (ha : a < 2 ^ ℓ) :
    toPoly a = ∑ b ∈ Finset.range ℓ, C (bitF (a.testBit b)) * X ^ b := by
  ext i
  rw [coeff_toPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hi
  · rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by simp at hi; omega)))]
    rfl

/-- `a = Σ_b a_b x^b` in the field. -/
theorem rep_eq_sum (p a ℓ : ℕ) (ha : a < 2 ^ ℓ) :
    rep p a = ∑ b ∈ Finset.range ℓ, bitF (a.testBit b) • xRoot p ^ b := by
  rw [rep, toPoly_eq_sum a ℓ ha, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X, Algebra.smul_def]
  rfl

theorem bitF_and_trace (x : Bool) (t : ZMod 2) : bitF (decide (t.val = 1) && x) = bitF x * t := by
  fin_cases t <;> cases x <;> decide

/-- **The machine's trace bit is the field trace**: `⟨τ, a⟩ mod 2 = Tr(a)` for every `ℓ`-bit `a`. -/
theorem trace_masked (p ℓ a : ℕ) (hc : PrimitiveCert p ℓ) (ha : a < 2 ^ ℓ) :
    parityMasked (tau p ℓ) a ℓ = (Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p)) (rep p a)).val := by
  have hp := hc.2.1
  have hcast : (parityMasked (tau p ℓ) a ℓ : ZMod 2) = Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p)) (rep p a) := by
    rw [parityMasked_cast, rep_eq_sum p a ℓ ha, map_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_range] at hb
    have hb2 : 2 ^ b < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hb
    rw [testBit_tau, map_smul, smul_eq_mul, ← rep_two_pow, traceRef_val p ℓ (2 ^ b) hc hb2]
    simp only [hb, true_and]
    exact bitF_and_trace _ _
  have hlt : parityMasked (tau p ℓ) a ℓ < 2 := by unfold parityMasked; exact Nat.mod_lt _ (by norm_num)
  rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-! ## The trace character's hypothesis and the projection -/

/-- The absolute trace `𝔽₂[X]/(p) → 𝔽₂` as an additive map. -/
noncomputable def refTrace (p : ℕ) : AdjoinRoot (toPoly p) →+ ZMod 2 :=
  (Algebra.trace (ZMod 2) (AdjoinRoot (toPoly p))).toAddMonoidHom

/-- **The trace is nontrivial** (the hypothesis of `WireExponent3_5TraceBias` and of the base-filter bounds). -/
theorem refTrace_nontrivial (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : ∃ b, refTrace p b ≠ 0 := by
  haveI := fact_irreducible p ℓ hc
  haveI : Finite (AdjoinRoot (toPoly p)) := Finite.of_equiv _ (encEquiv p ℓ hc.2.1)
  haveI : Module.Finite (ZMod 2) (AdjoinRoot (toPoly p)) := (toPoly_monic p ℓ hc.2.1).finite_adjoinRoot
  have hne := (traceForm_nondegenerate (ZMod 2) (AdjoinRoot (toPoly p))).ne_zero
  by_contra hall
  simp only [not_exists, not_not] at hall
  apply hne
  ext a b
  simpa [Algebra.traceForm_apply, refTrace] using hall (a * b)

noncomputable def projK (p ℓ : ℕ) (hp : ModulusOk p ℓ) (k : ℕ) : AdjoinRoot (toPoly p) →+ (Fin k → ZMod 2) where
  toFun y b := (AdjoinRoot.modByMonicHom (toPoly_monic p ℓ hp) y).coeff b
  map_zero' := by funext b; simp
  map_add' y z := by funext b; simp [coeff_add]

/-- **The projection reads the low `k` bits.** -/
theorem projK_rep (p ℓ : ℕ) (hp : ModulusOk p ℓ) (k a : ℕ) (ha : a < 2 ^ ℓ) (b : Fin k) :
    projK p ℓ hp k (rep p a) b = bitF (a.testBit b) := by
  show (AdjoinRoot.modByMonicHom (toPoly_monic p ℓ hp) (AdjoinRoot.mk _ (toPoly a))).coeff b = _
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (toPoly_monic p ℓ hp)).mpr, coeff_toPoly]
  rw [degree_eq_natDegree (toPoly_monic p ℓ hp).ne_zero, natDegree_toPoly p ℓ hp]
  exact degree_toPoly_lt a ℓ ha

/-- **The projection is onto** `𝔽₂^k` for `k ≤ ℓ` (the hypothesis of `projectKWise`). -/
theorem projK_surjective (p ℓ : ℕ) (hp : ModulusOk p ℓ) (k : ℕ) (hk : k ≤ ℓ) :
    Function.Surjective (projK p ℓ hp k) := by
  intro w
  refine ⟨AdjoinRoot.mk _ (∑ i : Fin k, C (w i) * X ^ (i : ℕ)), ?_⟩
  funext b
  show (AdjoinRoot.modByMonicHom (toPoly_monic p ℓ hp) (AdjoinRoot.mk _ _)).coeff b = _
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (toPoly_monic p ℓ hp)).mpr]
  · rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      have : (b : ℕ) ≠ i := fun e => hi (Fin.ext e).symm
      simp [this]
    · simp
  · rw [degree_eq_natDegree (toPoly_monic p ℓ hp).ne_zero, natDegree_toPoly p ℓ hp]
    exact lt_of_lt_of_le (degree_sum_fin_lt _) (by exact_mod_cast hk)

end NearCubicWires.WireExponent3_5.GF
