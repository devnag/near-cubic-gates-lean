import Bindings.CLW20_Lemma3_8_Base

/-! # CLW20 Lemma 3.8, Appendix A: Case 2

CLW20 (ECCC TR20-150), Appendix A, PDF pp.50–52, printed pp.49–51 (with `k + 1` here in place of
the paper's `k`, so the paper's `ε_k` is `xorEpsilon δ (k+1)` and its `ε_{k−1}` is `xorEpsilon δ k`):

> "Case 2. Otherwise, we have that for all y ∈ {0,1}^n: |Pr_z[f^{⊕k}(y,z) = C(y,z)] − 1/2| ≤
> ε_k/(1 − δ)."

> "Setting ℓ = O(n/(δε_k)^2), and applying a Chernoff bound, [...] By a union bound, we can fix an
> assignment Z_i = z_i for each of Z_i such that |T(y) − T̃(y)| ≤ δε_k/(2(1 − δ)) (27) holds, for
> all y ∈ {0,1}^n."

> "Letting r := (2ε_k + δε_k)/(1 − δ), we define: P̃(y) := (T̃(y) − 1/2)/r + 1/2. Note that
> P̃(y) ∈ [0,1] since |T̃(y) − 1/2| ≤ r/2."

> "... = (2 − δ)/(2 + δ) = 1 − 2δ/(2 + δ) ≥ 1 − δ. (29)"

> "Finally, we use the samples {(z_i, f^{⊕(k−1)}(z_i))}, to construct a Sum ◦ C circuit Q as
> follows: Q(y) := (Pr_i[f^{⊕(k−1)}(z_i) ≠ C(y,z_i)] − 1/2)/r + 1/2. Note that Q can be implemented
> as a sum of ℓ + 1 C circuits (one for the constant function 1), as f^{⊕(k−1)}(z_i) can all be
> replaced by the corresponding constants."

> "Q(y) = P̃(y) if f(y) = 1, 1 − P̃(y) if f(y) = 0. From the above, one can see that for all y, we
> have Q(y) − f = P̃(y) − 1. [...] ‖Q − f‖_1 ≤ E_y[1 − P̃(y)] ≤ δ. Also, since P̃(y) ∈ [0,1] for all
> y, Q(y) ∈ [0,1] for all y as well."

In Lean: `ℓ = sampleCount δ n (k+1)` (the explicit count fixed by the import's `SampleForm`), the
samples come from `exists_sample_at_level`, the atom `sampleAtom C b_i z_i` is
`y ↦ f^{⊕(k−1)}(z_i) ⊕ C(y,z_i)` (the indicator `[f^{⊕(k−1)}(z_i) ≠ C(y,z_i)]`, a restriction or a
negated restriction of `C`), `1/r = alphaQ δ (k+1)`, and the term list is exactly
`SampleForm.affine (k+1)`: each atom with coefficient `α/ℓ`, plus the constant function 1 with
coefficient `(1 − α)/2`. `pointwise_value` is "Q(y) = P̃(y) or 1 − P̃(y)" together with
"P̃(y) ∈ [0,1]", `alpha_band` is "|T̃(y) − 1/2| ≤ r/2", and `final_bound` is (29). The printed
hypothesis "at least 1/2 + ε_k" is taken strictly, as in the import. -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `ε_k/(1 − δ) = ε_{k−1}`, written as `ε_{k+1} = (1 − δ)·ε_k` for `k ≥ 1`. -/
theorem xorEpsilon_succ (d : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    xorEpsilon d (k + 1) = (1 - d) * xorEpsilon d k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [xorEpsilon, Nat.add_sub_cancel]
  ring

/-- "P̃(y) ∈ [0,1] since |T̃(y) − 1/2| ≤ r/2": with `1/r = α`, `α·(τ + ε_{k−1}) = 1/2`. -/
theorem alpha_band (d ek alpha : ℝ) (halpha : alpha * ((2 + d) * ek) = 1) :
    alpha * (d * ek / 2 + ek) = 1 / 2 := by
  linear_combination (1 / 2 : ℝ) * halpha

/-- (29): `1/2 − α·(ε_k − τ) = 2δ/(2 + δ) ≤ δ`. -/
theorem final_bound (d ek alpha : ℝ) (hd0 : 0 < d) (halpha : alpha * ((2 + d) * ek) = 1) :
    1 / 2 - alpha * ((1 - d) * ek - d * ek / 2) ≤ d := by
  have key : (2 + d) * (1 / 2 - alpha * ((1 - d) * ek - d * ek / 2)) = 2 * d := by
    linear_combination (-(1 - 3 * d / 2)) * halpha
  have h2 : 0 < 2 + d := by linarith
  nlinarith [key, sq_nonneg d]

/-- "Q(y) = P̃(y) if f(y) = 1, 1 − P̃(y) if f(y) = 0", with `P̃(y) ∈ [0,1]`, so
`|Q(y) − f(y)| = 1 − P̃(y)`. -/
theorem pointwise_value (alpha t : ℝ) (fy : Bool) (halpha : 0 ≤ alpha)
    (hband : alpha * |t - 1 / 2| ≤ 1 / 2) :
    0 ≤ alpha * (if fy = true then t else 1 - t) + (1 - alpha) / 2 ∧
    alpha * (if fy = true then t else 1 - t) + (1 - alpha) / 2 ≤ 1 ∧
    |alpha * (if fy = true then t else 1 - t) + (1 - alpha) / 2 - bitAsReal fy| =
      1 / 2 - alpha * (t - 1 / 2) := by
  have hb : |alpha * (t - 1 / 2)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg halpha]
    exact hband
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have hb0 : bitAsReal false = 0 := by simp [bitAsReal]
  have hb1 : bitAsReal true = 1 := by simp [bitAsReal]
  cases fy
  · rw [if_neg (by decide), hb0, sub_zero]
    have hV : alpha * (1 - t) + (1 - alpha) / 2 = 1 / 2 - alpha * (t - 1 / 2) := by ring
    rw [hV, abs_of_nonneg (by linarith)]
    exact ⟨by linarith, by linarith, rfl⟩
  · rw [if_pos rfl, hb1]
    have hV : alpha * t + (1 - alpha) / 2 = 1 / 2 + alpha * (t - 1 / 2) := by ring
    rw [hV, abs_of_nonpos (by linarith)]
    exact ⟨by linarith, by linarith, by ring⟩

/-- The ℓ1 budget of (29), summed over the cube (`S = Σ_y T(y)`, `St = Σ_y T̃(y)`). -/
theorem l1_budget (N alpha agr S St c d e : ℝ) (hN : 0 ≤ N) (halpha : 0 ≤ alpha)
    (hS : S = agr * N) (hSt : S - N * c ≤ St) (hagr : 1 / 2 + e < agr)
    (hfin : 1 / 2 - alpha * (e - c) ≤ d) :
    N * (1 / 2 + alpha / 2) - alpha * St ≤ d * N := by
  have P1 : alpha * (S - N * c) ≤ alpha * St := mul_le_mul_of_nonneg_left hSt halpha
  have P2 : alpha * N * (1 / 2 + e) ≤ alpha * N * agr :=
    mul_le_mul_of_nonneg_left hagr.le (mul_nonneg halpha hN)
  have P3 : N * (1 / 2 - alpha * (e - c)) ≤ N * d := mul_le_mul_of_nonneg_left hfin hN
  rw [hS] at P1
  nlinarith [P1, P2, P3]

/-- The indicator `[C(y,z) = G(y,z)]` whose mean over `z` is `T(y)`. -/
def fiberTest {n k : ℕ} (C G : BoolFunction ((k + 1) * n)) (y : BitInput n)
    (z : BitInput (k * n)) : Bool :=
  decide (C (joinInput y z) = G (joinInput y z))

/-- `T̃(y)`: the empirical mean over the samples. -/
noncomputable def empiricalMean {α : Type*} {ell : ℕ} (h : α → Bool) (zs : Fin ell → α) : ℝ :=
  (∑ i, bitAsReal (h (zs i))) / (ell : ℝ)

/-- The atom `y ↦ b ⊕ C(y,z)`, i.e. `[b ≠ C(y,z)]` with `b = f^{⊕(k−1)}(z)`. -/
def sampleAtom {n k : ℕ} (C : BoolFunction ((k + 1) * n)) (b : Bool) (z : BitInput (k * n)) :
    BoolFunction n :=
  fun y => xor b (C (joinInput y z))

theorem atom_relation (fy b c : Bool) :
    bitAsReal (xor b c) = if fy = true then bitAsReal (decide (c = xor fy b))
      else 1 - bitAsReal (decide (c = xor fy b)) := by
  cases fy <;> cases b <;> cases c <;> simp [bitAsReal]

/-- The atoms average to `T̃(y)` if `f(y) = 1` and to `1 − T̃(y)` if `f(y) = 0`. -/
theorem atom_average {n k ell : ℕ} (hell : 0 < ell) (f : BoolFunction n)
    (C : BoolFunction ((k + 1) * n)) (zs : Fin ell → BitInput (k * n)) (y : BitInput n) :
    (∑ i, bitAsReal (sampleAtom C (xorPower f k (zs i)) (zs i) y)) / (ell : ℝ) =
      if f y = true then empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs
      else 1 - empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs := by
  have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hrel : ∀ i, bitAsReal (sampleAtom C (xorPower f k (zs i)) (zs i) y) =
      if f y = true then bitAsReal (fiberTest C (xorPower f (k + 1)) y (zs i))
      else 1 - bitAsReal (fiberTest C (xorPower f (k + 1)) y (zs i)) := by
    intro i
    unfold sampleAtom fiberTest
    rw [xorPower_join]
    exact atom_relation (f y) (xorPower f k (zs i)) (C (joinInput y (zs i)))
  by_cases hfy : f y = true
  · rw [if_pos hfy]
    unfold empiricalMean
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hrel i, if_pos hfy])
  · rw [if_neg hfy]
    have hneg' : ∀ i, bitAsReal (sampleAtom C (xorPower f k (zs i)) (zs i) y) =
        1 - bitAsReal (fiberTest C (xorPower f (k + 1)) y (zs i)) := fun i => by
      rw [hrel i, if_neg hfy]
    rw [Finset.sum_congr rfl (fun i _ => hneg' i)]
    unfold empiricalMean
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [sub_div, div_self hell']

/-- Case 2 of Appendix A at level `k + 1`. -/
theorem case_two_step (delta : ℚ) (h0 : 0 < delta) (h1 : delta < 1 / 2)
    {family : SizedFunctionFamily} (hproj : LiteralProjectionClosed family)
    (hneg : NegationClosedFamily family) {n k : ℕ} (hk : 1 ≤ k) (f : BoolFunction n) (size : ℕ)
    (C : BoolFunction ((k + 1) * n)) (hC : family ((k + 1) * n) C size)
    (hagree : 1 / 2 + xorEpsilon (delta : ℝ) (k + 1) < agreement C (xorPower f (k + 1)))
    (hall : ∀ y, |fiberAgreement C (xorPower f (k + 1)) y - 1 / 2| ≤ xorEpsilon (delta : ℝ) k) :
    Nonempty (SampledXorSum family delta n (k + 1) size f) := by
  have hd0 : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast h0
  have hd1 : (delta : ℝ) < 1 / 2 := by
    have h : ((delta : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa using h
  have hq : (0 : ℝ) < 1 - (delta : ℝ) := by linarith
  have hq' : (1 : ℝ) - (delta : ℝ) ≠ 0 := hq.ne'
  have h2d : (0 : ℝ) < 2 + (delta : ℝ) := by linarith
  have hek : 0 < xorEpsilon (delta : ℝ) k := xorEpsilon_pos hd1 k
  have he : xorEpsilon (delta : ℝ) (k + 1) = (1 - (delta : ℝ)) * xorEpsilon (delta : ℝ) k :=
    xorEpsilon_succ (delta : ℝ) hk
  -- `α = 1/r`
  have halpha : ((alphaQ delta (k + 1) : ℚ) : ℝ) * ((2 + (delta : ℝ)) * xorEpsilon (delta : ℝ) k) = 1 := by
    rw [alphaQ_cast, he, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)]
    ring
  have halpha0 : (0 : ℝ) < ((alphaQ delta (k + 1) : ℚ) : ℝ) := by
    rw [alphaQ_cast, he]
    exact div_pos hq (mul_pos h2d (mul_pos hq hek))
  -- the tolerance of (27)
  have htau : (delta : ℝ) * xorEpsilon (delta : ℝ) (k + 1) / (2 * (1 - (delta : ℝ))) =
      (delta : ℝ) * xorEpsilon (delta : ℝ) k / 2 := by
    rw [he, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  -- (27): the samples
  have hellpos := sampleCount_pos delta h0 h1 n (k + 1)
  obtain ⟨zs, hzs⟩ := exists_sample_at_level delta h0 h1 n (k + 1)
    (fiberTest C (xorPower f (k + 1)))
  have hclose : ∀ y, |empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs -
      fiberAgreement C (xorPower f (k + 1)) y| ≤ (delta : ℝ) * xorEpsilon (delta : ℝ) k / 2 := by
    intro y
    have h := hzs y
    have hm : mean (fiberTest C (xorPower f (k + 1)) y) = fiberAgreement C (xorPower f (k + 1)) y :=
      (fiberAgreement_eq_mean C (xorPower f (k + 1)) y).symm
    rw [hm, htau] at h
    exact h
  -- "|T̃(y) − 1/2| ≤ r/2"
  have hband : ∀ y, ((alphaQ delta (k + 1) : ℚ) : ℝ) *
      |empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs - 1 / 2| ≤ 1 / 2 := by
    intro y
    have htri : |empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs - 1 / 2| ≤
        (delta : ℝ) * xorEpsilon (delta : ℝ) k / 2 + xorEpsilon (delta : ℝ) k := by
      calc |empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs - 1 / 2|
          = |(empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs -
              fiberAgreement C (xorPower f (k + 1)) y) +
            (fiberAgreement C (xorPower f (k + 1)) y - 1 / 2)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (hclose y) (hall y)
    calc ((alphaQ delta (k + 1) : ℚ) : ℝ) *
          |empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs - 1 / 2|
        ≤ ((alphaQ delta (k + 1) : ℚ) : ℝ) *
          ((delta : ℝ) * xorEpsilon (delta : ℝ) k / 2 + xorEpsilon (delta : ℝ) k) :=
          mul_le_mul_of_nonneg_left htri halpha0.le
      _ = 1 / 2 := alpha_band _ _ _ halpha
  -- the atoms and the constant function 1
  let atoms : Fin (sampleCount delta n (k + 1)) → BoolFunction n :=
    fun i => sampleAtom C (xorPower f k (zs i)) (zs i)
  have hatoms : ∀ i, family n (atoms i) size := fun i =>
    family_xor (family := family) (size := size) hneg
      (family_fixRest (family := family) hproj hC (zs i)) (xorPower f k (zs i))
  have hone : family n (fun _ => true) size := family_one (family := family) hproj hneg hC
  -- Q(y), from the imported `foldl` value
  have hval : ∀ y : BitInput n, ((List.ofFn atoms).map
        (fun g => (alphaQ delta (k + 1) / (List.ofFn atoms).length, g)) ++
        [((1 - alphaQ delta (k + 1)) / 2, fun _ : BitInput n => true)]).foldl
      (fun total term => total + (term.1 : ℝ) * bitAsReal (term.2 y)) 0 =
      ((alphaQ delta (k + 1) : ℚ) : ℝ) *
        (if f y = true then empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs
          else 1 - empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs) +
        (1 - ((alphaQ delta (k + 1) : ℚ) : ℝ)) / 2 := by
    intro y
    rw [sampled_value hellpos (alphaQ delta (k + 1)) atoms (fun _ => true) (fun _ => rfl) y]
    rw [atom_average hellpos f C zs y]
  have hpt := fun y => pointwise_value ((alphaQ delta (k + 1) : ℚ) : ℝ)
    (empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs) (f y) halpha0.le (hband y)
  let s : UnitIntervalCircuitSum family n size :=
    { terms := (List.ofFn atoms).map
          (fun g => (alphaQ delta (k + 1) / (List.ofFn atoms).length, g)) ++
          [((1 - alphaQ delta (k + 1)) / 2, fun _ : BitInput n => true)]
      legal := by
        intro term hterm
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hterm
        rcases hterm with ⟨a, ha, rfl⟩ | rfl
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
          exact hatoms i
        · exact hone
      inUnitInterval := by
        intro y
        rw [hval y]
        exact ⟨(hpt y).1, (hpt y).2.1⟩ }
  refine ⟨{ sum := s,
            form := SampleForm.affine (k + 1) (by omega) le_rfl (List.ofFn atoms)
              (List.length_ofFn) (fun _ => true) (fun _ => rfl),
            close := ?_ }⟩
  -- ‖Q − f‖_1 ≤ δ
  have hsv : ∀ y, |s.value y - bitAsReal (f y)| =
      (1 / 2 + ((alphaQ delta (k + 1) : ℚ) : ℝ) / 2) - ((alphaQ delta (k + 1) : ℚ) : ℝ) *
        empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs := by
    intro y
    have h := (hpt y).2.2
    rw [← hval y] at h
    exact h.trans (by ring)
  have hN : (0 : ℝ) < (Fintype.card (BitInput n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold l1DistanceFromBoolean
  rw [div_le_iff₀ hN]
  simp only [hsv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hS : (∑ y, fiberAgreement C (xorPower f (k + 1)) y) =
      agreement C (xorPower f (k + 1)) * (Fintype.card (BitInput n) : ℝ) := by
    rw [agreement_eq_average C (xorPower f (k + 1)), div_mul_cancel₀ _ hN.ne']
  have hSt : (∑ y, fiberAgreement C (xorPower f (k + 1)) y) -
      (Fintype.card (BitInput n) : ℝ) * ((delta : ℝ) * xorEpsilon (delta : ℝ) k / 2) ≤
      ∑ y, empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs := by
    have hlow : ∀ y, fiberAgreement C (xorPower f (k + 1)) y -
        (delta : ℝ) * xorEpsilon (delta : ℝ) k / 2 ≤
        empiricalMean (fiberTest C (xorPower f (k + 1)) y) zs := fun y => by
      have := (abs_le.mp (hclose y)).1
      linarith
    have h := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (BitInput n))) => hlow y)
    rw [Finset.sum_sub_distrib] at h
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hagr : 1 / 2 + (1 - (delta : ℝ)) * xorEpsilon (delta : ℝ) k <
      agreement C (xorPower f (k + 1)) := by
    rw [← he]
    exact hagree
  have hfin := final_bound (delta : ℝ) (xorEpsilon (delta : ℝ) k)
    ((alphaQ delta (k + 1) : ℚ) : ℝ) hd0 halpha
  have hb := l1_budget (Fintype.card (BitInput n) : ℝ) ((alphaQ delta (k + 1) : ℚ) : ℝ)
    (agreement C (xorPower f (k + 1))) _ _ ((delta : ℝ) * xorEpsilon (delta : ℝ) k / 2)
    (delta : ℝ) ((1 - (delta : ℝ)) * xorEpsilon (delta : ℝ) k) hN.le halpha0.le hS hSt hagr hfin
  linarith

end NearCubicWires.Bindings.CLW20Lemma38
