import Proof.Foundations.RepresentationSourceContracts

/-! Exact numeric bounds of the CLW sampled affine sum. No sampling,
coefficient-resource or published-contract premise is assumed here. -/
namespace NearCubicWires.RepairXor
open SourceInterfaces ExecutableInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem radius_cast_half (delta : ℚ) (hh : delta < 1 / 2) : (delta : ℝ) < 1 / 2 := by
  have hq : (2 : ℚ) * delta < 1 := by linarith
  have hr : (2 : ℝ) * (delta : ℝ) < 1 := by exact_mod_cast hq
  linarith

theorem epsilon_positive (delta : ℝ) (hd : 0 < delta) (hh : delta < 1 / 2) (k : ℕ) :
    0 < xorEpsilon delta k := by
  unfold xorEpsilon
  exact mul_pos (pow_pos (by linarith) _) (by linarith)

theorem epsilon_le_half (delta : ℝ) (hd : 0 < delta) (hh : delta < 1 / 2) (k : ℕ) :
    xorEpsilon delta k ≤ 1 / 2 := by
  have hp : (1 - delta) ^ (k - 1) ≤ (1 : ℝ) :=
    pow_le_one₀ (by linarith) (by linarith)
  unfold xorEpsilon
  nlinarith

theorem epsilon_antitone (delta : ℝ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {j k : ℕ} (hjk : j ≤ k) : xorEpsilon delta k ≤ xorEpsilon delta j := by
  unfold xorEpsilon
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  exact pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)

theorem epsilonQ_coe (delta : ℚ) (j : ℕ) :
    (epsilonQ delta j : ℝ) = xorEpsilon (delta : ℝ) j := by
  simp [epsilonQ, xorEpsilon]

theorem alphaQ_coe (delta : ℚ) (j : ℕ) :
    (alphaQ delta j : ℝ) =
      (1 - (delta : ℝ)) / ((2 + (delta : ℝ)) * xorEpsilon (delta : ℝ) j) := by
  simp [alphaQ, epsilonQ_coe]

theorem sampleCount_positive (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (n j : ℕ) : 0 < sampleCount delta n j := by
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hhr := radius_cast_half delta hh
  have he := epsilon_positive (delta : ℝ) hdr hhr j
  unfold sampleCount
  apply Nat.ceil_pos.mpr
  positivity

theorem sampleCount_add_one_le_terms (delta : ℚ) (hd : 0 < delta)
    (hh : delta < 1 / 2) {n j k : ℕ} (hn : 1 ≤ n) (hjk : j ≤ k) :
    sampleCount delta n j + 1 ≤ xorTermBound delta n k := by
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hhr := radius_cast_half delta hh
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hej := epsilon_positive (delta : ℝ) hdr hhr j
  have hek := epsilon_positive (delta : ℝ) hdr hhr k
  have hejHalf := epsilon_le_half (delta : ℝ) hdr hhr j
  have hden : 0 < (delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2 := by positivity
  have hdenOne : (delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2 ≤ 1 := by
    have hd2 : (delta : ℝ) ^ 2 ≤ 1 := by nlinarith
    have he2 : xorEpsilon (delta : ℝ) j ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hd2) (sub_nonneg.mpr he2)]
  have hceil := Nat.ceil_lt_add_one (show
    0 ≤ 4 * ((n + 1 : ℕ) : ℝ) /
      ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) by positivity)
  have hsmall : (sampleCount delta n j : ℝ) + 1 ≤
      16 * (n : ℝ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) := by
    change (sampleCount delta n j : ℝ) < _ at hceil
    have hratio : 4 * ((n + 1 : ℕ) : ℝ) /
        ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) + 2 ≤
          16 * (n : ℝ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2) := by
      apply (le_div_iff₀ hden).2
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
      push_cast
      nlinarith
    linarith
  have hdenMono : (delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) k ^ 2 ≤
      (delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (le_of_lt hek) (epsilon_antitone _ hdr hhr hjk) 2
  have hfinal : (sampleCount delta n j : ℝ) + 1 ≤
      (xorTermBound delta n k : ℝ) := by
    exact hsmall.trans ((div_le_div_of_nonneg_left (by positivity) (by positivity) hdenMono).trans
      (Nat.le_ceil _))
  exact_mod_cast hfinal

theorem one_le_terms (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {n k : ℕ} (hn : 1 ≤ n) : 1 ≤ xorTermBound delta n k := by
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hhr := radius_cast_half delta hh
  have he := epsilon_positive (delta : ℝ) hdr hhr k
  unfold xorTermBound
  apply Nat.one_le_ceil_iff.mpr
  positivity

theorem affine_mass_scalar (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    (j : ℕ) : |(alphaQ delta j : ℝ)| + |(((1 - alphaQ delta j) / 2 : ℚ) : ℝ)| ≤
      1 / xorEpsilon (delta : ℝ) j := by
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hhr := radius_cast_half delta hh
  have he := epsilon_positive (delta : ℝ) hdr hhr j
  have heHalf := epsilon_le_half (delta : ℝ) hdr hhr j
  have ha : 0 ≤ (alphaQ delta j : ℝ) := by
    rw [alphaQ_coe]
    exact div_nonneg (by linarith) (by positivity)
  have halpha : (alphaQ delta j : ℝ) ≤ 1 / (2 * xorEpsilon (delta : ℝ) j) := by
    rw [alphaQ_coe]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have habs : |1 - (alphaQ delta j : ℝ)| ≤ 1 + (alphaQ delta j : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hi : (1 : ℝ) ≤ 1 / (2 * xorEpsilon (delta : ℝ) j) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  push_cast
  rw [abs_of_nonneg ha, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hid : (1 : ℝ) / xorEpsilon (delta : ℝ) j =
      2 * (1 / (2 * xorEpsilon (delta : ℝ) j)) := by field_simp
  rw [hid]
  linarith

theorem mass_map_append {n : ℕ} (atoms : List (BoolFunction n))
    (coefficient constant : ℚ) (one : BoolFunction n) :
    ((atoms.map (fun f => (coefficient, f))) ++ [(constant, one)]).foldl
      (fun total term => total + |(term.1 : ℝ)|) 0 =
        (atoms.length : ℝ) * |(coefficient : ℝ)| + |(constant : ℝ)| := by
  have hfold : ∀ (xs : List (BoolFunction n)) (acc : ℝ),
      (xs.map (fun f => (coefficient, f))).foldl
        (fun total term => total + |(term.1 : ℝ)|) acc =
          acc + (xs.length : ℝ) * |(coefficient : ℝ)| := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih => intro acc; simp only [List.map_cons, List.foldl_cons, ih,
        List.length_cons, Nat.cast_add, Nat.cast_one]; ring
  simp only [List.foldl_append, hfold, zero_add, List.foldl_cons, List.foldl_nil]

theorem affine_mass (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {n j k : ℕ} (hjk : j ≤ k) (atoms : List (BoolFunction n))
    (hcount : atoms.length = sampleCount delta n j) (one : BoolFunction n) :
    ((atoms.map (fun f => (alphaQ delta j / atoms.length, f))) ++
      [((1 - alphaQ delta j) / 2, one)]).foldl
      (fun total term => total + |(term.1 : ℝ)|) 0 ≤ 1 / xorEpsilon (delta : ℝ) k := by
  have hlen : 0 < atoms.length := hcount ▸ sampleCount_positive delta hd hh n j
  have hlenR : (0 : ℝ) < atoms.length := by exact_mod_cast hlen
  have hdr : (0 : ℝ) < delta := by exact_mod_cast hd
  have hhr := radius_cast_half delta hh
  rw [mass_map_append]
  have hcancel : (atoms.length : ℝ) * |((alphaQ delta j / atoms.length : ℚ) : ℝ)| =
      |(alphaQ delta j : ℝ)| := by
    push_cast
    rw [abs_div, abs_of_pos hlenR]
    field_simp
  rw [hcancel]
  exact (affine_mass_scalar delta hd hh j).trans
    (one_div_le_one_div_of_le (epsilon_positive _ hdr hhr k) (epsilon_antitone _ hdr hhr hjk))

end NearCubicWires.RepairXor
