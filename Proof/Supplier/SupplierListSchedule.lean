import Proof.Supplier.SupplierListPolynomial

/-!
# Concrete zero-advice list parameters

This file instantiates the graded windows from Appendix A.10.  Three
consecutive levels share one geometric scale; the constant `64` leaves an
explicit margin after the terminal Markov term.  The resulting base failure
is at most `1 / 128`, while the exact degree ledger remains linear in
`sqrt(activeBound) + depth`.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierListSchedule

open NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore

/-- The three-level geometric window schedule.  `Nat.ceil` is important:
rounding never weakens the concentration bound, and the additive constant
keeps every window strictly positive after the active mass has decayed. -/
noncomputable def gradedWindow
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) : ℕ :=
  ⌈(64 : ℝ) *
    (Real.sqrt activeBound /
      (2 : ℝ) ^ (level.val / 3) + 1)⌉₊

/-- The terminal count is required to vanish.  This contributes no polynomial
degree and is valid once the explicit terminal sparsity premise below holds. -/
def gradedTerminalWindow : ℕ := 0

theorem gradedWindow_pos
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) :
    0 < gradedWindow activeBound level := by
  unfold gradedWindow
  apply Nat.ceil_pos.mpr
  positivity

/-- Encode a level by its three-level block and residue.  This injection lets
us compare the finite graded sum with three copies of one geometric series. -/
def divThreeEmbedding {depth : ℕ} (level : Fin depth) :
    Fin depth × Fin 3 :=
  (⟨level.val / 3, lt_of_le_of_lt (Nat.div_le_self _ _) level.isLt⟩,
    ⟨level.val % 3, Nat.mod_lt _ (by omega)⟩)

theorem divThreeEmbedding_injective {depth : ℕ} :
    Function.Injective (@divThreeEmbedding depth) := by
  intro left right hequal
  apply Fin.ext
  have hdiv := congrArg (fun pair => pair.1.val) hequal
  have hmod := congrArg (fun pair => pair.2.val) hequal
  have hleft := Nat.div_add_mod left.val 3
  have hright := Nat.div_add_mod right.val 3
  dsimp [divThreeEmbedding] at hdiv hmod
  omega

theorem sum_inverse_pow_div_three_le (depth : ℕ) :
    (∑ level : Fin depth,
      1 / (2 : ℝ) ^ (level.val / 3)) ≤ 6 := by
  let embedding : Fin depth → Fin depth × Fin 3 :=
    divThreeEmbedding
  let weight : Fin depth × Fin 3 → ℝ :=
    fun pair => 1 / (2 : ℝ) ^ pair.1.val
  have hinjective : Function.Injective embedding :=
    divThreeEmbedding_injective
  calc
    (∑ level : Fin depth,
        1 / (2 : ℝ) ^ (level.val / 3)) =
        ∑ pair ∈ (Finset.univ.image embedding),
          weight pair := by
      rw [Finset.sum_image hinjective.injOn]
      rfl
    _ ≤ ∑ pair : Fin depth × Fin 3, weight pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro pair _ _
        dsimp [weight]
        positivity
    _ = ∑ block : Fin depth, ∑ _residue : Fin 3,
          1 / (2 : ℝ) ^ block.val := by
      rw [Fintype.sum_prod_type]
    _ = 3 * ∑ block : Fin depth,
          1 / (2 : ℝ) ^ block.val := by
      simp only [Fin.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      norm_num
    _ ≤ 3 * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range
        (fun index : ℕ => 1 / (2 : ℝ) ^ index) depth]
      simpa [one_div_pow] using sum_geometric_two_le depth
    _ = 6 := by norm_num

theorem gradedWindow_level_failure_le
    {depth : ℕ} (activeBound : ℕ) (level : Fin depth) :
    ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
        (gradedWindow activeBound level : ℝ) ^ 2 ≤
      (1 / 4096 : ℝ) *
        (1 / (2 : ℝ) ^ (level.val / 3)) := by
  by_cases hactive : activeBound = 0
  · subst activeBound
    norm_num
  let block := level.val / 3
  let window := gradedWindow activeBound level
  have hactiveReal : (0 : ℝ) < activeBound := by
    exact_mod_cast Nat.pos_of_ne_zero hactive
  have hpow : (0 : ℝ) < (2 : ℝ) ^ block := by positivity
  have hsqrt : (0 : ℝ) < Real.sqrt activeBound :=
    Real.sqrt_pos.2 hactiveReal
  have hceil :
      (64 : ℝ) *
          (Real.sqrt activeBound / (2 : ℝ) ^ block + 1) ≤
        (window : ℝ) := by
    exact Nat.le_ceil _
  have hwindowLower :
      (64 : ℝ) * Real.sqrt activeBound /
          (2 : ℝ) ^ block ≤
        (window : ℝ) := by
    calc
      (64 : ℝ) * Real.sqrt activeBound /
          (2 : ℝ) ^ block ≤
          (64 : ℝ) *
            (Real.sqrt activeBound / (2 : ℝ) ^ block + 1) := by
        ring_nf
        linarith
      _ ≤ (window : ℝ) := hceil
  have hwindowPositive : (0 : ℝ) < window := by
    exact_mod_cast gradedWindow_pos activeBound level
  have hsquare :
      ((64 : ℝ) * Real.sqrt activeBound /
          (2 : ℝ) ^ block) ^ 2 ≤
        (window : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hwindowPositive.le).2
      hwindowLower
  have hfirst :
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
          (window : ℝ) ^ 2 ≤
        ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
          ((64 : ℝ) * Real.sqrt activeBound /
            (2 : ℝ) ^ block) ^ 2 := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · exact hsquare
  have hidentity :
      ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
          ((64 : ℝ) * Real.sqrt activeBound /
            (2 : ℝ) ^ block) ^ 2 =
        (1 / 4096 : ℝ) *
          ((2 : ℝ) ^ (2 * block) / (2 : ℝ) ^ level.val) := by
    have hsqrtSquare :
        (Real.sqrt activeBound) ^ 2 = (activeBound : ℝ) :=
      Real.sq_sqrt hactiveReal.le
    have hpowSquare :
        ((2 : ℝ) ^ block) ^ 2 = (2 : ℝ) ^ (2 * block) := by
      rw [← pow_mul]
      congr 1
      omega
    field_simp [ne_of_gt hpow, ne_of_gt hsqrt]
    norm_num at *
    nlinarith [hsqrtSquare, hpowSquare]
  have hblock : 3 * block ≤ level.val := by
    dsimp [block]
    omega
  have hratio :
      (2 : ℝ) ^ (2 * block) / (2 : ℝ) ^ level.val ≤
        1 / (2 : ℝ) ^ block := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
        (gradedWindow activeBound level : ℝ) ^ 2 =
        ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
          (window : ℝ) ^ 2 := rfl
    _ ≤ ((activeBound : ℝ) * (1 / (2 : ℝ) ^ level.val)) /
          ((64 : ℝ) * Real.sqrt activeBound /
            (2 : ℝ) ^ block) ^ 2 := hfirst
    _ = (1 / 4096 : ℝ) *
          ((2 : ℝ) ^ (2 * block) / (2 : ℝ) ^ level.val) :=
      hidentity
    _ ≤ (1 / 4096 : ℝ) *
        (1 / (2 : ℝ) ^ block) := by
      gcongr

theorem gradedFailureBound_le
    (activeBound depth : ℕ)
    (hterminal : 256 * activeBound ≤ 2 ^ depth) :
    listFailureBound activeBound
        (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow ≤
      (1 : ℝ) / 128 := by
  have hterminalReal :
      ((activeBound : ℝ) / (2 : ℝ) ^ depth) ≤
        (1 : ℝ) / 256 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num
    exact_mod_cast (by simpa [Nat.mul_comm] using hterminal)
  have hlevels :
      (∑ level : Fin depth,
          (((activeBound : ℝ) *
              (1 / (2 : ℝ) ^ level.val)) /
            (gradedWindow activeBound level : ℝ) ^ 2)) ≤
        (6 : ℝ) / 4096 := by
    calc
      (∑ level : Fin depth,
          (((activeBound : ℝ) *
              (1 / (2 : ℝ) ^ level.val)) /
            (gradedWindow activeBound level : ℝ) ^ 2)) ≤
          ∑ level : Fin depth,
            (1 / 4096 : ℝ) *
              (1 / (2 : ℝ) ^ (level.val / 3)) := by
        apply Finset.sum_le_sum
        intro level _
        exact gradedWindow_level_failure_le activeBound level
      _ = (1 / 4096 : ℝ) *
          ∑ level : Fin depth,
            (1 / (2 : ℝ) ^ (level.val / 3)) := by
        rw [Finset.mul_sum]
      _ ≤ (1 / 4096 : ℝ) * 6 := by
        gcongr
        exact sum_inverse_pow_div_three_le depth
      _ = (6 : ℝ) / 4096 := by ring
  unfold listFailureBound gradedTerminalWindow
  norm_num only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, div_one]
  calc
    (activeBound : ℝ) / (2 : ℝ) ^ depth +
        ∑ level : Fin depth,
          (↑activeBound * (1 / (2 : ℝ) ^ level.val)) /
            ↑(gradedWindow activeBound level) ^ 2 ≤
      (1 : ℝ) / 256 + 6 / 4096 :=
        add_le_add hterminalReal hlevels
    _ ≤ (1 : ℝ) / 128 := by norm_num

/-- Extend a finite window schedule by zero.  This keeps the recursive degree
ledger over natural intervals, without manufacturing out-of-range `Fin`
values. -/
def listWindowAt {depth : ℕ} (window : Fin depth → ℕ)
    (level : ℕ) : ℕ :=
  if hlevel : level < depth then window ⟨level, hlevel⟩ else 0

@[simp] theorem listWindowAt_of_lt
    {depth : ℕ} (window : Fin depth → ℕ)
    (level : ℕ) (hlevel : level < depth) :
    listWindowAt window level = window ⟨level, hlevel⟩ := by
  unfold listWindowAt
  rw [dif_pos hlevel]

theorem listDegreeFrom_eq_terminal_add_sum
    {depth : ℕ} (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) (hlevel : level ≤ depth) :
    listDegreeFrom window terminalWindow level =
      terminalWindow +
        ∑ index ∈ Finset.Ico level depth,
          2 * listWindowAt window index := by
  rw [listDegreeFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext]
    rw [listDegreeFrom_eq_terminal_add_sum window terminalWindow
      (level + 1) (by omega)]
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hnext]
    rw [Finset.sum_insert (by simp)]
    rw [listWindowAt_of_lt window level hnext]
    omega
  · rw [dif_neg hnext]
    have hequal : level = depth := by omega
    subst level
    simp
termination_by depth - level
decreasing_by omega

theorem listDegree_eq_terminal_add_sum
    {depth : ℕ} (window : Fin depth → ℕ)
    (terminalWindow : ℕ) :
    listDegree window terminalWindow =
      terminalWindow + ∑ level : Fin depth, 2 * window level := by
  unfold listDegree
  rw [listDegreeFrom_eq_terminal_add_sum window terminalWindow
    0 (Nat.zero_le depth)]
  rw [Nat.Ico_zero_eq_range]
  congr 1
  calc
    (∑ index ∈ Finset.range depth,
        2 * listWindowAt window index) =
        ∑ level : Fin depth,
          2 * listWindowAt window level.val := by
      exact (Fin.sum_univ_eq_sum_range
        (fun index : ℕ => 2 * listWindowAt window index) depth).symm
    _ = ∑ level : Fin depth, 2 * window level := by
      apply Finset.sum_congr rfl
      intro level _
      rw [listWindowAt_of_lt window level.val level.isLt]

theorem gradedWindow_cast_le
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) :
    (gradedWindow activeBound level : ℝ) ≤
      (64 : ℝ) *
          (Real.sqrt activeBound /
            (2 : ℝ) ^ (level.val / 3) + 1) + 1 := by
  unfold gradedWindow
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem sum_gradedWindow_cast_le
    (activeBound depth : ℕ) :
    (∑ level : Fin depth,
        (gradedWindow activeBound level : ℝ)) ≤
      384 * Real.sqrt activeBound + 65 * depth := by
  calc
    (∑ level : Fin depth,
        (gradedWindow activeBound level : ℝ)) ≤
        ∑ level : Fin depth,
          ((64 : ℝ) * Real.sqrt activeBound *
              (1 / (2 : ℝ) ^ (level.val / 3)) + 65) := by
      apply Finset.sum_le_sum
      intro level _
      calc
        (gradedWindow activeBound level : ℝ) ≤
            (64 : ℝ) *
              (Real.sqrt activeBound /
                (2 : ℝ) ^ (level.val / 3) + 1) + 1 :=
          gradedWindow_cast_le activeBound level
        _ = (64 : ℝ) * Real.sqrt activeBound *
              (1 / (2 : ℝ) ^ (level.val / 3)) + 65 := by
          ring
    _ = (64 : ℝ) * Real.sqrt activeBound *
          (∑ level : Fin depth,
            (1 / (2 : ℝ) ^ (level.val / 3))) +
          65 * depth := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp
      ring
    _ ≤ (64 : ℝ) * Real.sqrt activeBound * 6 +
          65 * depth := by
      gcongr
      exact sum_inverse_pow_div_three_le depth
    _ = 384 * Real.sqrt activeBound + 65 * depth := by ring

/-- Exact quantitative form of `D₀ = O(sqrt R + J)` for the production
schedule.  Constants are deliberately simple and leave the ceiling overhead
visible rather than burying it in asymptotic notation. -/
theorem gradedListDegree_cast_le
    (activeBound depth : ℕ) :
    (listDegree (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow : ℝ) ≤
      768 * Real.sqrt activeBound + 130 * depth := by
  rw [listDegree_eq_terminal_add_sum]
  unfold gradedTerminalWindow
  norm_num only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_zero, zero_add]
  calc
    (∑ level : Fin depth,
        (2 : ℝ) * gradedWindow activeBound level) =
        2 * ∑ level : Fin depth,
          (gradedWindow activeBound level : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (384 * Real.sqrt activeBound + 65 * depth) := by
      gcongr
      exact sum_gradedWindow_cast_le activeBound depth
    _ = 768 * Real.sqrt activeBound + 130 * depth := by ring

/-- The degree bound applies to the actual recursively compiled output
polynomials, not merely to an abstract ledger. -/
theorem totalDegree_gradedListPolynomial_cast_le
    {rank depth population : ℕ}
    (activeBound : ℕ)
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (candidate : Fin (population + 1)) :
    ((listPolynomialVector label seed
        (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow candidate).totalDegree : ℝ) ≤
      768 * Real.sqrt activeBound + 130 * depth := by
  have hdegree :
      (listPolynomialVector label seed
        (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow candidate).totalDegree ≤
      listDegree (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow :=
    totalDegree_listPolynomialVector_le label seed
      (gradedWindow activeBound) gradedTerminalWindow candidate
  have hdegreeReal :
      ((listPolynomialVector label seed
        (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow candidate).totalDegree : ℝ) ≤
      (listDegree (gradedWindow activeBound : Fin depth → ℕ)
        gradedTerminalWindow : ℝ) := by
    exact_mod_cast hdegree
  exact hdegreeReal.trans
    (gradedListDegree_cast_le activeBound depth)

end NearCubicWires.SupplierListSchedule
