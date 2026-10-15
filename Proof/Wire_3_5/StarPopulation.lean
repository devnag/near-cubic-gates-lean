import Proof.Wire_3_5.PopulationChain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

namespace StarParams
variable (P : StarParams)

theorem blockCoord_inj {j j' : Fin P.r} {i i' : Fin P.b} (h : P.blockCoord j i = P.blockCoord j' i') :
    j = j' ∧ i = i' := by
  have hv := congrArg Fin.val h
  simp only [blockCoord] at hv
  have hi := i.isLt; have hi' := i'.isLt
  have hjj : j.val = j'.val := by
    rcases lt_trichotomy j.val j'.val with hlt | heq | hgt
    · exfalso
      have : (j.val + 1) * P.b ≤ j'.val * P.b := Nat.mul_le_mul_right _ hlt
      nlinarith
    · exact heq
    · exfalso
      have : (j'.val + 1) * P.b ≤ j.val * P.b := Nat.mul_le_mul_right _ hgt
      nlinarith
  refine ⟨Fin.ext hjj, Fin.ext ?_⟩
  rw [hjj] at hv; omega

theorem leftBlock_inj : Function.Injective P.leftBlock := by
  intro a b h; exact Fin.ext (by simpa [leftBlock] using congrArg Fin.val h)

theorem rightBlock_inj : Function.Injective P.rightBlock := by
  intro a b h; exact Fin.ext (by have := congrArg Fin.val h; simp [rightBlock] at this; omega)

/-- The flip set of an error choice. -/
def flipSet (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) : Finset (Fin P.n) :=
  univ.filter fun x => P.errorVector side e x = true

theorem xorInput_errorVector (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) (c : BitInput P.n) :
    xorInput c (P.errorVector side e) = xorSet (P.flipSet side e) c := by
  funext x; simp [xorInput, xorSet, flipSet]

/-- `#{u : u j = some i} = (b+1)^{r/2−1}`. -/
theorem card_errors_fixed (j : Fin (P.r / 2)) (o : Option (Fin P.b)) :
    (univ.filter fun u : P.Errors => u j = o).card = (P.b + 1) ^ (P.r / 2 - 1) := by
  classical
  have hset : (univ.filter fun u : P.Errors => u j = o) =
      Fintype.piFinset (fun j' => if j' = j then ({o} : Finset (Option (Fin P.b))) else univ) := by
    ext u
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j'; split_ifs with hj
      · subst hj; simp [h]
      · exact mem_univ _
    · intro h; have := h j; simpa using this
  rw [hset, Fintype.card_piFinset]
  have : ∀ j', (if j' = j then ({o} : Finset (Option (Fin P.b))) else univ).card =
      if j' = j then 1 else P.b + 1 := by
    intro j'; split_ifs <;> simp [Fintype.card_option]
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' univ j, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, Fintype.card_fin]

theorem coordPair_inj (side : Fin (P.r / 2) → Fin P.r) (hside : Function.Injective side) :
    Function.Injective fun p : Fin (P.r / 2) × Fin P.b => P.blockCoord (side p.1) p.2 := by
  intro p q h
  obtain ⟨h1, h2⟩ := P.blockCoord_inj h
  exact Prod.ext (hside h1) h2

theorem mem_flipSet (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) (x : Fin P.n) :
    x ∈ P.flipSet side e ↔ ∃ j i, e j = some i ∧ P.blockCoord (side j) i = x := by
  simp [flipSet, errorVector]

theorem sum_flipSet_le (f : Fin P.n → ℕ) :
    ∑ u : P.Errors, ∑ x ∈ P.flipSet P.leftBlock u, f x ≤ (P.b + 1) ^ (P.r / 2 - 1) * ∑ x, f x := by
  classical
  set g : Fin (P.r / 2) × Fin P.b → Fin P.n := fun p => P.blockCoord (P.leftBlock p.1) p.2
  have hg : Function.Injective g := P.coordPair_inj P.leftBlock P.leftBlock_inj
  have hu : ∀ u : P.Errors, ∑ x ∈ P.flipSet P.leftBlock u, f x ≤
      ∑ p : Fin (P.r / 2) × Fin P.b, if u p.1 = some p.2 then f (g p) else 0 := by
    intro u
    have hsub : P.flipSet P.leftBlock u ⊆ (univ.filter fun p : Fin (P.r / 2) × Fin P.b => u p.1 = some p.2).image g := by
      intro x hx
      obtain ⟨j, i, hji, hx'⟩ := (P.mem_flipSet _ u x).mp hx
      exact Finset.mem_image.mpr ⟨(j, i), by simp [hji], hx'⟩
    calc ∑ x ∈ P.flipSet P.leftBlock u, f x
        ≤ ∑ x ∈ (univ.filter fun p : Fin (P.r / 2) × Fin P.b => u p.1 = some p.2).image g, f x :=
          Finset.sum_le_sum_of_subset hsub
      _ = ∑ p ∈ (univ.filter fun p : Fin (P.r / 2) × Fin P.b => u p.1 = some p.2), f (g p) :=
          Finset.sum_image fun a _ b _ h => hg h
      _ = _ := by rw [Finset.sum_filter]
  calc ∑ u : P.Errors, ∑ x ∈ P.flipSet P.leftBlock u, f x
      ≤ ∑ u : P.Errors, ∑ p : Fin (P.r / 2) × Fin P.b, (if u p.1 = some p.2 then f (g p) else 0) :=
        Finset.sum_le_sum fun u _ => hu u
    _ = ∑ p : Fin (P.r / 2) × Fin P.b, f (g p) * (univ.filter fun u : P.Errors => u p.1 = some p.2).card := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = (P.b + 1) ^ (P.r / 2 - 1) * ∑ p : Fin (P.r / 2) × Fin P.b, f (g p) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
        rw [P.card_errors_fixed, mul_comm]
    _ ≤ (P.b + 1) ^ (P.r / 2 - 1) * ∑ x, f x := by
        apply Nat.mul_le_mul_left
        rw [← Finset.sum_image (s := univ) (fun a _ b _ h => hg h)]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem card_hit_le (g : NormalizedThresholdGate P.n) :
    (univ.filter fun v : P.Errors => ∃ i ∈ P.flipSet P.rightBlock v, g.weight i ≠ 0).card ≤
      (P.b + 1) ^ (P.r / 2 - 1) * (gateSupport g).card := by
  classical
  set h : Fin (P.r / 2) × Fin P.b → Fin P.n := fun p => P.blockCoord (P.rightBlock p.1) p.2
  have hh : Function.Injective h := P.coordPair_inj P.rightBlock P.rightBlock_inj
  set R := univ.filter fun p : Fin (P.r / 2) × Fin P.b => g.weight (h p) ≠ 0
  have hsub : (univ.filter fun v : P.Errors => ∃ i ∈ P.flipSet P.rightBlock v, g.weight i ≠ 0) ⊆
      R.biUnion fun p => univ.filter fun v : P.Errors => v p.1 = some p.2 := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    obtain ⟨x, hx, hw⟩ := hv
    obtain ⟨j, i, hji, hx'⟩ := (P.mem_flipSet _ v x).mp hx
    rw [Finset.mem_biUnion]
    refine ⟨(j, i), ?_, by simp [hji]⟩
    simp only [R, mem_filter, mem_univ, true_and, h]; rw [hx']; exact hw
  have hR : R.card ≤ (gateSupport g).card := by
    apply Finset.card_le_card_of_injOn h
    · intro p hp
      simp only [R, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp [gateSupport, hp]
    · intro p _ q _ hpq; exact hh hpq
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ R, (univ.filter fun v : P.Errors => v p.1 = some p.2).card := Finset.card_biUnion_le
    _ = ∑ _p ∈ R, (P.b + 1) ^ (P.r / 2 - 1) := Finset.sum_congr rfl fun p _ => P.card_errors_fixed _ _
    _ = R.card * (P.b + 1) ^ (P.r / 2 - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (P.b + 1) ^ (P.r / 2 - 1) * (gateSupport g).card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hR

end StarParams

theorem pivotCount_eq_pivCount {n : ℕ} (g : NormalizedThresholdGate n) (i : Fin n) :
    pivotCount g.eval i = pivCount g i := by
  unfold pivotCount pivCount pivotal
  congr 1; ext x; simp [bne_iff_ne]

theorem xorSet_comm {n : ℕ} (A B : Finset (Fin n)) (c : BitInput n) :
    xorSet B (xorSet A c) = xorSet A (xorSet B c) := by
  funext i; simp only [xorSet]; cases c i <;> cases decide (i ∈ A) <;> cases decide (i ∈ B) <;> rfl

theorem starPopulation_holds : StarPopulation := by
  intro P g
  classical
  set K : ℕ := P.b + 1 with hKdef
  set h2 : ℕ := P.r / 2 with hh2def
  have hK : 0 < K := Nat.succ_pos _
  have hh2 : 1 ≤ h2 := by have := P.two_le_r; omega
  have hE : Fintype.card P.Errors = K ^ h2 := by
    simp [StarParams.Errors, Fintype.card_option, K, h2]
  -- the mixed differences as flip-set differences
  have hΔ : ∀ u v c, mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) =
      mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c := by
    intro u v c
    unfold mixedDifference mixedDiffSet
    simp only [P.xorInput_errorVector, xorSet_comm]
  have hLHS : (∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0).card) =
      ∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c ≠ 0).card := by
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _
    congr 1; ext c; simp [hΔ]
  -- natural-number bounds
  set H := (univ.filter fun v : P.Errors => ∃ i ∈ P.flipSet P.rightBlock v, g.weight i ≠ 0).card
  set U := ∑ u : P.Errors, ∑ i ∈ P.flipSet P.leftBlock u, pivotCount g.eval i
  set PiC := ∑ x, pivotCount g.eval x
  set f := (gateSupport g).card
  have hS := sum_card_mixed_le g (fun u => P.flipSet P.leftBlock u) (fun v => P.flipSet P.rightBlock v)
  have hU : U ≤ K ^ (h2 - 1) * PiC := P.sum_flipSet_le (fun x => pivotCount g.eval x)
  have hH1 : H ≤ K ^ (h2 - 1) * f := P.card_hit_le g
  have hH2 : H ≤ K ^ (h2 - 1) * K := by
    have := Finset.card_le_univ (univ.filter fun v : P.Errors => ∃ i ∈ P.flipSet P.rightBlock v, g.weight i ≠ 0)
    rw [hE] at this
    rw [← pow_succ, Nat.sub_add_cancel hh2]; exact this
  have hHm : H ≤ K ^ (h2 - 1) * min K f := by
    rcases le_total K f with hkf | hkf
    · rw [min_eq_left hkf]; exact hH2
    · rw [min_eq_right hkf]; exact hH1
  have hSnat : (∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c ≠ 0).card) ≤
      2 * (K ^ (h2 - 1) * K ^ (h2 - 1)) * (min K f * PiC) := by
    calc _ ≤ 2 * H * U := hS
      _ ≤ 2 * (K ^ (h2 - 1) * min K f) * (K ^ (h2 - 1) * PiC) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hHm) hU
      _ = _ := by ring
  -- influence
  have hI : ((PiC : ℕ) : ℝ) / 2 ^ P.n ≤ Real.sqrt f := by
    have h := influence_sum_le_sqrt g
    rw [← Finset.sum_div] at h
    have hPi : ((PiC : ℕ) : ℝ) = ∑ i, (pivCount g i : ℝ) := by
      simp only [PiC]; push_cast; apply Finset.sum_congr rfl; intro i _; rw [pivotCount_eq_pivCount]
    rw [hPi]; exact h
  -- real chain
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h2n : (0 : ℝ) < 2 ^ P.n := by positivity
  have hKp : (0 : ℝ) < (K : ℝ) ^ (h2 - 1) := by positivity
  have hEsq : ((Fintype.card P.Errors : ℕ) : ℝ) ^ 2 = ((K : ℝ) ^ (h2 - 1) * (K : ℝ) ^ (h2 - 1)) * ((K : ℝ) * K) := by
    rw [hE]; push_cast
    have : h2 = (h2 - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [hLHS, hEsq]
  have hstep : ((∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c ≠ 0).card : ℕ) : ℝ) /
      (2 ^ P.n * (((K : ℝ) ^ (h2 - 1) * (K : ℝ) ^ (h2 - 1)) * ((K : ℝ) * K))) ≤
      2 * (((PiC : ℕ) : ℝ) / 2 ^ P.n) / K * min 1 ((f : ℝ) / K) := by
    rw [div_le_iff₀ (by positivity)]
    have hcast : ((∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c ≠ 0).card : ℕ) : ℝ) ≤
        2 * ((K : ℝ) ^ (h2 - 1) * (K : ℝ) ^ (h2 - 1)) * (min (K : ℝ) (f : ℝ) * ((PiC : ℕ) : ℝ)) := by
      have := hSnat
      have hmin : ((min K f : ℕ) : ℝ) = min (K : ℝ) (f : ℝ) := Nat.cast_min K f
      calc _ ≤ ((2 * (K ^ (h2 - 1) * K ^ (h2 - 1)) * (min K f * PiC) : ℕ) : ℝ) := by exact_mod_cast this
        _ = _ := by push_cast [hmin]; ring
    have hmin' : min 1 ((f : ℝ) / K) * K = min (K : ℝ) f := by
      rw [min_mul_of_nonneg _ _ hKr.le, one_mul, div_mul_cancel₀ _ hKr.ne']
    calc _ ≤ _ := hcast
      _ = _ := by rw [← hmin']; field_simp
  have hnpos : 0 < P.n := by have := P.four_r_le_n; have := P.two_le_r; omega
  have hn : (0 : ℝ) < P.n := by exact_mod_cast hnpos
  have hrpos : 0 < P.r := by have := P.two_le_r; omega
  have hr : (0 : ℝ) < P.r := by exact_mod_cast hrpos
  have hnr : (P.n : ℝ) + P.r < 2 * (K : ℝ) * P.r := by
    have := P.n_add_r_lt; exact_mod_cast this
  calc _ ≤ _ := hstep
    _ ≤ 2 * (f : ℝ) / ((K : ℝ) * Real.sqrt K) :=
        star_bound_second hKr hI (Nat.cast_nonneg _) le_rfl
    _ ≤ _ := star_bound_third (Nat.cast_nonneg _) hn hr hKr hnr

end NearCubicWires.WireExponent3_5.Shared
