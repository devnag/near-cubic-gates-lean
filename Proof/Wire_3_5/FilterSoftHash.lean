import Proof.Wire_3_5.FilterSoft

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces Finset

namespace MajorantParams
variable (P : MajorantParams)

/-- The hash seed's binary code: `2t` field coefficients, each by its `ℓ₀` basis coordinates. -/
noncomputable def seedCode : (Fin (2 * P.t * P.ell0) → Bool) ≃ P.Seed :=
  (Equiv.arrowCongr (finProdFinEquiv.symm) (Equiv.refl Bool)).trans <|
    (Equiv.curry (Fin (2 * P.t)) (Fin P.ell0) Bool).trans <|
      Equiv.arrowCongr (Equiv.refl _) <|
        (Equiv.arrowCongr (Equiv.refl (Fin P.ell0)) finTwoEquiv.symm).trans P.coord.toEquiv.symm

/-- `H_h(x)·Π_{j<J}W_j^{2t}` as a natural number: the terminal counts times the product of all window powers, plus each
discrepancy power times the other windows' powers. -/
noncomputable def Hcleared (Zs : List (List Bool)) (h : P.Seed) : ℕ :=
  (Zs.map fun Z => (P.data h).levelCount P.J Z * ∏ j ∈ Finset.range P.J, P.W j ^ (2 * P.t) +
    ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z).natAbs ^ (2 * P.t) *
      ∏ j' ∈ (Finset.range P.J).erase j, P.W j' ^ (2 * P.t)).sum

theorem H_mul_prod_W (Zs : List (List Bool)) (h : P.Seed) :
    P.H Zs h * ∏ j ∈ Finset.range P.J, (P.W j : ℝ) ^ (2 * P.t) = P.Hcleared Zs h := by
  unfold H Hcleared
  induction Zs with
  | nil => simp
  | cons Z Zs ih =>
    simp only [List.map_cons, List.sum_cons]
    push_cast at ih ⊢
    rw [add_mul, ih]
    congr 1
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hW : (P.W j : ℝ) ≠ 0 := by exact_mod_cast (show P.W j ≠ 0 by have := P.W_ge j; omega)
    rw [← Finset.mul_prod_erase _ _ hj]
    have habs : ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) =
        (((P.data h).levelDelta j Z).natAbs : ℝ) ^ (2 * P.t) := by
      rw [pow_mul, pow_mul, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [habs]
    field_simp

/-! ## The instance -/

variable {X : Type} [Fintype X] [Nonempty X]

theorem booleanMean_eq_uMean {Ω : Type} [Fintype Ω] (f : Ω → Bool) : booleanMean f = uMean fun ω => bitR (f ω) := rfl

theorem booleanMean_not {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → Bool) :
    booleanMean (fun ω => !f ω) = 1 - booleanMean f := by
  unfold booleanMean
  have hc : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hc.ne', ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun ω _ => show bitAsReal (!f ω) + bitAsReal (f ω) = 1 by cases f ω <;> simp [bitAsReal])]
  simp

theorem soft_hash (spectrum : ExpanderSpectrumContract) (Paux : GapParams) (hauxU : 1 ≤ Paux.cap)
    (hauxE : 1 ≤ Paux.errExp) (zres : X → List Bool) (hzlen : ∀ x, (zres x).length ≤ Paux.len)
    (pops : X → List (List Bool)) (ht : 1 ≤ P.t) (hA : ∀ x, (pops x).length ≤ P.A)
    (hM : ∀ x, ∀ Z ∈ pops x, Z.length ≤ P.M)
    (hlow : ∀ x, (zres x).count true ≤ 4096 * Paux.cap → ∀ Z ∈ pops x, (P.active Z).card ≤ P.Bstar) :
    let hstar := P.seedCode (greedy (2 * P.t * P.ell0) fun s =>
      softObjective (fun e x => gapFilter Paux e (zres x)) (fun h x => P.H (pops x) h) (P.seedCode s))
    uMean (fun x => bitR (decide ((zres x).count true ≤ Paux.cap) &&
        decide (∃ Z ∈ pops x, (P.data hstar).listReport Z ≠ Z.count true))) ≤
      (P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) +
        (1 / 2 ^ Paux.errExp) * (P.A * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t)))) / (1 - 1 / 2 ^ Paux.errExp) := by
  intro hstar
  have hG := gapFilter_guarantee spectrum Paux hauxU
  have hε1 : (1 : ℝ) / 2 ^ Paux.errExp < 1 := by
    rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hH0 : ∀ h x, 0 ≤ P.H (pops x) h := fun h x => P.H_nonneg _ h
  have hHmax : ∀ h x, P.H (pops x) h ≤ P.A * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t)) := by
    intro h x
    refine (P.H_le_max (pops x) (hM x) h).trans ?_
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hA x) (by positivity)
  have hlowH : ∀ x, (zres x).count true ≤ 4096 * Paux.cap →
      uMean (fun h => P.H (pops x) h) ≤ P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) := by
    intro x hx
    have := P.sum_H_le ht (pops x) (fun Z hZ => ⟨hM x Z hZ, hlow x hx Z hZ⟩)
    unfold uMean
    have hS : (0 : ℝ) < Fintype.card P.Seed := Nat.cast_pos.mpr Fintype.card_pos
    rw [div_le_iff₀ hS]
    have hlen : ((pops x).length : ℝ) ≤ P.A := by exact_mod_cast hA x
    have hnn : (0 : ℝ) ≤ P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t := by positivity
    calc ∑ h, P.H (pops x) h
        ≤ Fintype.card P.Seed * ((pops x).length * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := this
      _ ≤ Fintype.card P.Seed * (P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := by gcongr
      _ = P.A * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) * Fintype.card P.Seed := by ring
  have hhigh : ∀ x, 4096 * Paux.cap < (zres x).count true →
      auxMean (fun e x => gapFilter Paux e (zres x)) x ≤ 1 / 2 ^ Paux.errExp := by
    intro x hx
    unfold auxMean
    rw [← booleanMean_eq_uMean]
    exact hG.sound (zres x) (hzlen x) hx.le
  have hcomp : ∀ x, (zres x).count true ≤ Paux.cap →
      1 - 1 / 2 ^ Paux.errExp ≤ auxMean (fun e x => gapFilter Paux e (zres x)) x := by
    intro x hx
    unfold auxMean
    rw [← booleanMean_eq_uMean]
    have := hG.complete (zres x) (hzlen x) hx
    rw [booleanMean_not] at this
    linarith
  exact filt_soft (fun e x => gapFilter Paux e (zres x)) (fun h x => P.H (pops x) h) (fun x => (zres x).count true)
    Paux.cap (4096 * Paux.cap) ((P.A : ℝ) * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t))
    (1 / 2 ^ Paux.errExp) ((P.A : ℝ) * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t))) (by positivity) (by positivity) hε1
    hH0 hHmax hlowH hhigh hcomp
    (fun h x => decide (∃ Z ∈ pops x, (P.data h).listReport Z ≠ Z.count true))
    (fun h x hE => by
      simp only [decide_eq_true_eq] at hE
      obtain ⟨Z, hZ, hne⟩ := hE
      apply P.H_dominates ht (pops x) h Z hZ
      intro hgood
      exact hne ((P.data h).listReport_eq_count (P.inLevel_zero h) (P.inLevel_nest h) Z (hM x Z hZ) hgood))
    P.seedCode

theorem observable (spectrum : ExpanderSpectrumContract) (Preg : GapParams) (hregU : 1 ≤ Preg.cap)
    (zres : X → List Bool) (hzlen : ∀ x, (zres x).length ≤ Preg.len) (pops : X → List (List Bool))
    (h : P.Seed) (δ : ℝ)
    (hδ : uMean (fun x => bitR (decide ((zres x).count true ≤ 4096 * Preg.cap) &&
      decide (∃ Z ∈ pops x, (P.data h).listReport Z ≠ Z.count true))) ≤ δ)
    (R Rhat : X → Bool)
    (hagree : ∀ x, (∀ Z ∈ pops x, (P.data h).listReport Z = Z.count true) → Rhat x = R x) :
    uMean (fun p : X × GapSeed Preg => bitR (gapFilter Preg p.2 (zres p.1)) * |bitR (Rhat p.1) - bitR (R p.1)|) ≤
      δ + 1 / 2 ^ Preg.errExp := by
  have hG := gapFilter_guarantee spectrum Preg hregU
  refine observable_error_le (fun e x => gapFilter Preg e (zres x)) (fun x => (zres x).count true) (4096 * Preg.cap)
    (1 / 2 ^ Preg.errExp) δ (by positivity) ?_ R Rhat
    (fun x => decide (∃ Z ∈ pops x, (P.data h).listReport Z ≠ Z.count true)) ?_ hδ
  · intro x hx
    rw [← booleanMean_eq_uMean]
    exact hG.sound (zres x) (hzlen x) hx.le
  · intro x _ hfail
    apply hagree x
    intro Z hZ
    by_contra hne
    simp only [decide_eq_false_iff_not, not_exists, not_and, not_not] at hfail
    exact hne (hfail Z hZ)

end MajorantParams

end NearCubicWires.WireExponent3_5.Filters
