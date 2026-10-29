import Proof.Gates.PairReconstruction
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Proof.Gates.Counter.Pure
import Proof.Gates.Counter.Params
import Proof.Gates.CertifiedScoreSupport

/-!
# Counter module 3/9 — prop:sound (`prop:sound` and its proof)

Parts: uniqueness of the residue systems on the reconstruction boxes (lem:one-window, lem:two-window, singleton);
the cell layer (`partAnswer_eq`, `cellCount_eq_of_tests`, `certain_of_tests`, `certain_iff_tests`); the output
layer (`outputOf_sound`, `outputOf_radius_le`).
-/

/-!
# Uniqueness of the residue systems on reconstruction boxes (lem:one-window, lem:two-window)

The counter solves, for each digit vector, the push-forward equations of a distribution on the box
`∏_r [lo_r, hi_r]` (`sec:algorithm`, "Reconstruction inside a certified cell").
This module proves that a rational function on such a box with zero
push-forward data vanishes on the box, in the three situations the parameters produce:
* one score, side at most `D' = window` (lem:one-window, via `scalarMatrix_injective`);
* two scores, sides at most an admissible `L ≥ 2` (lem:two-window, via `pairMatrix_injective`);
* any number of scores, sides at most one (the singleton convention of `L₂ = 1`, after `lem:window-size`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators Matrix
open NearCubicGates NearCubicGates.Reconstruction

/-- The box `∏_r [lo_r, hi_r]`. -/
noncomputable def boxOf {d : ℕ} (lo hi : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun r => Finset.Icc (lo r) (hi r)

theorem mem_boxOf {d : ℕ} (lo hi : Fin d → ℤ) (u : Fin d → ℤ) :
    u ∈ boxOf lo hi ↔ ∀ r, lo r ≤ u r ∧ u r ≤ hi r := by
  simp [boxOf, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Zero push-forward data on the box, for every prime of the set and every residue vector. -/
def ZeroData {d : ℕ} (primes : Finset ℕ) (lo hi : Fin d → ℤ) (G : (Fin d → ℤ) → ℚ) : Prop :=
  ∀ q ∈ primes, ∀ σ : Fin d → Fin q,
    (∑ u ∈ (boxOf lo hi).filter (fun u => ∀ r, u r ≡ (σ r : ℤ) [ZMOD (q : ℤ)]), G u) = 0

theorem emod_eq_fin_iff (a : ℤ) (q : ℕ) (ρ : Fin q) :
    a ≡ (ρ : ℤ) [ZMOD (q : ℤ)] ↔ a % (q : ℤ) = (ρ.val : ℤ) := by
  have h0 : (0 : ℤ) ≤ (ρ.val : ℤ) := by positivity
  have h1 : (ρ.val : ℤ) < (q : ℤ) := by exact_mod_cast ρ.isLt
  unfold Int.ModEq
  rw [Int.emod_eq_of_lt h0 h1]

/-! ## One score -/

theorem sum_box_one (lo hi : Fin 1 → ℤ) (f : (Fin 1 → ℤ) → ℚ) :
    ∑ u ∈ boxOf lo hi, f u =
      ∑ i : Fin (hi 0 - lo 0 + 1).toNat, f (fun _ => lo 0 + (i.val : ℤ)) := by
  symm
  refine Finset.sum_bij' (fun i _ => (fun _ => lo 0 + (i.val : ℤ)))
    (fun u hu => (⟨(u 0 - lo 0).toNat, by
      have h := (mem_boxOf lo hi u).mp hu 0
      omega⟩ : Fin (hi 0 - lo 0 + 1).toNat)) ?_ ?_ ?_ ?_ ?_
  · intro i _
    rw [mem_boxOf]
    intro r
    have hr : r = 0 := Subsingleton.elim r 0
    subst hr
    have h := i.isLt
    omega
  · intro u _
    exact Finset.mem_univ _
  · intro i _
    apply Fin.ext
    simp
  · intro u hu
    funext r
    have hr : r = 0 := Subsingleton.elim r 0
    subst hr
    have h := (mem_boxOf lo hi u).mp hu 0
    simp only
    omega
  · intro i _
    rfl

theorem box_unique_one (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ q ∈ primes, Nat.Prime q)
    (lo hi : Fin 1 → ℤ) (hw : hi 0 - lo 0 + 1 ≤ (ScalarWindow.window primes : ℤ))
    (G : (Fin 1 → ℤ) → ℚ) (hG : ZeroData primes lo hi G) : ∀ u ∈ boxOf lo hi, G u = 0 := by
  classical
  set L := (hi 0 - lo 0 + 1).toNat with hLdef
  have hL : L ≤ ScalarWindow.window primes := by omega
  let mass : Fin L → ℚ := fun i => G (fun _ => lo 0 + (i.val : ℤ))
  have hinj := scalarMatrix_injective primes hne hprime (lo 0) L hL
  have hzero : scalarMatrix primes (lo 0) L *ᵥ mass = scalarMatrix primes (lo 0) L *ᵥ 0 := by
    funext row
    rw [Matrix.mulVec_zero, Pi.zero_apply]
    obtain ⟨⟨q, hq⟩, ρ⟩ := row
    rw [scalarMatrix_mulVec]
    have h := hG q hq (fun _ => ρ)
    rw [Finset.sum_filter, sum_box_one] at h
    simp only [ScalarWindow.frameResidueData]
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro i _
    simp only [mass]
    by_cases hc : (lo 0 + (i.val : ℤ)) % (q : ℤ) = (ρ.val : ℤ)
    · rw [if_pos hc, if_pos]
      intro r
      exact (emod_eq_fin_iff _ q ρ).mpr hc
    · rw [if_neg hc, if_neg]
      intro hall
      exact hc ((emod_eq_fin_iff _ q ρ).mp (hall 0))
  have hm := hinj hzero
  intro u hu
  have h := (mem_boxOf lo hi u).mp hu 0
  have hi' : (u 0 - lo 0).toNat < L := by omega
  have hv := congrFun hm ⟨(u 0 - lo 0).toNat, hi'⟩
  simp only [mass] at hv
  have hu' : (fun _ : Fin 1 => lo 0 + (((u 0 - lo 0).toNat : ℕ) : ℤ)) = u := by
    funext r
    have hr : r = 0 := Subsingleton.elim r 0
    subst hr
    omega
  rw [hu'] at hv
  exact hv

/-! ## Two scores -/

/-- The frame embedding of the box into `Fin L × Fin L`, extended by zero. -/
noncomputable def pairMass (lo hi : Fin 2 → ℤ) (L : ℕ) (G : (Fin 2 → ℤ) → ℚ) : Fin L × Fin L → ℚ :=
  fun ij => if lo 0 + (ij.1.val : ℤ) ≤ hi 0 ∧ lo 1 + (ij.2.val : ℤ) ≤ hi 1 then
    G ![lo 0 + (ij.1.val : ℤ), lo 1 + (ij.2.val : ℤ)] else 0

theorem sum_box_two (lo hi : Fin 2 → ℤ) (L : ℕ) (hw : ∀ r, hi r - lo r + 1 ≤ (L : ℤ))
    (f : (Fin 2 → ℤ) → ℚ) :
    ∑ u ∈ boxOf lo hi, f u = ∑ ij : Fin L × Fin L,
      if lo 0 + (ij.1.val : ℤ) ≤ hi 0 ∧ lo 1 + (ij.2.val : ℤ) ≤ hi 1 then
        f ![lo 0 + (ij.1.val : ℤ), lo 1 + (ij.2.val : ℤ)] else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun ij _ => ![lo 0 + (ij.1.val : ℤ), lo 1 + (ij.2.val : ℤ)])
    (fun u hu => ((⟨(u 0 - lo 0).toNat, by
      have h := (mem_boxOf lo hi u).mp hu 0
      have h' := hw 0
      omega⟩ : Fin L), (⟨(u 1 - lo 1).toNat, by
      have h := (mem_boxOf lo hi u).mp hu 1
      have h' := hw 1
      omega⟩ : Fin L))) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    rw [Finset.mem_filter] at hij
    rw [mem_boxOf]
    intro r
    fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      omega
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  · intro u hu
    rw [Finset.mem_filter]
    have h0 := (mem_boxOf lo hi u).mp hu 0
    have h1 := (mem_boxOf lo hi u).mp hu 1
    refine ⟨Finset.mem_univ _, ?_, ?_⟩ <;> simp only <;> omega
  · intro ij hij
    rw [Finset.mem_filter] at hij
    apply Prod.ext <;> apply Fin.ext <;> simp
  · intro u hu
    have h0 := (mem_boxOf lo hi u).mp hu 0
    have h1 := (mem_boxOf lo hi u).mp hu 1
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      omega
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  · intro ij _
    rfl

theorem box_unique_two (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ q ∈ primes, Nat.Prime q)
    (L : ℕ) (hL : 2 ≤ L)
    (hadm : L ≤ TomographyDirections.degreeSum ((ScalarWindow.window primes - 1) / (L - 1)))
    (lo hi : Fin 2 → ℤ) (hw : ∀ r, hi r - lo r + 1 ≤ (L : ℤ))
    (G : (Fin 2 → ℤ) → ℚ) (hG : ZeroData primes lo hi G) : ∀ u ∈ boxOf lo hi, G u = 0 := by
  classical
  have hinj := pairMatrix_injective primes hne hprime (lo 0) (lo 1) L hL hadm
  have hzero : pairMatrix primes (lo 0) (lo 1) L *ᵥ pairMass lo hi L G =
      pairMatrix primes (lo 0) (lo 1) L *ᵥ 0 := by
    funext row
    rw [Matrix.mulVec_zero, Pi.zero_apply]
    obtain ⟨⟨q, hq⟩, ρ1, ρ2⟩ := row
    have h := hG q hq ![ρ1, ρ2]
    rw [Finset.sum_filter, sum_box_two lo hi L hw] at h
    simp only [pairMatrix, pairResidueMatrix, Matrix.mulVec, dotProduct, pairMass]
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro ij _
    by_cases hb : lo 0 + (ij.1.val : ℤ) ≤ hi 0 ∧ lo 1 + (ij.2.val : ℤ) ≤ hi 1
    · rw [if_pos hb, if_pos hb]
      by_cases hc : (lo 0 + (ij.1.val : ℤ)) % (q : ℤ) = (ρ1.val : ℤ) ∧
          (lo 1 + (ij.2.val : ℤ)) % (q : ℤ) = (ρ2.val : ℤ)
      · rw [if_pos hc, if_pos, one_mul]
        intro r
        fin_cases r
        · simpa using (emod_eq_fin_iff _ q ρ1).mpr hc.1
        · simpa using (emod_eq_fin_iff _ q ρ2).mpr hc.2
      · rw [if_neg hc, if_neg, zero_mul]
        intro hall
        apply hc
        constructor
        · have h0 := hall 0
          simp only [Fin.isValue, Matrix.cons_val_zero] at h0
          exact (emod_eq_fin_iff _ q ρ1).mp h0
        · have h1 := hall 1
          simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
          exact (emod_eq_fin_iff _ q ρ2).mp h1
    · rw [if_neg hb, if_neg hb, mul_zero]
  have hm := hinj hzero
  intro u hu
  have h0 := (mem_boxOf lo hi u).mp hu 0
  have h1 := (mem_boxOf lo hi u).mp hu 1
  have hw0 := hw 0
  have hw1 := hw 1
  have hv := congrFun hm ((⟨(u 0 - lo 0).toNat, by omega⟩ : Fin L), (⟨(u 1 - lo 1).toNat, by omega⟩ : Fin L))
  simp only [pairMass] at hv
  rw [if_pos (by constructor <;> omega)] at hv
  have hu' : ![lo 0 + (((u 0 - lo 0).toNat : ℕ) : ℤ), lo 1 + (((u 1 - lo 1).toNat : ℕ) : ℤ)] = u := by
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      omega
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      omega
  rw [hu'] at hv
  exact hv

/-! ## Singleton boxes -/

theorem box_unique_singleton {d : ℕ} (primes : Finset ℕ) (hne : primes.Nonempty)
    (hprime : ∀ q ∈ primes, Nat.Prime q)
    (lo hi : Fin d → ℤ) (hw : ∀ r, hi r - lo r + 1 ≤ 1)
    (G : (Fin d → ℤ) → ℚ) (hG : ZeroData primes lo hi G) : ∀ u ∈ boxOf lo hi, G u = 0 := by
  classical
  intro u hu
  have hlo : u = lo := by
    funext r
    have h := (mem_boxOf lo hi u).mp hu r
    have h' := hw r
    omega
  obtain ⟨q, hq⟩ := hne
  have hqpos : 0 < q := (hprime q hq).pos
  let σ : Fin d → Fin q := fun r => ⟨((lo r) % (q : ℤ)).toNat, by
    have h0 := Int.emod_nonneg (lo r) (show (q : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos (lo r) (show (0 : ℤ) < q by omega)
    omega⟩
  have h := hG q hq σ
  have hfilter : (boxOf lo hi).filter (fun u => ∀ r, u r ≡ (σ r : ℤ) [ZMOD (q : ℤ)]) = {u} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hv
      have hv' : v = lo := by
        funext r
        have h := (mem_boxOf lo hi v).mp hv.1 r
        have h' := hw r
        omega
      rw [hv', hlo]
    · intro hv
      subst hv
      refine ⟨hu, ?_⟩
      intro r
      rw [hlo]
      have h0 := Int.emod_nonneg (lo r) (show (q : ℤ) ≠ 0 by omega)
      simp only [σ, Int.ModEq, Int.toNat_of_nonneg h0, Int.emod_emod_of_dvd _ (dvd_refl (q : ℤ))]
  rw [hfilter, Finset.sum_singleton] at h
  exact h

/-- The three window cases of the counter, in one statement. -/
theorem box_unique {d : ℕ} (primes : Finset ℕ) (hne : primes.Nonempty) (hprime : ∀ q ∈ primes, Nat.Prime q)
    (lo hi : Fin d → ℤ) (L : ℕ) (hw : ∀ r, hi r - lo r + 1 ≤ (L : ℤ))
    (hcase : (d = 1 ∧ L ≤ ScalarWindow.window primes) ∨
      (d = 2 ∧ 2 ≤ L ∧ L ≤ TomographyDirections.degreeSum ((ScalarWindow.window primes - 1) / (L - 1))) ∨
      L ≤ 1)
    (G : (Fin d → ℤ) → ℚ) (hG : ZeroData primes lo hi G) : ∀ u ∈ boxOf lo hi, G u = 0 := by
  rcases hcase with ⟨rfl, hL⟩ | ⟨rfl, hL, hadm⟩ | hL
  · exact box_unique_one primes hne hprime lo hi (by have := hw 0; omega) G hG
  · exact box_unique_two primes hne hprime L hL hadm lo hi hw G hG
  · exact box_unique_singleton primes hne hprime lo hi (fun r => by have := hw r; omega) G hG

end NearCubicGates.Close.Counter

/-!
# prop:sound, the cell layer (proof of `prop:sound`)

For a selected parameter record and an ARBITRARY decoded witness, a cell that passes the strict tests eq:tests has:
* every digit within `h_E` of its reference value (lem:moment, after `eq:tests`), so the enumeration contains each point's
  digit vector and a digit residue modulo any `p ∈ 𝒫` fixes the digit vector (proof of `prop:sound`);
* on each exact digit class, the score lies in the box eq:box (eq:telescope for arbitrary proposals, proof of `prop:sound`);
* the true score distribution of the class solves the residue system, every solution agrees with it on the box
  (`box_unique`: lem:one-window / lem:two-window), hence the predicate sum is the exact count (proof of `prop:sound`).
Main results: `partAnswer_eq`, `cellCount_eq_of_tests`, `certain_of_tests`, `cellCount_eq_of_certain`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

/-! ## eq:telescope for arbitrary proposals -/

theorem reconstruct_sum (rate value : ℕ → ℤ) (m : ℕ) :
    value m = ∑ j ∈ Finset.range (m + 1),
      (∏ t ∈ Finset.Ico j m, rate t) * CountingCore.proposedDigit rate value j := by
  induction m with
  | zero => simp [CountingCore.proposedDigit]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, one_mul]
    have hsplit : ∀ j ∈ Finset.range (m + 1),
        (∏ t ∈ Finset.Ico j (m + 1), rate t) * CountingCore.proposedDigit rate value j =
          rate m * ((∏ t ∈ Finset.Ico j m, rate t) * CountingCore.proposedDigit rate value j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.prod_Ico_succ_top (by omega)]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, ← ih]
    simp only [CountingCore.proposedDigit]
    ring

section Cell

variable {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The digit vector `E(y, x)`. -/
def digitVec (x : Points wt.I) : Role c × Fin p.J → ℤ :=
  fun rj => digit c p wt rj.1.val rj.2.val (extend wt.I y x)

/-- The score vector `X(y, x)`. -/
def scoreVec (x : Points wt.I) : Role c → ℤ := fun r => scoreForm c r.val (extend wt.I y x)

/-- eq:telescope: `K_J = Σ_j A_j E_j` for every proposal. -/
theorem stage_telescope (hJ : 1 ≤ p.J) (r : ℕ) (z : BitInput c.n) :
    stageForm c wt r (p.J - 1) z = ∑ j : Fin p.J, tailProd p j.val * digit c p wt r j.val z := by
  rw [reconstruct_sum (rateOf p) (fun s => stageForm c wt r s z) (p.J - 1)]
  rw [show p.J - 1 + 1 = p.J by omega, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem abs_lt_of_natAbs_lt (v : ℤ) (R : ℕ) (h : v.natAbs < R) : -(R : ℤ) < v ∧ v < R := by
  have h' : |v| < (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h
  exact abs_lt.mp h'

/-- Passing digit moments bound every digit (lem:moment). -/
theorem digit_bounds (ht : CellTests c p wt y) (x : Points wt.I) (rj : Role c × Fin p.J) :
    digitVec c p wt y (zeroPoint wt.I) rj - p.hE < digitVec c p wt y x rj ∧
      digitVec c p wt y x rj < digitVec c p wt y (zeroPoint wt.I) rj + p.hE := by
  have h := CertifiedScoreSupport.finite_integer_moment_sound p.k p.hE
    (fun x => digit c p wt rj.1.val rj.2.val (extend wt.I y x) -
      digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I))) (ht.1 rj.1 rj.2) x
  have h2 := abs_lt_of_natAbs_lt _ _ h
  simp only [digitVec]
  constructor <;> linarith [h2.1, h2.2]

/-- Passing score moments bound `ΔΦ` (lem:moment). -/
theorem phi_bounds (ht : CellTests c p wt y) (x : Points wt.I) (r : Role c) :
    (phi c p wt r.val (extend wt.I y x) - phi c p wt r.val (extend wt.I y (zeroPoint wt.I))).natAbs < p.Lambda :=
  CertifiedScoreSupport.finite_integer_moment_sound p.k p.Lambda
    (fun x => phi c p wt r.val (extend wt.I y x) - phi c p wt r.val (extend wt.I y (zeroPoint wt.I)))
    (ht.2 r) x

theorem digitVec_mem (ht : CellTests c p wt y) (x : Points wt.I) :
    digitVec c p wt y x ∈ digitVectors c p wt y := by
  rw [digitVectors, Fintype.mem_piFinset]
  intro rj
  rw [Finset.mem_Ioo]
  exact digit_bounds c p wt y ht x rj

theorem mem_digitVectors (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) (rj : Role c × Fin p.J) :
    digitVec c p wt y (zeroPoint wt.I) rj - p.hE < κ rj ∧ κ rj < digitVec c p wt y (zeroPoint wt.I) rj + p.hE := by
  rw [digitVectors, Fintype.mem_piFinset] at hκ
  exact Finset.mem_Ioo.mp (hκ rj)

/-- A digit residue modulo any prime of the set fixes the digit vector (proof of `prop:sound`). -/
theorem class_iff (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (κ : Role c × Fin p.J → ℤ)
    (hκ : κ ∈ digitVectors c p wt y) (q : ℕ) (hq : q ∈ p.primes) (x : Points wt.I) :
    (∀ rj, digitVec c p wt y x rj ≡ κ rj [ZMOD (q : ℤ)]) ↔ digitVec c p wt y x = κ := by
  constructor
  · intro hm
    funext rj
    have hx := digit_bounds c p wt y ht x rj
    have hk := mem_digitVectors c p wt y κ hκ rj
    exact CountingCore.centered_digit_residue_unique _ _ _ _ _ hx.1 hx.2 hk.1 hk.2
      (digit_width hs q hq) (hm rj)
  · intro he rj
    rw [he]

/-- `|X^r(z)| ≤ W^r`. -/
theorem linForm_abs_le {n : ℕ} (gates : List (NormalizedThresholdGate n)) (a : List ℤ) (z : BitInput n) :
    |linForm gates a z| ≤ ((a.map Int.natAbs).sum : ℤ) := by
  induction gates generalizing a with
  | nil =>
    simp only [linForm, List.zip_nil_left, List.map_nil, List.sum_nil, abs_zero]
    positivity
  | cons g gs ih =>
    cases a with
    | nil => simp [linForm]
    | cons b bs =>
      have h := ih bs
      have hb : |b * (if g.eval z then 1 else 0)| ≤ |b| := by
        split_ifs <;> simp
      simp only [linForm, List.zip_cons_cons, List.map_cons, List.sum_cons] at h ⊢
      rw [Nat.cast_add, ← Int.abs_eq_natAbs]
      exact (abs_add_le _ _).trans (add_le_add hb h)

theorem score_abs_le {n : ℕ} (C : NCircuit n) (z : BitInput n) : |C.score z| ≤ (C.topWeight : ℤ) := by
  rw [score_eq_linForm]
  exact linForm_abs_le C.gates C.coeffs z

/-- On an exact digit class the score lies in the box eq:box (proof of `prop:sound`). -/
theorem score_mem_box (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (κ : Role c × Fin p.J → ℤ)
    (x : Points wt.I) (hx : digitVec c p wt y x = κ) (r : Role c) :
    boxLo c p wt y κ r ≤ scoreVec c wt y x r ∧ scoreVec c wt y x r ≤ boxHi c p wt y κ r := by
  have hA := A_pos hs
  have hphi := phi_bounds c p wt y ht x r
  have htel := stage_telescope c p wt hs.J_pos r.val (extend wt.I y x)
  have hK : stageForm c wt r.val (p.J - 1) (extend wt.I y x) = ∑ j : Fin p.J, tailProd p j.val * κ (r, j) := by
    rw [htel]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hx]
    rfl
  have hid : phi c p wt r.val (extend wt.I y x) - phi c p wt r.val (extend wt.I y (zeroPoint wt.I)) =
      boxCenter c p wt y κ r - (p.A : ℤ) * (scoreVec c wt y x r -
        scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) := by
    simp only [phi, boxCenter, scoreVec, hK]
    ring
  rw [hid] at hphi
  have hbox := ScoreBox.score_in_box (boxCenter c p wt y κ r) p.A
    (scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) p.Lambda (scoreVec c wt y x r)
    (by exact_mod_cast hA) (by exact_mod_cast hphi)
  have hW := abs_le.mp (score_abs_le (circ c r.val) (extend wt.I y x))
  have hsv : scoreVec c wt y x r = (circ c r.val).score (extend wt.I y x) := rfl
  simp only [boxLo, boxHi]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- Every box side has at most `L_w` integers (`sec:algorithm`, "Reconstruction inside a certified cell"). -/
theorem box_width (hs : Spec cT (header c) p) (κ : Role c × Fin p.J → ℤ) (r : Role c) :
    boxHi c p wt y κ r - boxLo c p wt y κ r + 1 ≤ (p.Lw : ℤ) := by
  have hA := A_pos hs
  have hcount := ScoreBox.public_radius_boxCount_le (boxCenter c p wt y κ r) p.A
    (scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) p.Lw (by exact_mod_cast hA) (by positivity)
  rw [← Lambda_cast hs] at hcount
  simp only [ScoreBox.boxCount, Int.toNat_natCast] at hcount
  have hlo : ScoreBox.lower (boxCenter c p wt y κ r) p.A (scoreForm c r.val (extend wt.I y (zeroPoint wt.I)))
      p.Lambda ≤ boxLo c p wt y κ r := by
    simp only [boxLo]; split_ifs <;> omega
  have hhi : boxHi c p wt y κ r ≤ ScoreBox.upper (boxCenter c p wt y κ r) p.A
      (scoreForm c r.val (extend wt.I y (zeroPoint wt.I))) p.Lambda := by
    simp only [boxHi]; split_ifs <;> omega
  omega

/-! ## The true distribution solves the residue system; every solution equals it -/

/-- Summing fiber counts over a set of values. -/
theorem sum_card_fiber {α β : Type*} [Fintype α] [DecidableEq β] (Q : α → Prop) [DecidablePred Q] (f : α → β)
    (S : Finset β) :
    (∑ u ∈ S, (((Finset.univ : Finset α).filter fun x => Q x ∧ f x = u).card : ℚ)) =
      (((Finset.univ : Finset α).filter fun x => Q x ∧ f x ∈ S).card : ℚ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2.2)]
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hu⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩

open Classical in
/-- The true score distribution of the exact digit class `κ` on a part of the cell. -/
noncomputable def trueDist (part : Option Bool) (κ : Role c × Fin p.J → ℤ) (u : Role c → ℤ) : ℚ :=
  (((Finset.univ : Finset (Points wt.I)).filter fun x =>
    inPart c wt part x = true ∧ digitVec c p wt y x = κ ∧ scoreVec c wt y x = u).card : ℚ)

open Classical in
/-- The true distribution solves the push-forward equations (proof of `prop:sound`). -/
theorem trueDist_solves (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (part : Option Bool)
    (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) :
    Solves c p wt part y κ (trueDist c p wt y part κ) := by
  intro q hq σ
  unfold trueDist
  have hfib := sum_card_fiber (fun x => inPart c wt part x = true ∧ digitVec c p wt y x = κ)
    (scoreVec c wt y) ((box c p wt y κ).filter fun u => ∀ r, u r ≡ (σ r : ℤ) [ZMOD (q : ℤ)])
  simp only [and_assoc] at hfib
  rw [hfib]
  unfold jointCount
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h4⟩
    intro rj
    have := (class_iff c p wt y hs ht κ hκ q hq x).mpr h2 rj
    exact this
  · rintro ⟨h1, h2, h3⟩
    have hd : digitVec c p wt y x = κ := (class_iff c p wt y hs ht κ hκ q hq x).mp h2
    refine ⟨h1, hd, ?_, h3⟩
    rw [box, Fintype.mem_piFinset]
    intro r
    rw [Finset.mem_Icc]
    exact score_mem_box c p wt y hs ht κ x hd r

theorem roleCount_of_header (hs : (header c).pair = false) : roleCount c.kind = 1 := by
  simp only [header, decide_eq_false_iff_not] at hs
  cases h : c.kind <;> simp_all [roleCount]

theorem roleCount_of_header_pair (hs : (header c).pair = true) : roleCount c.kind = 2 := by
  simp only [header, decide_eq_true_eq] at hs
  rw [hs]; rfl

/-- Any solution equals the true distribution on the box (lem:one-window / lem:two-window). -/
theorem solution_eq_trueDist (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (part : Option Bool)
    (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) (F : (Role c → ℤ) → ℚ)
    (hF : Solves c p wt part y κ F) : ∀ u ∈ box c p wt y κ, F u = trueDist c p wt y part κ u := by
  have hT := trueDist_solves c p wt y hs ht part κ hκ
  have hzero : ZeroData p.primes (boxLo c p wt y κ) (boxHi c p wt y κ)
      (fun u => F u - trueDist c p wt y part κ u) := by
    intro q hq σ
    rw [Finset.sum_sub_distrib]
    have h1 := hF q hq σ
    have h2 := hT q hq σ
    simp only [box] at h1 h2
    rw [boxOf, h1, h2, sub_self]
  have hu := box_unique p.primes hs.primes_nonempty (primes_prime hs) (boxLo c p wt y κ) (boxHi c p wt y κ)
    p.Lw (box_width c p wt y hs κ)
    (window_cases hs (roleCount c.kind) (roleCount_of_header c) (roleCount_of_header_pair c)) _ hzero
  intro u hmem
  exact sub_eq_zero.mp (hu u hmem)

theorem system_unique (hs : Spec cT (header c) p) (part : Option Bool) (κ : Role c × Fin p.J → ℤ)
    (F G : (Role c → ℤ) → ℚ) (hF : Solves c p wt part y κ F) (hG : Solves c p wt part y κ G) :
    ∀ u ∈ box c p wt y κ, F u = G u := by
  have hzero : ZeroData p.primes (boxLo c p wt y κ) (boxHi c p wt y κ) (fun u => F u - G u) := by
    intro q hq σ
    rw [Finset.sum_sub_distrib]
    have h1 := hF q hq σ
    have h2 := hG q hq σ
    simp only [box] at h1 h2
    rw [boxOf, h1, h2, sub_self]
  have hu := box_unique p.primes hs.primes_nonempty (primes_prime hs) (boxLo c p wt y κ) (boxHi c p wt y κ)
    p.Lw (box_width c p wt y hs κ)
    (window_cases hs (roleCount c.kind) (roleCount_of_header c) (roleCount_of_header_pair c)) _ hzero
  intro u hmem
  exact sub_eq_zero.mp (hu u hmem)

open Classical in
/-- The predicate sum of one digit class is the exact class count (proof of `prop:sound`). -/
theorem partAnswer_eq (hs : Spec cT (header c) p) (ht : CellTests c p wt y) (part : Option Bool)
    (κ : Role c × Fin p.J → ℤ) (hκ : κ ∈ digitVectors c p wt y) :
    partAnswer c p wt part y κ = (((Finset.univ : Finset (Points wt.I)).filter fun x =>
      inPart c wt part x = true ∧ digitVec c p wt y x = κ ∧
        scorePredicate c (xor (outerParity c wt y) (part.getD false)) (scoreVec c wt y x) = true).card : ℚ) := by
  have hex : ∃ F, Solves c p wt part y κ F := ⟨_, trueDist_solves c p wt y hs ht part κ hκ⟩
  have hsol : solveSystem c p wt part y κ = some (Classical.choose hex) := by
    simp only [solveSystem, dif_pos hex]
  have hF := solution_eq_trueDist c p wt y hs ht part κ hκ _ (Classical.choose_spec hex)
  simp only [partAnswer, hsol]
  rw [Finset.sum_congr rfl (fun u hu => by rw [hF u hu])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  unfold trueDist
  have hfib := sum_card_fiber (fun x => inPart c wt part x = true ∧ digitVec c p wt y x = κ)
    (scoreVec c wt y) ((box c p wt y κ).filter fun u =>
      scorePredicate c (xor (outerParity c wt y) (part.getD false)) u = true)
  simp only [and_assoc] at hfib
  rw [hfib]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_, h3⟩
    rw [box, Fintype.mem_piFinset]
    intro r
    rw [Finset.mem_Icc]
    exact score_mem_box c p wt y hs ht κ x h2 r

/-! ## Summing over the digit enumeration and the parts -/

open Classical in
theorem sum_digitVectors (ht : CellTests c p wt y) (P Q : Points wt.I → Prop) :
    (∑ κ ∈ digitVectors c p wt y, (((Finset.univ : Finset (Points wt.I)).filter fun x =>
      P x ∧ digitVec c p wt y x = κ ∧ Q x).card : ℚ)) =
      (((Finset.univ : Finset (Points wt.I)).filter fun x => P x ∧ Q x).card : ℚ) := by
  have hfib := sum_card_fiber (fun x => P x ∧ Q x) (digitVec c p wt y) (digitVectors c p wt y)
  have hl : ∀ κ ∈ digitVectors c p wt y, (((Finset.univ : Finset (Points wt.I)).filter fun x =>
      P x ∧ digitVec c p wt y x = κ ∧ Q x).card : ℚ) =
      (((Finset.univ : Finset (Points wt.I)).filter fun x => (P x ∧ Q x) ∧ digitVec c p wt y x = κ).card : ℚ) := by
    intro κ _
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [Finset.sum_congr rfl hl, hfib]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, digitVec_mem c p wt y ht x⟩⟩

theorem foldl_xor_acc (l : List Bool) (a : Bool) : l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor a b), ih b]
    cases a <;> cases b <;> simp

theorem foldl_xor_map {α : Type*} (l : List α) (f g : α → Bool) :
    (l.map fun i => xor (f i) (g i)).foldl xor false =
      xor ((l.map f).foldl xor false) ((l.map g).foldl xor false) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons, Bool.false_xor]
    rw [foldl_xor_acc _ (xor (f a) (g a)), foldl_xor_acc _ (f a), foldl_xor_acc _ (g a), ih]
    cases f a <;> cases g a <;> simp

/-- `PAR_Σ(y, x) = PAR_{Σ∩I}(x) ⊕ PAR_{Σ∖I}(y)`: the parity split is a partition (proof of `prop:sound`). -/
theorem parityOf_extend (x : Points wt.I) :
    c.parityOf (extend wt.I y x) = xor (innerParity c wt x) (outerParity c wt y) := by
  unfold Call.parityOf innerParity outerParity
  rw [← foldl_xor_map]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : i < c.n
  · simp only [dif_pos h, extend]
    by_cases hI : (⟨i, h⟩ : Fin c.n) ∈ wt.I
    · simp [dif_pos hI]
    · simp [dif_neg hI]
  · simp [dif_neg h]

theorem coord0_scoreVec (x : Points wt.I) : coord0 (scoreVec c wt y x) = c.first.score (extend wt.I y x) := by
  simp [coord0, scoreVec, scoreForm, circ]

theorem coord1_scoreVec (hk : c.kind = .pair) (x : Points wt.I) :
    coord1 (scoreVec c wt y x) = c.second.score (extend wt.I y x) := by
  have h : 1 < roleCount c.kind := by rw [hk]; decide
  simp [coord1, dif_pos h, scoreVec, scoreForm, circ]

theorem kind_cases : c.kind = .single ∨ c.kind = .pair ∨ c.kind = .parity := by
  cases c.kind <;> simp

open Classical in
/-- The parts and the requested predicate recover the call's predicate (`sec:algorithm`,
"Reconstruction inside a certified cell"). -/
theorem parts_sum :
    ((parts c).map fun part => (((Finset.univ : Finset (Points wt.I)).filter fun x =>
      inPart c wt part x = true ∧
        scorePredicate c (xor (outerParity c wt y) (part.getD false)) (scoreVec c wt y x) = true).card : ℚ)).sum =
      (((Finset.univ : Finset (Points wt.I)).filter fun x => c.predicate (extend wt.I y x) = true).card : ℚ) := by
  rcases kind_cases c with hk | hk | hk
  · have hp : parts c = [none] := by simp [parts, hk]
    rw [hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inPart, scorePredicate, hk, Call.predicate,
      coord0_scoreVec, eval_eq_topLookup]
  · have hp : parts c = [none] := by simp [parts, hk]
    rw [hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inPart, scorePredicate, hk, Call.predicate,
      coord0_scoreVec, coord1_scoreVec c wt y hk, eval_eq_topLookup]
  · have hp : parts c = [some false, some true] := by simp [parts, hk]
    rw [hp]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Points wt.I)).filter
      fun x => c.predicate (extend wt.I y x) = true) (fun x => innerParity c wt x = false)]
    push_cast
    congr 3
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inPart, scorePredicate, hk, Call.predicate,
        coord0_scoreVec, eval_eq_topLookup, parityOf_extend, Option.getD_some, beq_iff_eq]
      rcases Bool.eq_false_or_eq_true (innerParity c wt x) with h | h <;>
        rcases Bool.eq_false_or_eq_true (outerParity c wt y) with h' | h' <;> simp [h, h']
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, inPart, scorePredicate, hk, Call.predicate,
        coord0_scoreVec, eval_eq_topLookup, parityOf_extend, Option.getD_some, beq_iff_eq,
        Bool.not_eq_false]
      rcases Bool.eq_false_or_eq_true (innerParity c wt x) with h | h <;>
        rcases Bool.eq_false_or_eq_true (outerParity c wt y) with h' | h' <;> simp [h, h']

open Classical in
/-- The true count `N*_y` of accepting points of the cell `y`. -/
noncomputable def trueCount : ℚ :=
  (((Finset.univ : Finset (Points wt.I)).filter fun x => c.predicate (extend wt.I y x) = true).card : ℚ)

/-- On a cell passing the tests, the reconstructed count is exact (proof of prop:sound). -/
theorem cellCount_eq_of_tests (hs : Spec cT (header c) p) (ht : CellTests c p wt y) :
    cellCount c p wt y = trueCount c wt y := by
  classical
  unfold cellCount trueCount
  rw [← parts_sum c wt y]
  congr 1
  apply List.map_congr_left
  intro part _
  rw [Finset.sum_congr rfl (fun κ hκ => partAnswer_eq c p wt y hs ht part κ hκ)]
  convert sum_digitVectors c p wt y ht (fun x => inPart c wt part x = true)
    (fun x => scorePredicate c (xor (outerParity c wt y) (part.getD false)) (scoreVec c wt y x) = true)

theorem card_points (hk : wt.I.card = p.k) : Fintype.card (Points wt.I) = 2 ^ p.k := by
  simp [Points, hk]

theorem trueCount_bounds (hk : wt.I.card = p.k) : 0 ≤ trueCount c wt y ∧ trueCount c wt y ≤ 2 ^ p.k := by
  classical
  unfold trueCount
  refine ⟨by positivity, ?_⟩
  have h := Finset.card_filter_le (Finset.univ : Finset (Points wt.I))
    (fun x => c.predicate (extend wt.I y x) = true)
  rw [Finset.card_univ, card_points c p wt hk] at h
  exact_mod_cast h

/-- A cell passing the tests is certain (used by the proof of prop:complete). -/
theorem certain_of_tests (hs : Spec cT (header c) p) (hk : wt.I.card = p.k) (ht : CellTests c p wt y) :
    Certain c p wt y := by
  have heq := cellCount_eq_of_tests c p wt y hs ht
  have hb := trueCount_bounds c p wt y hk
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · intro part _ κ hκ
    exact ⟨_, trueDist_solves c p wt y hs ht part κ hκ⟩
  · rw [heq]; unfold trueCount; simp
  · rw [heq]; exact hb.1
  · rw [heq]; exact hb.2

/-- On every cell, certainty is exactly the strict tests eq:tests: once the tests pass, every residue system is
consistent and its unique solution gives an integer count in `[0, 2^k]`, so the inconsistency and integrality
checks of `sec:algorithm`, "Reconstruction inside a certified cell", never fire after passing tests. -/
theorem certain_iff_tests (hs : Spec cT (header c) p) (hk : wt.I.card = p.k) :
    Certain c p wt y ↔ CellTests c p wt y :=
  ⟨fun h => h.1, certain_of_tests c p wt y hs hk⟩

/-- Every certain cell's count is exact (prop:sound). -/
theorem cellCount_eq_of_certain (hs : Spec cT (header c) p) (hc : Certain c p wt y) :
    cellCount c p wt y = trueCount c wt y :=
  cellCount_eq_of_tests c p wt y hs hc.1

end Cell

end NearCubicGates.Close.Counter

/-!
# prop:sound, the output layer (`eq:output`, and the end of the proof of `prop:sound`)

The cube is the disjoint union of the cells; certain cells contribute their exact counts and each uncertain cell
has between zero and `2^k` accepting points, so replacing its count by `2^{k−1}` errs by at most `2^{k−1}`
(`outputOf_sound`). The radius is `2^{k−1} N_unc / 2^n`, which `outputOf_radius_le` bounds by the fraction of cells
failing the tests (used by prop:complete).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

/-- The cube splits into cells times inner points. -/
def splitEquiv {n : ℕ} (I : Finset (Fin n)) : Cells I × Points I ≃ BitInput n where
  toFun yx := extend I yx.1 yx.2
  invFun z := (fun i => z i.1, fun i => z i.1)
  left_inv yx := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [extend, dif_neg i.2]
    · simp [extend]
  right_inv z := by
    funext i
    simp only [extend]
    split_ifs <;> rfl

theorem card_filter_split {n : ℕ} (I : Finset (Fin n)) (P : BitInput n → Prop) [DecidablePred P] :
    (((Finset.univ : Finset (BitInput n)).filter P).card : ℚ) =
      ∑ y : Cells I, (((Finset.univ : Finset (Points I)).filter fun x => P (extend I y x)).card : ℚ) := by
  rw [Finset.card_filter]
  push_cast
  rw [← Fintype.sum_equiv (splitEquiv I) (fun yx => if P (extend I yx.1 yx.2) then (1 : ℚ) else 0)
    (fun z => if P z then (1 : ℚ) else 0) (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.card_filter]
  push_cast
  rfl

theorem prob_eq_sum (c : Call) (wt : Wit c.n) :
    c.prob = (∑ y : Cells wt.I, trueCount c wt y) / 2 ^ c.n := by
  classical
  unfold Call.prob trueCount
  rw [card_filter_split wt.I]

section Out

variable {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n)

open Classical in
/-- eq:output is sound for every witness (prop:sound). -/
theorem outputOf_sound (hs : Spec cT (header c) p) (hk : wt.I.card = p.k) (hk1 : 1 ≤ p.k) :
    |(outputOf c p wt).1 - c.prob| ≤ (outputOf c p wt).2 := by
  rw [prob_eq_sum c wt]
  simp only [outputOf]
  set S := (Finset.univ : Finset (Cells wt.I))
  have hpow : (2 : ℚ) ^ p.k = 2 * 2 ^ (p.k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun y => Certain c p wt y) (fun y => trueCount c wt y)
  have hcert : ∑ y ∈ S.filter (fun y => Certain c p wt y), cellCount c p wt y =
      ∑ y ∈ S.filter (fun y => Certain c p wt y), trueCount c wt y :=
    Finset.sum_congr rfl fun y hy => cellCount_eq_of_certain c p wt y hs (Finset.mem_filter.mp hy).2
  have hunc : ((2 : ℚ) ^ (p.k - 1)) * ((S.filter fun y => ¬ Certain c p wt y).card : ℚ) =
      ∑ y ∈ S.filter (fun y => ¬ Certain c p wt y), (2 : ℚ) ^ (p.k - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdiff : (∑ y ∈ S.filter (fun y => Certain c p wt y), cellCount c p wt y +
      2 ^ (p.k - 1) * ((S.filter fun y => ¬ Certain c p wt y).card : ℚ)) - ∑ y, trueCount c wt y =
      ∑ y ∈ S.filter (fun y => ¬ Certain c p wt y), ((2 : ℚ) ^ (p.k - 1) - trueCount c wt y) := by
    rw [hcert, hunc, Finset.sum_sub_distrib, ← hsplit]
    ring
  have hbound : |∑ y ∈ S.filter (fun y => ¬ Certain c p wt y), ((2 : ℚ) ^ (p.k - 1) - trueCount c wt y)| ≤
      ∑ y ∈ S.filter (fun y => ¬ Certain c p wt y), (2 : ℚ) ^ (p.k - 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    have hb := trueCount_bounds c p wt y hk
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  have h2n : (0 : ℚ) < 2 ^ c.n := by positivity
  rw [← sub_div, abs_div, abs_of_pos h2n, div_le_div_iff_of_pos_right h2n, hdiff, hunc]
  exact hbound

open Classical in
/-- The radius is at most half the fraction of cells failing the tests (proof of prop:complete). -/
theorem outputOf_radius_le (hs : Spec cT (header c) p) (hk : wt.I.card = p.k) (hk1 : 1 ≤ p.k) (hkn : p.k ≤ c.n) :
    (outputOf c p wt).2 ≤
      (((Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ CellTests c p wt y).card : ℚ) /
        2 ^ (c.n - p.k) / 2 := by
  simp only [outputOf]
  have hsub : (Finset.univ.filter fun y => ¬ Certain c p wt y) ⊆
      (Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ CellTests c p wt y := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact fun ht => hy (certain_of_tests c p wt y hs hk ht)
  have hcard := Finset.card_le_card hsub
  have hpow : (2 : ℚ) ^ c.n = 2 ^ (c.n - p.k) * 2 ^ (p.k - 1) * 2 := by
    rw [mul_assoc, ← pow_succ, ← pow_add]; congr 1; omega
  rw [hpow]
  have h1 : (0 : ℚ) < 2 ^ (c.n - p.k) := by positivity
  have h2 : (0 : ℚ) < 2 ^ (p.k - 1) := by positivity
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : ((Finset.univ.filter fun y => ¬ Certain c p wt y).card : ℚ) ≤
      (((Finset.univ : Finset (Cells wt.I)).filter fun y => ¬ CellTests c p wt y).card : ℚ) := by
    exact_mod_cast hcard
  nlinarith [mul_le_mul_of_nonneg_left hc (le_of_lt (mul_pos h1 h2))]

end Out

end NearCubicGates.Close.Counter
