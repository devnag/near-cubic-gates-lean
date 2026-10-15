import Proof.Gates.Interfaces.CounterFormats
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Solve

open NearCubicGates.Close.Interfaces.Formats
open Matrix

/-! ## The augmented matrix and the algorithm -/

/-- The 0/1 coefficient of a row at a point. -/
def coef (row : ℕ × List ℕ × ℕ) (u : List ℤ) : ℤ := if inClass row.1 row.2.1 u = true then 1 else 0

/-- Entry `(i, j)` of the augmented matrix: rows `i < m` are the system (columns `j < n` the coefficients, the right
side elsewhere), rows `m + v` the unit vector `e_v` with right side `0`. -/
def amat (s : SysReq) (i j : ℕ) : ℤ :=
  if i < s.rows.length then
    (if j < s.pts.length then coef (s.rows.getD i (0, [], 0)) (s.pts.getD j []) else ((s.rows.getD i (0, [], 0)).2.2 : ℤ))
  else if j < s.pts.length ∧ i - s.rows.length = j then 1 else 0

/-- The elimination state: the current entries and the last pivot. -/
structure St where
  a : ℕ → ℕ → ℤ
  D : ℤ

/-- The pivot row of column `v`: the first row `i < m` with a nonzero entry. -/
def piv (m : ℕ) (a : ℕ → ℕ → ℤ) (v : ℕ) : Option ℕ := (List.range m).find? fun i => a i v != 0

/-- One Bareiss update with pivot `(r, v)` and previous pivot `D`. -/
def upd (a : ℕ → ℕ → ℤ) (D : ℤ) (r v : ℕ) : ℕ → ℕ → ℤ := fun i j => Int.tdiv (a r v * a i j - a i v * a r j) D

/-- Column `v`. -/
def step (m : ℕ) (st : St) (v : ℕ) : St :=
  match piv m st.a v with
  | none => st
  | some r => ⟨upd st.a st.D r v, st.a r v⟩

/-- The first `V` columns. -/
def run (m : ℕ) (st : St) : ℕ → St
  | 0 => st
  | V + 1 => step m (run m st V) V

/-- The final state. -/
def final (s : SysReq) : St := run s.rows.length ⟨amat s, 1⟩ s.pts.length

/-- **The solver**: `none` when a system row keeps a nonzero right side, else `x_v = −a (m+v) n / D`. -/
def solve (s : SysReq) : Option (List ℚ) :=
  if (List.range s.rows.length).all (fun i => (final s).a i s.pts.length == 0) then
    some ((List.range s.pts.length).map fun v => -((final s).a (s.rows.length + v) s.pts.length : ℚ) / (final s).D)
  else none

/-! ## The bordered-determinant lemma -/

/-- `det [[A, u], [w, d]] = det A · (d − μ·u)` when `w = μ A`. -/
theorem det_bord {k : ℕ} (A : Matrix (Fin k) (Fin k) ℚ) (u w μ : Fin k → ℚ) (d : ℚ)
    (hw : ∀ b, w b = ∑ a, μ a * A a b) :
    (fromBlocks A (Matrix.of fun a (_ : Fin 1) => u a) (Matrix.of fun (_ : Fin 1) b => w b)
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => d)).det = A.det * (d - ∑ a, μ a * u a) := by
  have hfac : fromBlocks A (Matrix.of fun a (_ : Fin 1) => u a) (Matrix.of fun (_ : Fin 1) b => w b)
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => d) =
      fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) 0 (Matrix.of fun (_ : Fin 1) a => μ a) 1 *
      fromBlocks A (Matrix.of fun a (_ : Fin 1) => u a) 0
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => d - ∑ a, μ a * u a) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i b; simp [Matrix.mul_apply, hw]
    · ext i b; simp [Matrix.mul_apply]
  rw [hfac, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_one, Matrix.det_fin_one]
  simp

/-! ## The invariant -/

section Inv
variable (M : ℕ → ℕ → ℤ)

/-- The pivot block `M[R, C]` after `k` pivots. -/
def pmat (R C : ℕ → ℕ) (k : ℕ) : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun a b => M (R a) (C b)

/-- `Σ_a μ_a M (R a) j`. -/
def comb (R : ℕ → ℕ) (k : ℕ) (μ : Fin k → ℚ) (j : ℕ) : ℚ := ∑ a : Fin k, μ a * (M (R a) j : ℚ)

/-- The bordered integer matrix of row `ρ` and column `j`. -/
def bord (R C : ℕ → ℕ) (k : ℕ) (ρ j : ℕ) : Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℤ :=
  fromBlocks (pmat M R C k) (Matrix.of fun a (_ : Fin 1) => M (R a) j) (Matrix.of fun (_ : Fin 1) b => M ρ (C b))
    (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => M ρ j)

/-- **The elimination invariant** after `k` pivots `(R a, C a)`. -/
structure Inv (st : St) (k : ℕ) (R C : ℕ → ℕ) : Prop where
  det : st.D = (pmat M R C k).det
  ne : st.D ≠ 0
  row : ∀ ρ : ℕ, ∃ μ : Fin k → ℚ, (∀ b : Fin k, (M ρ (C b) : ℚ) = comb M R k μ (C b)) ∧
    ∀ j, (st.a ρ j : ℚ) = st.D * ((M ρ j : ℚ) - comb M R k μ j)

theorem bord_cast (R C : ℕ → ℕ) (k : ℕ) (ρ j : ℕ) :
    ((bord M R C k ρ j).det : ℚ) =
      (fromBlocks ((pmat M R C k).map (Int.cast : ℤ → ℚ)) (Matrix.of fun a (_ : Fin 1) => (M (R a) j : ℚ))
        (Matrix.of fun (_ : Fin 1) b => (M ρ (C b) : ℚ)) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (M ρ j : ℚ))).det := by
  have h := RingHom.map_det (Int.castRingHom ℚ) (bord M R C k ρ j)
  simp only [eq_intCast] at h
  rw [h]
  congr 1
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> simp [bord, RingHom.mapMatrix_apply]

/-- Any rational row combination with the column condition gives a determinant. -/
theorem det_bord_comb (R C : ℕ → ℕ) (k : ℕ) (ρ j : ℕ) (μ : Fin k → ℚ)
    (hμ : ∀ b : Fin k, (M ρ (C b) : ℚ) = comb M R k μ (C b)) :
    ((bord M R C k ρ j).det : ℚ) = ((pmat M R C k).det : ℚ) * ((M ρ j : ℚ) - comb M R k μ j) := by
  rw [bord_cast]
  have h := det_bord ((pmat M R C k).map (Int.cast : ℤ → ℚ)) (fun a => (M (R a) j : ℚ)) (fun b => (M ρ (C b) : ℚ))
    μ (M ρ j : ℚ) (fun b => by rw [hμ b]; simp [comb, pmat])
  have hc : ((pmat M R C k).det : ℚ) = ((pmat M R C k).map (Int.cast : ℤ → ℚ)).det := by
    simpa using RingHom.map_det (Int.castRingHom ℚ) (pmat M R C k)
  rw [h, hc]
  rfl

/-- **Every entry is a determinant** of entries of `M`. -/
theorem entry_eq_det {st : St} {k : ℕ} {R C : ℕ → ℕ} (h : Inv M st k R C) (ρ j : ℕ) :
    st.a ρ j = (bord M R C k ρ j).det := by
  obtain ⟨μ, hμc, hμv⟩ := h.row ρ
  have e := det_bord_comb M R C k ρ j μ hμc
  rw [← h.det] at e
  exact_mod_cast (hμv j).trans e.symm

/-- **The bound** `|a| ≤ (k+1)!·X^{k+1}` for entries of `M` bounded by `X`. -/
theorem abs_entry_le {st : St} {k : ℕ} {R C : ℕ → ℕ} (h : Inv M st k R C) (X : ℤ) (hX : ∀ i j, |M i j| ≤ X)
    (ρ j : ℕ) : |st.a ρ j| ≤ (k + 1).factorial * X ^ (k + 1) := by
  rw [entry_eq_det M h ρ j]
  have hb := Matrix.det_le (abv := AbsoluteValue.abs) (A := bord M R C k ρ j) (x := X) (fun x y => by
    rcases x with x | x <;> rcases y with y | y <;> simp [bord, pmat, hX])
  simpa [nsmul_eq_mul] using hb

end Inv

/-! ## One pivot -/

section Step
variable (M : ℕ → ℕ → ℤ)

/-- A pivot list extended by one entry at position `k`. -/
def ext (R : ℕ → ℕ) (k r : ℕ) : ℕ → ℕ := fun a => if a = k then r else R a

theorem ext_lt (R : ℕ → ℕ) {k a : ℕ} (r : ℕ) (h : a < k) : ext R k r a = R a := by
  simp [ext, Nat.ne_of_lt h]

theorem ext_self (R : ℕ → ℕ) (k r : ℕ) : ext R k r k = r := by simp [ext]

/-- The new pivot block is the bordered matrix of the pivot. -/
theorem pmat_succ (R C : ℕ → ℕ) (k r v : ℕ) :
    (pmat M (ext R k r) (ext C k v) (k + 1)).det = (bord M R C k r v).det := by
  rw [← det_reindex_self finSumFinEquiv.symm (pmat M (ext R k r) (ext C k v) (k + 1))]
  congr 1
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · simp [bord, pmat, ext_lt _ _ x.isLt, ext_lt _ _ y.isLt]
  · have hy : (y : ℕ) = 0 := by omega
    simp [bord, pmat, ext_lt _ _ x.isLt, hy, ext_self]
  · have hx : (x : ℕ) = 0 := by omega
    simp [bord, pmat, ext_lt _ _ y.isLt, hx, ext_self]
  · have hx : (x : ℕ) = 0 := by omega
    have hy : (y : ℕ) = 0 := by omega
    simp [bord, pmat, hx, hy, ext_self]

theorem comb_succ (R : ℕ → ℕ) (k r : ℕ) (μ ν : Fin k → ℚ) (t : ℚ) (j : ℕ) :
    comb M (ext R k r) (k + 1) (Fin.snoc (α := fun _ => ℚ) (fun a => μ a - t * ν a) t) j =
      comb M R k μ j - t * comb M R k ν j + t * (M r j : ℚ) := by
  simp only [comb, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
    ext_self]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [ext_lt _ _ a.isLt]
  ring

/-- **The step lemma**: one Bareiss update keeps the invariant, with one more pivot. -/
theorem inv_step {st : St} {k : ℕ} {R C : ℕ → ℕ} (h : Inv M st k R C) (r v : ℕ) (hr : st.a r v ≠ 0) :
    Inv M ⟨upd st.a st.D r v, st.a r v⟩ (k + 1) (ext R k r) (ext C k v) := by
  have hdet : st.a r v = (pmat M (ext R k r) (ext C k v) (k + 1)).det := by
    rw [pmat_succ, entry_eq_det M h r v]
  refine ⟨hdet, hr, fun ρ => ?_⟩
  obtain ⟨μ, hμc, hμv⟩ := h.row ρ
  obtain ⟨ν, hνc, hνv⟩ := h.row r
  have hD : (st.D : ℚ) ≠ 0 := by exact_mod_cast h.ne
  have hsrv : (M r v : ℚ) - comb M R k ν v ≠ 0 := by
    intro h0
    have := hνv v
    rw [h0, mul_zero] at this
    exact hr (by exact_mod_cast this)
  set t := ((M ρ v : ℚ) - comb M R k μ v) / ((M r v : ℚ) - comb M R k ν v) with ht
  set μ' : Fin (k + 1) → ℚ := Fin.snoc (α := fun _ => ℚ) (fun a => μ a - t * ν a) t with hμ'
  have hcomb := comb_succ M R k r μ ν t
  have hcol : ∀ b : Fin (k + 1), (M ρ (ext C k v b) : ℚ) = comb M (ext R k r) (k + 1) μ' (ext C k v b) := by
    intro b
    rw [hμ', hcomb]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · simp only [Fin.val_last, ext_self]
      rw [ht]; field_simp; ring
    · simp only [Fin.val_castSucc, ext_lt _ _ b'.isLt]
      rw [← hμc b', ← hνc b']; ring
  refine ⟨μ', hcol, fun j => ?_⟩
  have hz := det_bord_comb M (ext R k r) (ext C k v) (k + 1) ρ j μ' hcol
  rw [← hdet] at hz
  have hnum : ((st.a r v * st.a ρ j - st.a ρ v * st.a r j : ℤ) : ℚ) =
      (st.D : ℚ) * ((st.a r v : ℚ) * ((M ρ j : ℚ) - comb M (ext R k r) (k + 1) μ' j)) := by
    rw [hμ', hcomb]
    push_cast
    rw [hνv v, hμv j, hμv v, hνv j, ht]
    field_simp
    ring
  have hint : st.a r v * st.a ρ j - st.a ρ v * st.a r j = st.D * (bord M (ext R k r) (ext C k v) (k + 1) ρ j).det := by
    have e : ((st.a r v * st.a ρ j - st.a ρ v * st.a r j : ℤ) : ℚ) =
        ((st.D * (bord M (ext R k r) (ext C k v) (k + 1) ρ j).det : ℤ) : ℚ) := by
      rw [hnum, Int.cast_mul, hz]
    exact_mod_cast e
  show ((Int.tdiv (st.a r v * st.a ρ j - st.a ρ v * st.a r j) st.D : ℤ) : ℚ) =
    (st.a r v : ℚ) * ((M ρ j : ℚ) - comb M (ext R k r) (k + 1) μ' j)
  rw [hint, Int.mul_tdiv_cancel_left _ h.ne, hz]

end Step

/-! ## The run -/

section Run
variable (M : ℕ → ℕ → ℤ) (m : ℕ)

theorem piv_some {a : ℕ → ℕ → ℤ} {v r : ℕ} (h : piv m a v = some r) : r < m ∧ a r v ≠ 0 := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  refine ⟨List.mem_range.mp h2, ?_⟩
  simpa using h1

theorem piv_none {a : ℕ → ℕ → ℤ} {v : ℕ} (h : piv m a v = none) : ∀ i < m, a i v = 0 := by
  intro i hi
  have := List.find?_eq_none.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem inv_zero (R C : ℕ → ℕ) : Inv M ⟨M, 1⟩ 0 R C := by
  refine ⟨by simp [pmat], one_ne_zero, fun ρ => ⟨fun a => a.elim0, fun b => b.elim0, fun j => ?_⟩⟩
  simp [comb]

/-- **The run invariant**: after the first `V` columns, `k ≤ V` pivots in system rows and earlier columns, and every
system row is zero in those columns. -/
theorem run_inv (V : ℕ) : ∃ (k : ℕ) (R C : ℕ → ℕ), Inv M (run m ⟨M, 1⟩ V) k R C ∧ k ≤ V ∧
    (∀ a < k, R a < m ∧ C a < V) ∧ ∀ i < m, ∀ v < V, (run m ⟨M, 1⟩ V).a i v = 0 := by
  induction V with
  | zero => exact ⟨0, fun _ => 0, fun _ => 0, inv_zero M _ _, le_rfl, fun a ha => absurd ha (by omega),
      fun _ _ v hv => absurd hv (by omega)⟩
  | succ V ih =>
    obtain ⟨k, R, C, hI, hk, hRC, hz⟩ := ih
    set st := run m ⟨M, 1⟩ V with hst
    have hrun : run m ⟨M, 1⟩ (V + 1) = step m st V := rfl
    rw [hrun]
    unfold step
    rcases hp : piv m st.a V with _ | r
    · refine ⟨k, R, C, hI, by omega, fun a ha => ⟨(hRC a ha).1, by have := (hRC a ha).2; omega⟩, fun i hi v hv => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | hv
      · exact hz i hi v hv
      · subst hv; exact piv_none m hp i hi
    · obtain ⟨hrm, hr0⟩ := piv_some m hp
      refine ⟨k + 1, ext R k r, ext C k V, inv_step M hI r V hr0, by omega, fun a ha => ?_, fun i hi v hv => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | ha
        · rw [ext_lt _ _ ha, ext_lt _ _ ha]; exact ⟨(hRC a ha).1, by have := (hRC a ha).2; omega⟩
        · subst ha; rw [ext_self, ext_self]; exact ⟨hrm, by omega⟩
      · show Int.tdiv (st.a r V * st.a i v - st.a i V * st.a r v) st.D = 0
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | hv
        · rw [hz i hi v hv, hz r hrm v hv]; simp
        · subst hv; rw [show st.a r v * st.a i v - st.a i v * st.a r v = 0 by ring]; simp

/-- **The bound** on every entry and pivot of the run, for entries of `M` bounded by `X ≥ 1`. -/
theorem run_bound (X : ℤ) (hX1 : 1 ≤ X) (hX : ∀ i j, |M i j| ≤ X) (V : ℕ) :
    (∀ ρ j, |(run m ⟨M, 1⟩ V).a ρ j| ≤ (V + 1).factorial * X ^ (V + 1)) ∧
      |(run m ⟨M, 1⟩ V).D| ≤ (V + 1).factorial * X ^ (V + 1) := by
  obtain ⟨k, R, C, hI, hk, -, -⟩ := run_inv M m V
  have hmono : ∀ a b : ℕ, a ≤ b → (a.factorial : ℤ) * X ^ a ≤ (b.factorial : ℤ) * X ^ b := by
    intro a b hab
    have h1 : (a.factorial : ℤ) ≤ b.factorial := by exact_mod_cast Nat.factorial_le hab
    have h2 : X ^ a ≤ X ^ b := pow_le_pow_right₀ hX1 hab
    have h3 : (0 : ℤ) ≤ X ^ a := pow_nonneg (by omega) a
    have h4 : (0 : ℤ) ≤ b.factorial := by exact_mod_cast (Nat.zero_le _)
    nlinarith
  refine ⟨fun ρ j => (abs_entry_le M hI X hX ρ j).trans (hmono _ _ (by omega)), ?_⟩
  rw [hI.det]
  have hb := Matrix.det_le (abv := AbsoluteValue.abs) (A := pmat M R C k) (x := X) (fun x y => by simp [pmat, hX])
  simp only [Fintype.card_fin, nsmul_eq_mul] at hb
  exact hb.trans (hmono _ _ (by omega))

end Run

/-! ## Soundness and completeness of `solve` -/

section Solve
variable (s : SysReq)

theorem amat_sys {i j : ℕ} (hi : i < s.rows.length) (hj : j < s.pts.length) :
    amat s i j = coef (s.rows.getD i (0, [], 0)) (s.pts.getD j []) := by simp [amat, hi, hj]

theorem amat_rhs {i : ℕ} (hi : i < s.rows.length) :
    amat s i s.pts.length = ((s.rows.getD i (0, [], 0)).2.2 : ℤ) := by simp [amat, hi]

theorem amat_id (v j : ℕ) :
    amat s (s.rows.length + v) j = if j < s.pts.length ∧ v = j then 1 else 0 := by simp [amat]

/-- The filtered sum of `SysSolves` as a sum over the points. -/
theorem sum_filter_zip (p : List ℤ → Bool) : ∀ (us : List (List ℤ)) (F : List ℚ), us.length = F.length →
    (((us.zip F).filter fun uf => p uf.1).map Prod.snd).sum =
      ∑ v ∈ Finset.range us.length, (if p (us.getD v []) = true then F.getD v 0 else 0)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | u :: us, f :: F, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.filter_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sum_filter_zip p us F h
    by_cases hp : p u = true
    · simp only [hp, if_true, List.map_cons, List.sum_cons, ih, List.getD_cons_zero, List.getD_cons_succ]
      ring
    · simp only [hp, Bool.false_eq_true, if_false, ih, List.getD_cons_zero, List.getD_cons_succ]
      ring

/-- `SysSolves` as row sums of the augmented matrix. -/
theorem solves_iff (F : List ℚ) : SysSolves s F ↔ F.length = s.pts.length ∧
    ∀ i < s.rows.length, ∑ v ∈ Finset.range s.pts.length, (amat s i v : ℚ) * F.getD v 0 =
      (amat s i s.pts.length : ℚ) := by
  unfold SysSolves
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨hl, fun i hi => ?_⟩
    have hmem : s.rows[i] ∈ s.rows := List.getElem_mem hi
    have h := hr _ hmem
    rw [sum_filter_zip _ _ _ hl.symm] at h
    rw [amat_rhs s hi, List.getD_eq_getElem _ _ hi, Int.cast_natCast, ← h]
    apply Finset.sum_congr rfl
    intro v hv
    rw [amat_sys s hi (Finset.mem_range.mp hv), List.getD_eq_getElem _ _ hi]
    unfold coef
    split_ifs <;> simp_all
  · rintro ⟨hl, hr⟩
    refine ⟨hl, fun row hrow => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
    have h := hr i hi
    rw [sum_filter_zip _ _ _ hl.symm]
    rw [amat_rhs s hi, List.getD_eq_getElem _ _ hi, Int.cast_natCast] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro v hv
    rw [amat_sys s hi (Finset.mem_range.mp hv), List.getD_eq_getElem _ _ hi]
    unfold coef
    split_ifs <;> simp_all

theorem final_eq : final s = run s.rows.length ⟨amat s, 1⟩ s.pts.length := rfl

/-- **Soundness**: a returned list solves every row. -/
theorem solve_sound (F : List ℚ) (h : solve s = some F) : SysSolves s F := by
  set m := s.rows.length with hm
  set n := s.pts.length with hn
  unfold solve at h
  split_ifs at h with hall
  obtain rfl := Option.some.inj h
  obtain ⟨k, R, C, hI, -, hRC, hz⟩ := run_inv (amat s) m n
  rw [← final_eq] at hI hz
  set st := final s with hst
  have hD : (st.D : ℚ) ≠ 0 := by exact_mod_cast hI.ne
  choose μ hμc hμv using hI.row
  set x : ℕ → ℚ := fun v => -(st.a (m + v) n : ℚ) / st.D with hx
  have hxv : ∀ v, x v = comb (amat s) R k (μ (m + v)) n := by
    intro v
    have h1 := hμv (m + v) n
    have h0 : amat s (m + v) n = 0 := by rw [amat_id]; simp [hn]
    rw [h0, Int.cast_zero, zero_sub] at h1
    show -(st.a (m + v) n : ℚ) / st.D = _
    rw [h1]; field_simp
  have hall' : ∀ i < m, st.a i n = 0 := by
    intro i hi
    have := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
    simpa using this
  have hrowc : ∀ i < m, ∀ j ≤ n, (amat s i j : ℚ) = comb (amat s) R k (μ i) j := by
    intro i hi j hj
    have h0 : st.a i j = 0 := by
      rcases Nat.lt_or_eq_of_le hj with hj | hj
      · exact hz i hi j hj
      · rw [hj]; exact hall' i hi
    have h1 := hμv i j
    rw [h0, Int.cast_zero] at h1
    have h2 := (mul_eq_zero.mp h1.symm).resolve_left hD
    linarith
  -- the pivot block is invertible and `M_R Λ = 1`
  set A : Matrix (Fin k) (Fin k) ℚ := (pmat (amat s) R C k).map (Int.cast : ℤ → ℚ) with hA
  have hAdet : A.det = st.D := by
    rw [hI.det, hA]
    simpa using (RingHom.map_det (Int.castRingHom ℚ) (pmat (amat s) R C k)).symm
  set Λ : Matrix (Fin n) (Fin k) ℚ := Matrix.of fun v a => μ (m + v) a with hΛ
  set MR : Matrix (Fin k) (Fin n) ℚ := Matrix.of fun a v => (amat s (R a) v : ℚ) with hMR
  set E : Matrix (Fin n) (Fin k) ℚ := Matrix.of fun v b => if C b = v then 1 else 0 with hE
  have hΛA : Λ * A = E := by
    ext v b
    have h1 := hμc (m + v) b
    rw [amat_id] at h1
    have hCb : C b < s.pts.length := (hRC b b.isLt).2
    simp only [Matrix.mul_apply, hΛ, hA, hE, Matrix.of_apply, Matrix.map_apply, pmat]
    rw [show (∑ a : Fin k, μ (m + v) a * ((amat s (R a) (C b) : ℤ) : ℚ)) = comb (amat s) R k (μ (m + v)) (C b) from rfl,
      ← h1]
    by_cases hv : (v : ℕ) = C b
    · simp [hCb, hv]
    · have hv' : C b ≠ v := fun e => hv (by rw [← e])
      simp [hv, hv']
  have hMRE : MR * E = A := by
    ext a b
    have hCb : C b < n := (hRC b b.isLt).2
    simp only [Matrix.mul_apply, hMR, hE, hA, Matrix.of_apply, Matrix.map_apply, pmat, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (⟨C b, hCb⟩ : Fin n)]
    · simp
    · intro x _ hx
      rw [if_neg]
      intro e; apply hx; ext; simp [e]
    · simp
  have hu : IsUnit A.det := by rw [hAdet]; exact isUnit_iff_ne_zero.mpr hD
  have hMRΛ : MR * Λ = 1 := by
    calc MR * Λ = MR * Λ * (A * A⁻¹) := by rw [mul_nonsing_inv A hu, Matrix.mul_one]
      _ = MR * E * A⁻¹ := by rw [← hΛA]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMRE, mul_nonsing_inv A hu]
  have hpiv : ∀ a : Fin k, ∑ v ∈ Finset.range n, (amat s (R a) v : ℚ) * x v = amat s (R a) n := by
    intro a
    rw [← Fin.sum_univ_eq_sum_range (fun v => (amat s (R a) v : ℚ) * x v) n]
    simp only [hxv, comb, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e : ∀ a' : Fin k, ∑ v : Fin n, (amat s (R a) v : ℚ) * (μ (m + v) a' * (amat s (R a') n : ℚ)) =
        (MR * Λ) a a' * (amat s (R a') n : ℚ) := by
      intro a'
      simp only [Matrix.mul_apply, hMR, hΛ, Matrix.of_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro v _; ring
    simp only [e, hMRΛ, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    simp
  rw [solves_iff]
  refine ⟨by simp, fun i hi => ?_⟩
  have hF : ∀ v ∈ Finset.range n, ((List.range n).map fun v => -((final s).a (m + v) n : ℚ) / (final s).D).getD v 0 =
      x v := by
    intro v hv
    have hv' := Finset.mem_range.mp hv
    rw [List.getD_eq_getElem _ _ (by simpa using hv')]
    simp [hx, hst]
  rw [Finset.sum_congr rfl (fun v hv => by rw [hF v hv])]
  rw [Finset.sum_congr rfl (fun v hv => by rw [hrowc i hi v (Finset.mem_range.mp hv).le])]
  rw [hrowc i hi n le_rfl]
  simp only [comb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hpiv a, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v _; ring

/-- **Completeness**: `none` only when no list solves every row. -/
theorem solve_complete (h : solve s = none) (F : List ℚ) : ¬ SysSolves s F := by
  set m := s.rows.length with hm
  set n := s.pts.length with hn
  intro hF
  rw [solves_iff] at hF
  obtain ⟨-, hrows⟩ := hF
  unfold solve at h
  split_ifs at h with hall
  obtain ⟨i, hi, hin⟩ : ∃ i < m, (final s).a i n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hall (List.all_eq_true.mpr fun i hi => by simpa using hcon i (List.mem_range.mp hi))
  obtain ⟨k, R, C, hI, -, hRC, hz⟩ := run_inv (amat s) m n
  rw [← final_eq] at hI hz
  obtain ⟨μ, -, hμv⟩ := hI.row i
  set x : ℕ → ℚ := fun v => F.getD v 0
  set D : ℚ := ((final s).D : ℚ) with hD
  have hA : ∀ v, ((final s).a i v : ℚ) * x v =
      D * ((amat s i v : ℚ) * x v) - ∑ a : Fin k, D * μ a * ((amat s (R a) v : ℚ) * x v) := by
    intro v
    rw [hμv v]
    unfold comb
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro a _; ring
  have key : ∑ v ∈ Finset.range n, ((final s).a i v : ℚ) * x v = (final s).a i n := by
    rw [Finset.sum_congr rfl (fun v _ => hA v), Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.mul_sum]
    simp only [← Finset.mul_sum]
    rw [hrows i hi, hμv n]
    have e : ∀ a : Fin k, ∑ v ∈ Finset.range n, (amat s (R a) v : ℚ) * x v = amat s (R a) n :=
      fun a => hrows (R a) (hRC a a.isLt).1
    simp only [e, comb, Finset.mul_sum]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro a _; ring
  have h0 : ∑ v ∈ Finset.range n, ((final s).a i v : ℚ) * x v = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hz i hi v (Finset.mem_range.mp hv)]; simp
  exact hin (by exact_mod_cast key.symm.trans h0)

end Solve

end NearCubicGates.Close.Solve
