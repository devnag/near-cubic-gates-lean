import Proof.Wire_3_5.DirectMoment
import Proof.Wire_3_5.NormDomination

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared Finset Matrix

variable {N : ℕ}

/-- A sum over `(m+1)`-tuples splits off the first entry. -/
theorem sum_fun_succ {n : ℕ} {α : Type} [Fintype α] (f : (Fin (n + 1) → α) → ℝ) :
    ∑ w, f w = ∑ a, ∑ w : Fin n → α, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over `(m+1)`-tuples splits off the last entry. -/
theorem sum_fun_snoc {n : ℕ} {α : Type} [Fintype α] (f : (Fin (n + 1) → α) → ℝ) :
    ∑ w, f w = ∑ v : Fin n → α, ∑ x, f (Fin.snoc v x) := by
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The product `A₀A₁⋯A_{m−1}`. -/
def prodList (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (List.ofFn fun k : Fin m => A k).prod

/-- The value of a path `w₀ → w₁ → ⋯ → w_m` through `A₀, …, A_{m−1}`. -/
def pathVal (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (w : Fin (m + 1) → Fin N) : ℝ :=
  ∏ k : Fin m, A k (w k.castSucc) (w k.succ)

theorem prodList_succ (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) :
    prodList (m + 1) A = A 0 * prodList m (fun k => A (k + 1)) := by
  simp [prodList, List.ofFn_succ, Fin.val_succ]

theorem pathVal_cons (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (d : Fin N) (w : Fin (m + 1) → Fin N) :
    pathVal (m + 1) A (Fin.cons d w) = A 0 d (w 0) * pathVal m (fun k => A (k + 1)) w := by
  unfold pathVal
  rw [Fin.prod_univ_succ]
  congr 1

/-- **A matrix product's entry is the sum over paths.** -/
theorem prodList_apply : ∀ (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) (a b : Fin N),
    prodList m A a b = ∑ w : Fin (m + 1) → Fin N, if w 0 = a ∧ w (Fin.last m) = b then pathVal m A w else 0
  | 0, A, a, b => by
    rw [sum_fun_succ]
    simp only [prodList, List.ofFn_zero, List.prod_nil, Matrix.one_apply, Fin.cons_zero, Fin.last_zero,
      pathVal, Finset.univ_eq_empty, Finset.prod_empty]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hab (h1 ▸ h2)
  | m + 1, A, a, b => by
    rw [prodList_succ, Matrix.mul_apply]
    simp_rw [prodList_apply m (fun k => A (k + 1))]
    rw [sum_fun_succ]
    simp only [Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, pathVal_cons]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have lhs : ∀ w : Fin (m + 1) → Fin N,
        (∑ c : Fin N, A 0 a c * if w 0 = c ∧ w (Fin.last m) = b then pathVal m (fun k => A (k + 1)) w else 0) =
          if w (Fin.last m) = b then A 0 a (w 0) * pathVal m (fun k => A (k + 1)) w else 0 := by
      intro w
      rw [Finset.sum_eq_single (w 0)]
      · by_cases hb : w (Fin.last m) = b <;> simp [hb]
      · intro c _ hc
        have : ¬ (w 0 = c ∧ w (Fin.last m) = b) := fun h => hc h.1.symm
        simp [this]
      · simp
    have rhs : ∀ w : Fin (m + 1) → Fin N,
        (∑ d : Fin N, if d = a ∧ w (Fin.last m) = b then A 0 d (w 0) * pathVal m (fun k => A (k + 1)) w else 0) =
          if w (Fin.last m) = b then A 0 a (w 0) * pathVal m (fun k => A (k + 1)) w else 0 := by
      intro w
      rw [Finset.sum_eq_single a]
      · by_cases hb : w (Fin.last m) = b <;> simp [hb]
      · intro d _ hd
        have : ¬ (d = a ∧ w (Fin.last m) = b) := fun h => hd h.1
        simp [this]
      · simp
    rw [Finset.sum_comm (f := fun d w => if d = a ∧ w (Fin.last m) = b then
      A 0 d (w 0) * pathVal m (fun k => A (k + 1)) w else 0)]
    exact Finset.sum_congr rfl fun w _ => (lhs w).trans (rhs w).symm

/-- The cyclic successor of a slot (`(k+1) mod (m+1)`), as in `WalkCount.nextSlot`. -/
theorem snoc_succ (m : ℕ) (v : Fin (m + 1) → Fin N) (k : Fin (m + 1)) :
    Fin.snoc (α := fun _ => Fin N) v (v 0) k.succ = v ⟨(k.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ := by
  by_cases hk : k.val + 1 < m + 1
  · have h1 : k.succ = Fin.castSucc ⟨k.val + 1, hk⟩ := Fin.ext (by simp)
    rw [h1, Fin.snoc_castSucc]
    congr 1
    exact Fin.ext (by simp [Nat.mod_eq_of_lt hk])
  · have hkm : k = Fin.last m := Fin.ext (by simp; omega)
    subst hkm
    rw [Fin.succ_last, Fin.snoc_last]
    congr 1
    exact Fin.ext (by simp)

/-- **The trace of a product is the sum over closed walks** (`m+1` factors, slot `k` read at `(v_k, v_{k+1 mod m+1})`). -/
theorem trace_prodList (m : ℕ) (A : ℕ → Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace (prodList (m + 1) A) =
      ∑ v : Fin (m + 1) → Fin N, ∏ k : Fin (m + 1),
        A k (v k) (v ⟨(k.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩) := by
  unfold Matrix.trace Matrix.diag
  simp_rw [prodList_apply]
  rw [Finset.sum_comm, sum_fun_snoc]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm, Finset.sum_eq_single (v 0)]
  · rw [Finset.sum_eq_single (v 0)]
    · have h0 : Fin.snoc (α := fun _ => Fin N) v (v 0) (0 : Fin (m + 2)) = v 0 := by
        have : (0 : Fin (m + 2)) = Fin.castSucc (0 : Fin (m + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
      rw [if_pos ⟨h0, Fin.snoc_last _ _⟩]
      unfold pathVal
      apply Finset.prod_congr rfl
      intro k _
      rw [Fin.snoc_castSucc, snoc_succ]
    · intro a _ ha
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply ha
      rw [← h2, Fin.snoc_last]
    · simp
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    rintro ⟨h1, _⟩
    have h0 : Fin.snoc (α := fun _ => Fin N) v a (0 : Fin (m + 2)) = v 0 := by
      have : (0 : Fin (m + 2)) = Fin.castSucc (0 : Fin (m + 1)) := rfl
      rw [this, Fin.snoc_castSucc]
    exact hx (h1.symm.trans h0)
  · simp

/-! ## The sampling error matrix and the walk moment -/

def errMatrix {Q : ℕ} (D : Cell N → ℝ) (S : Fin Q → Cell N) : Matrix (Fin N) (Fin N) ℝ :=
  fun u v => Ecell D S (u, v)

/-- The alternating factors `E, Eᵀ, E, Eᵀ, …` of `(EEᵀ)^h`. -/
def altFactor (E : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : Matrix (Fin N) (Fin N) ℝ := if k % 2 = 0 then E else Eᵀ

theorem prodList_alt_eight (E : Matrix (Fin N) (Fin N) ℝ) : prodList 8 (altFactor E) = (E * Eᵀ) ^ 4 := by
  simp [prodList, List.ofFn_succ, altFactor, pow_succ, mul_assoc]

/-- **The walk-sum moment is the trace moment**: `walkMoment = tr((EEᵀ)⁴)` at `2h = 8` slots. -/
theorem walkMoment_eq_trace {Q : ℕ} (D : Cell N → ℝ) (S : Fin Q → Cell N) :
    walkMoment (L := 8) (by norm_num) D S = Matrix.trace ((errMatrix D S * (errMatrix D S)ᵀ) ^ 4) := by
  rw [← prodList_alt_eight, trace_prodList 7 (altFactor (errMatrix D S))]
  unfold walkMoment
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.prod_congr rfl
  intro k _
  unfold cellOf altFactor nextSlot errMatrix
  split_ifs <;> rfl

/-- `tr((EᵀE)⁴) = tr((EEᵀ)⁴)`. -/
theorem trace_transpose_mul_pow (E : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace ((Eᵀ * E) ^ 4) = Matrix.trace ((E * Eᵀ) ^ 4) := by
  have h1 : (Eᵀ * E) ^ 4 = Eᵀ * (E * Eᵀ * E * Eᵀ * E * Eᵀ * E) := by simp [pow_succ, mul_assoc]
  have h2 : (E * Eᵀ) ^ 4 = (E * Eᵀ * E * Eᵀ * E * Eᵀ * E) * Eᵀ := by simp [pow_succ, mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm]

end NearCubicWires.WireExponent3_5.Sampler
