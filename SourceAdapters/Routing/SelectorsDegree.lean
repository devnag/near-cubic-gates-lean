import SourceAdapters.Joins.AffineRouting

/-! Elementary bounds for the actual formal weighted degree.-/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.Selectors

open scoped BigOperators Pointwise

variable {F σ : Type*} [CommSemiring F]

theorem degree_le_iff (w : σ → ℕ) (p : MvPolynomial σ F) (d : ℕ) :
    p.weightedTotalDegree w ≤ d ↔ ∀ s ∈ p.support, Finsupp.weight w s ≤ d :=
  Finset.sup_le_iff

theorem degree_C (w : σ → ℕ) (c : F) :
    (MvPolynomial.C c).weightedTotalDegree w ≤ 0 := by
  classical
  rw [degree_le_iff]
  intro s hs
  have h : s = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)
  subst s
  simp

theorem degree_X [Nontrivial F] (w : σ → ℕ) (v : σ) :
    (MvPolynomial.X v : MvPolynomial σ F).weightedTotalDegree w = w v := by
  classical
  simp [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X, Finsupp.weight_single]

theorem degree_add (w : σ → ℕ) {p q : MvPolynomial σ F} {d : ℕ}
    (hp : p.weightedTotalDegree w ≤ d) (hq : q.weightedTotalDegree w ≤ d) :
    (p + q).weightedTotalDegree w ≤ d := by
  classical
  rw [degree_le_iff] at *
  intro s hs
  rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
  · exact hp s h
  · exact hq s h

theorem degree_mul (w : σ → ℕ) {p q : MvPolynomial σ F} {a b : ℕ}
    (hp : p.weightedTotalDegree w ≤ a) (hq : q.weightedTotalDegree w ≤ b) :
    (p * q).weightedTotalDegree w ≤ a + b := by
  classical
  rw [degree_le_iff] at *
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hs)
  rw [map_add]
  exact Nat.add_le_add (hp u hu) (hq v hv)

theorem degree_one (w : σ → ℕ) :
    (1 : MvPolynomial σ F).weightedTotalDegree w ≤ 0 := by
  simpa only [MvPolynomial.C_1] using degree_C w (1 : F)

theorem degree_zero (w : σ → ℕ) :
    (0 : MvPolynomial σ F).weightedTotalDegree w ≤ 0 := by
  simp [MvPolynomial.weightedTotalDegree_zero]

theorem degree_pow (w : σ → ℕ) {p : MvPolynomial σ F} {d : ℕ}
    (hp : p.weightedTotalDegree w ≤ d) (n : ℕ) :
    (p ^ n).weightedTotalDegree w ≤ n * d := by
  induction n with
  | zero => simpa using degree_one (F := F) w
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using degree_mul w ih hp

theorem degree_sum {ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (p : ι → MvPolynomial σ F) (d : ℕ)
    (hp : ∀ i ∈ s, (p i).weightedTotalDegree w ≤ d) :
    (∑ i ∈ s, p i).weightedTotalDegree w ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (degree_zero (F := F) w).trans (Nat.zero_le d)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact degree_add w (hp i (Finset.mem_insert_self i s))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem degree_prod {ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (p : ι → MvPolynomial σ F) (d : ℕ)
    (hp : ∀ i ∈ s, (p i).weightedTotalDegree w ≤ d) :
    (∏ i ∈ s, p i).weightedTotalDegree w ≤ s.card * d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degree_one (F := F) w
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul]
    exact (degree_mul w (hp i (Finset.mem_insert_self i s))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))).trans (by omega)

end NearCubicGates.Adapters.Routing.Selectors
