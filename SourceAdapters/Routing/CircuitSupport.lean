import SourceAdapters.Routing.CircuitTerms

/-! Syntactic reads imply formal polynomial support inside the fixed translation bank. -/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open Polynomial
variable {F : Type} [Field F]

def Supports (bank : List ℕ) (p : MP F) : Prop :=
  ∀ v ∈ p.vars, match v with | none => True | some b => b ∈ bank

theorem supports_C (bank : List ℕ) (c : F) : Supports bank (MvPolynomial.C c) := by
  intro v hv
  simp only [MvPolynomial.vars_C] at hv
  simp at hv

theorem supports_one (bank : List ℕ) : Supports bank (1 : MP F) := by
  simpa only [map_one] using supports_C bank (1 : F)

theorem supports_zero (bank : List ℕ) : Supports bank (0 : MP F) := by
  simpa only [map_zero] using supports_C bank (0 : F)

theorem supports_X (bank : List ℕ) (v : Vars)
    (h : match v with | none => True | some b => b ∈ bank) : Supports bank (MvPolynomial.X v : MP F) := by
  intro u hu
  have he : u = v := by simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hu
  simpa only [he] using h

theorem Supports.add {bank : List ℕ} {p q : MP F} (hp : Supports bank p) (hq : Supports bank q) :
    Supports bank (p + q) := by
  intro v hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset p q hv) with h | h
  · exact hp v h
  · exact hq v h

theorem Supports.mul {bank : List ℕ} {p q : MP F} (hp : Supports bank p) (hq : Supports bank q) :
    Supports bank (p * q) := by
  intro v hv
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul p q hv) with h | h
  · exact hp v h
  · exact hq v h

theorem Supports.pow {bank : List ℕ} {p : MP F} (hp : Supports bank p) (n : ℕ) :
    Supports bank (p ^ n) := by
  intro v hv
  exact hp v (MvPolynomial.vars_pow p n hv)

theorem supports_liftX (bank : List ℕ) (p : F[X]) : Supports bank (liftX p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [liftX, Polynomial.eval₂_add] using hp.add hq
  | monomial n a =>
      simpa only [liftX, Polynomial.eval₂_monomial] using
        (supports_C bank a).mul ((supports_X bank none trivial).pow n)

theorem supports_prod {ι : Type} (bank : List ℕ) (s : Finset ι) (f : ι → MP F)
    (h : ∀ i ∈ s, Supports bank (f i)) : Supports bank (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using supports_one (F := F) bank
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem supports_selector {m : ℕ} {e : Fin m → F} (bank : List ℕ)
    (coords : Coordinates m e) (p : Pattern m) : Supports bank (selector coords p) := by
  unfold selector
  apply supports_prod
  intro a _
  cases hp : p a with
  | none => exact supports_one bank
  | some b =>
      cases b with
      | true => exact supports_liftX bank _
      | false => exact (supports_one bank).add (supports_liftX bank _)

theorem supports_expr (bank : List ℕ) (E : Expr F) (h : ReadsIn bank E) : Supports bank E.poly := by
  induction E with
  | const c => exact supports_C bank c
  | read v => exact supports_X bank v h
  | add a b ia ib => exact (ia h.1).add (ib h.2)
  | mul a b ia ib => exact (ia h.1).mul (ib h.2)
  | square a ia => exact (ia h).pow 2

theorem supports_sum (bank : List ℕ) (ps : List (MP F))
    (h : ∀ p ∈ ps, Supports bank p) : Supports bank ps.sum := by
  induction ps with
  | nil => exact supports_zero bank
  | cons p ps ih =>
      exact (h p (by simp)).add (ih (fun q hq => h q (by simp [hq])))

/-- The generic compiler also has no undeclared read variable in its formal polynomial. -/
theorem compileTerms_support (l : Layout) {e : Fin l.m → F} (coords : Coordinates l.m e)
    (items : List (Item l.m F)) (hr : ∀ item ∈ items, ReadsIn (globalBank l) item.2) :
    Supports (globalBank l) (emit coords (termList items)) := by
  unfold emit termList
  rw [List.map_map]
  apply supports_sum
  intro p hp
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hp
  exact (supports_selector (globalBank l) coords item.1).mul (supports_expr _ _ (hr item hi))

end NearCubicGates.Adapters.Routing.Circuit
end
