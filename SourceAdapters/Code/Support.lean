import SourceAdapters.Code.Basic

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": extracting parity supports from binary linearity. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicGates.Published.CW19Code

private theorem fold_xor_acc {α : Type} (x : α → Bool) (xs : List α) (b : Bool) :
    xs.foldl (fun p i => xor p (x i)) b =
      xor b (xs.foldl (fun p i => xor p (x i)) false) := by
  induction xs generalizing b with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (xor false (x i))]
    cases b <;> cases x i <;> cases xs.foldl (fun p i => xor p (x i)) false <;> rfl

theorem parityOn_insert {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (x : BitInput n) : parityOn (insert i S) x = xor (x i) (parityOn S x) := by
  unfold parityOn
  rw [(Finset.toList_insert hi).foldl_eq' (fun a _ b _ c => by
    cases c <;> cases x a <;> cases x b <;> rfl) false]
  simp only [List.foldl_cons, Bool.false_xor]
  exact fold_xor_acc x S.toList (x i)

theorem parityOn_filter {n : ℕ} (S : Finset (Fin n)) (p : Fin n → Prop)
    [DecidablePred p] (x : BitInput n) :
    parityOn (S.filter p) x = parityOn S (fun i => if p i then x i else false) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [parityOn]
  | @insert i S hi ih =>
    have hif : i ∉ S.filter p := fun h => hi (Finset.mem_filter.mp h).1
    by_cases hp : p i
    · simp [Finset.filter_insert, hp, parityOn_insert, hi, hif, ih]
    · simp [Finset.filter_insert, hp, parityOn_insert, hi, ih]

/-- A coordinate vector of the source F₂ vector space. -/
def unitVector {n : ℕ} (i : Fin n) : BitInput n := fun j => decide (j = i)

/-- Restriction to a coordinate set, with zero outside it. -/
def mask {n : ℕ} (S : Finset (Fin n)) (x : BitInput n) : BitInput n :=
  fun j => if j ∈ S then x j else false

private theorem linear_mask {n : ℕ} (f : BitInput n → Bool)
    (hzero : f (fun _ => false) = false)
    (hadd : ∀ x y, f (fun j => xor (x j) (y j)) = xor (f x) (f y))
    (S : Finset (Fin n)) (x : BitInput n) :
    f (mask S x) = parityOn S (fun i => if f (unitVector i) then x i else false) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hm : mask (∅ : Finset (Fin n)) x = fun _ => false := by
      funext j
      simp [mask]
    rw [hm, hzero]
    simp [parityOn]
  | @insert i S hi ih =>
    rw [parityOn_insert S i hi]
    cases hx : x i with
    | false =>
      have hm : mask (insert i S) x = mask S x := by
        funext j
        by_cases hji : j = i
        · subst j; simp [mask, hi, hx]
        · simp [mask, hji]
      rw [hm, ih]
      cases f (unitVector i) <;> simp
    | true =>
      have hm : mask (insert i S) x = fun j => xor (unitVector i j) (mask S x j) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [mask, hi, hx, unitVector]
        · simp [mask, hji, unitVector]
      rw [hm, hadd, ih]
      cases f (unitVector i) <;> simp

/-- The values of a linear functional on basis vectors determine its support.
No efficiency assumption is made about constructing this finite set. -/
noncomputable def functionalSupport {n : ℕ} (f : BitInput n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f (unitVector i) = true

theorem linear_eq_parityOn {n : ℕ} (f : BitInput n → Bool)
    (hzero : f (fun _ => false) = false)
    (hadd : ∀ x y, f (fun j => xor (x j) (y j)) = xor (f x) (f y))
    (x : BitInput n) : f x = parityOn (functionalSupport f) x := by
  have h := linear_mask f hzero hadd Finset.univ x
  have hm : mask Finset.univ x = x := by
    funext j
    simp [mask]
  rw [hm] at h
  simpa [functionalSupport, parityOn_filter] using h

noncomputable def sourceSupport (F : BinaryFamily) (n : ℕ) (j : Fin (F.length n)) :
    Finset (Fin n) := functionalSupport (fun x => F.encode n x j)

theorem sourceSupport_enc (F : BinaryFamily) (hlinear : IsLinear F)
    (n : ℕ) (x : BitInput n) (j : Fin (F.length n)) :
    F.encode n x j = parityOn (sourceSupport F n j) x := by
  change (fun u => F.encode n u j) x = parityOn (functionalSupport (fun u => F.encode n u j)) x
  apply linear_eq_parityOn (fun u => F.encode n u j)
  · exact congrFun (hlinear.1 n) j
  · intro u v
    exact congrFun (hlinear.2 n u v) j

end NearCubicGates.Adapters.Code
