import SourceAdapters.Routing.TermsMachineEncoding

/-! The construction in `lem:generator`: exact row-major addresses of supplied coordinate masks. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.TermsMachine

open Joins

theorem flatMap_getD_uniform {α β : Type} (xs : List α) (g : α → List β)
    (m a r : ℕ) (d : β) (hg : ∀ x ∈ xs, (g x).length = m)
    (ha : a < xs.length) (hr : r < m) :
    (xs.flatMap g).getD (a * m + r) d = (g xs[a]).getD r d := by
  induction xs generalizing a with
  | nil => simp at ha
  | cons x xs ih =>
      have hx : (g x).length = m := hg x (by simp)
      have hxs : ∀ y ∈ xs, (g y).length = m := fun y hy => hg y (by simp [hy])
      cases a with
      | zero =>
          simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega)]
      | succ a =>
          have ha' : a < xs.length := by simp at ha; omega
          have he : ((a + 1) * m + r) - (g x).length = a * m + r := by
            rw [hx, Nat.add_mul, Nat.one_mul]
            omega
          have hright : (g x).length ≤ (a + 1) * m + r := by
            rw [hx, Nat.add_mul, Nat.one_mul]
            omega
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          calc
            (g x ++ xs.flatMap g).getD ((a + 1) * m + r) d =
                (xs.flatMap g).getD (a * m + r) d := by
              simp only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right hright, he]
            _ = (g xs[a]).getD r d := ih a hxs ha'

theorem coordMasks_get (p : TermsReq) (h : TermsOk p) (a r : Fin p.l.m) :
    (coordMasks p h).getD (a.val * p.l.m + r.val) 0 =
      termsMask p h (termsCoeff p h a r) := by
  unfold coordMasks
  rw [flatMap_getD_uniform (List.finRange p.l.m)
    (fun a => (List.finRange p.l.m).map fun r => termsMask p h (termsCoeff p h a r))
    p.l.m a.val r.val 0 (by simp) (by simp) r.isLt]
  simp only [List.getElem_finRange]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

end NearCubicGates.Adapters.Routing.TermsMachine
