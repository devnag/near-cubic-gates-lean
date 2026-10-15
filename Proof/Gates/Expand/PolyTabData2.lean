import Proof.Gates.Expand.PolyTabData

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

theorem flatMap_getElem?_const {α β : Type} (f : α → List β) (c : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = c) → ∀ (b i : ℕ) (hb : b < l.length), i < c →
      (l.flatMap f)[c * b + i]? = (f l[b])[i]?
  | [], _, b, i, hb, _ => by simp at hb
  | a :: l, h, b, i, hb, hi => by
    rw [List.flatMap_cons]
    cases b with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [h a (by simp)]; exact hi)]
    | succ b =>
      have ha := h a (by simp)
      rw [List.getElem?_append_right (by rw [ha]; nlinarith)]
      have e : c * (b + 1) + i - (f a).length = c * b + i := by rw [ha]; ring_nf; omega
      rw [e, flatMap_getElem?_const f c l (fun x hx => h x (by simp [hx])) b i (by simpa using hb) hi]
      simp

def wSign (z : ℤ) : ℕ := if z < 0 then 1 else 0

theorem intN_flat_sign {n : ℕ} (w : Fin n → ℤ) (i : Fin n) :
    ((List.ofFn w).flatMap intN)[2 * i.val]? = some (wSign (w i)) := by
  have := flatMap_getElem?_const intN 2 (List.ofFn w) (fun _ _ => by simp [intN]) i.val 0 (by simp) (by norm_num)
  rw [Nat.add_zero] at this; rw [this]; simp [intN, wSign]

theorem intN_flat_mag {n : ℕ} (w : Fin n → ℤ) (i : Fin n) :
    ((List.ofFn w).flatMap intN)[2 * i.val + 1]? = some (w i).natAbs := by
  rw [flatMap_getElem?_const intN 2 (List.ofFn w) (fun _ _ => by simp [intN]) i.val 1 (by simp) (by norm_num)]
  simp [intN]

/-- Field `j` of gate `g`'s block. -/
theorem preN_gate (r : TabReq) (g : Fin r.G) (j : ℕ) (hj : j < 2 * r.n + 3) :
    (preN r)[5 + g.val * (2 * r.n + 3) + j]? = (gateN (r.gates g))[j]? := by
  have e : preN r = [r.n, r.k, r.s, r.B, r.G] ++ ((List.ofFn r.gates).flatMap gateN ++ ([r.k] ++ innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN)) := by simp [preN]
  have hl : ((List.ofFn r.gates).flatMap gateN).length = r.G * (2 * r.n + 3) := gates_length r
  have hlt : g.val * (2 * r.n + 3) + j < r.G * (2 * r.n + 3) := by
    have := g.isLt; nlinarith
  rw [e, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons, List.length_nil, show 5 + g.val * (2 * r.n + 3) + j - 5 = (2 * r.n + 3) * g.val + j by
    ring_nf; omega]
  rw [List.getElem?_append_left (by rw [hl]; nlinarith)]
  rw [flatMap_getElem?_const gateN (2 * r.n + 3) _ (fun x _ => gateN_length x) g.val j (by simp) hj]
  simp

theorem intN_len {n : ℕ} (w : Fin n → ℤ) : ((List.ofFn w).flatMap intN).length = 2 * n := by
  rw [flatMap_len_const _ _ 2 (fun _ _ => by simp [intN])]; simp; ring

theorem preN_wsign (r : TabReq) (g : Fin r.G) (i : Fin r.n) :
    (preN r)[5 + g.val * (2 * r.n + 3) + (1 + 2 * i.val)]? = some (wSign ((r.gates g).weight i)) := by
  rw [preN_gate r g _ (by omega)]
  have hl := intN_len (r.gates g).weight
  simp only [gateN, List.getElem?_cons_succ, Nat.add_comm 1]
  rw [List.getElem?_append_left (by omega)]
  exact intN_flat_sign _ i

theorem preN_wmag (r : TabReq) (g : Fin r.G) (i : Fin r.n) :
    (preN r)[5 + g.val * (2 * r.n + 3) + (2 + 2 * i.val)]? = some ((r.gates g).weight i).natAbs := by
  rw [preN_gate r g _ (by omega)]
  simp only [gateN, show 2 + 2 * i.val = (2 * i.val + 1) + 1 by ring, List.getElem?_cons_succ]
  have hl := intN_len (r.gates g).weight
  rw [List.getElem?_append_left (by omega)]
  exact intN_flat_mag _ i

theorem preN_tsign (r : TabReq) (g : Fin r.G) :
    (preN r)[5 + g.val * (2 * r.n + 3) + (1 + 2 * r.n)]? = some (wSign (r.gates g).threshold) := by
  rw [preN_gate r g _ (by omega)]
  have hl := intN_len (r.gates g).weight
  simp only [gateN, Nat.add_comm 1, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]
  simp [intN, wSign]

theorem preN_tmag (r : TabReq) (g : Fin r.G) :
    (preN r)[5 + g.val * (2 * r.n + 3) + (2 + 2 * r.n)]? = some (r.gates g).threshold.natAbs := by
  rw [preN_gate r g _ (by omega)]
  have hl := intN_len (r.gates g).weight
  simp only [gateN, show 2 + 2 * r.n = (2 * r.n + 1) + 1 by ring, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), hl, show 2 * r.n + 1 - 2 * r.n = 1 by omega]
  simp [intN]

theorem preN_inner (r : TabReq) (j : Fin r.k) :
    (preN r)[pk r + 1 + j.val]? = some (r.layout.symm (.inl j)).val := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k]) ++ (innerL r ++
      ([r.s] ++ outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN)) := by simp [preN]
  have hA : ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k]).length = pk r + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, gates_length, pk]
  rw [e, List.getElem?_append_right (by omega), hA, show pk r + 1 + j.val - (pk r + 1) = j.val by omega]
  rw [List.getElem?_append_left (by simp [innerL])]
  simp [innerL]

theorem preN_outer (r : TabReq) (t : Fin r.s) :
    (preN r)[ps r + 1 + t.val]? = some (r.layout.symm (.inr t)).val := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s]) ++
      (outerL r ++ ([2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN)) := by simp [preN]
  have hA : ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++
      [r.s]).length = ps r + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, List.length_ofFn, ps, pk]
    omega
  rw [e, List.getElem?_append_right (by omega), hA, show ps r + 1 + t.val - (ps r + 1) = t.val by omega]
  rw [List.getElem?_append_left (by simp [outerL])]
  simp [outerL]

theorem preN_role (r : TabReq) (v : Fin r.V) :
    (preN r)[pV r + 1 + 2 * v.val]? = some (r.role v).gate.val ∧
    (preN r)[pV r + 1 + 2 * v.val + 1]? = some (if (r.role v).reference then 1 else 0) := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V]) ++ (List.ofFn r.role).flatMap roleN := by simp [preN]
  have hA : ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V]).length = pV r + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, bitsL,
      List.length_ofFn, pV, pN, ps, pk]; omega
  rw [e]
  constructor
  · rw [List.getElem?_append_right (by omega), hA, show pV r + 1 + 2 * v.val - (pV r + 1) = 2 * v.val + 0 by omega,
      flatMap_getElem?_const roleN 2 _ (fun _ _ => by simp [roleN]) v.val 0 (by simp) (by norm_num)]
    simp [roleN]
  · rw [List.getElem?_append_right (by omega), hA, show pV r + 1 + 2 * v.val + 1 - (pV r + 1) = 2 * v.val + 1 by omega,
      flatMap_getElem?_const roleN 2 _ (fun _ _ => by simp [roleN]) v.val 1 (by simp) (by norm_num)]
    simp [roleN]

end NearCubicGates.Close.Expand.PolyTab
