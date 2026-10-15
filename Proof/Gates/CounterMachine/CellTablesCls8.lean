import Proof.Gates.CounterMachine.CellTablesCls7

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ}

/-- The class unit. -/
def Gc (r : CellReq B1 B2 cT) : ℕ := 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (2 * Jmax r.c.n)

theorem Gc_pos (r : CellReq B1 B2 cT) : 1 ≤ Gc r :=
  Nat.mul_le_mul Nat.one_le_two_pow (Nat.one_le_pow _ _ (by omega)) |>.trans_eq' rfl

theorem flatMap_len_le {α β : Type} (l : List α) (f : α → List β) (B : ℕ) (h : ∀ a ∈ l, (f a).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    rw [Nat.succ_mul]; omega

theorem pD_le (r : CellReq B1 B2 cT) (q : ℕ) (hq : q ∈ r.p.primes) :
    q ^ dOf r.c r.p ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n) * (r.c.n + 1) ^ 2 := by
  have sz := sizes r
  have hqT : q ≤ r.c.n + 1 := by have := (sz.q q hq).1; have := sz.P; omega
  calc q ^ dOf r.c r.p ≤ (r.c.n + 1) ^ dOf r.c r.p := Nat.pow_le_pow_left hqT _
    _ ≤ (r.c.n + 1) ^ (2 * Jmax r.c.n + 2) := Nat.pow_le_pow_right (by omega) sz.DJ
    _ = _ := by rw [pow_add]

theorem reqIds_le (r : CellReq B1 B2 cT) :
    (reqIds r.c r.p).length ≤ (8 + 4 * zeta) * (r.c.n + 1) ^ (2 * Jmax r.c.n) * (r.c.n + 1) ^ (b0Of B1 B2 + 3) := by
  have sz := sizes r
  set T := r.c.n + 1 with hT
  have hT1 : 1 ≤ T := by omega
  set JJ := T ^ (2 * Jmax r.c.n) with hJJ
  have hJJ1 : 1 ≤ JJ := Nat.one_le_pow _ _ hT1
  rw [← enum_eq, List.length_append]
  have hparts : (parts r.c).length ≤ 2 := by unfold parts; split <;> simp
  have h1 : ((parts r.c).flatMap fun part => (r.p.primes.sort (· ≤ ·)).flatMap fun q =>
      (List.range (q ^ dOf r.c r.p)).map (resId r.c r.p part q)).length ≤ 2 * (T * (JJ * T ^ 2)) := by
    refine (flatMap_len_le _ _ (T * (JJ * T ^ 2)) (fun part _ => ?_)).trans (Nat.mul_le_mul_right _ hparts)
    refine (flatMap_len_le _ _ (JJ * T ^ 2) (fun q hq => ?_)).trans (Nat.mul_le_mul_right _ sz.np)
    simp only [List.length_map, List.length_range]
    have := pD_le r q ((Finset.mem_sort _).mp hq)
    rw [← hT] at this
    exact this
  have h2 : ((List.range (roleCount r.c.kind)).flatMap (momIds r.p.J)).length ≤ 2 * (r.p.J + 1) := by
    have e : ((List.range (roleCount r.c.kind)).flatMap (momIds r.p.J)).length = roleCount r.c.kind * (r.p.J + 1) := by
      simp [List.length_flatMap, momIds]
    rw [e]; exact Nat.mul_le_mul_right _ sz.rc
  have hJ := sz.JX
  have hX := Z_le r
  rw [← hT] at hX
  have hb : 1 ≤ T ^ b0Of B1 B2 := Nat.one_le_pow _ _ hT1
  have e1 : T * (JJ * T ^ 2) = JJ * T ^ 3 := by ring
  have e2 : T ^ 3 ≤ T ^ (b0Of B1 B2 + 3) := Nat.pow_le_pow_right hT1 (by omega)
  have e3 : T ^ b0Of B1 B2 ≤ T ^ (b0Of B1 B2 + 3) := Nat.pow_le_pow_right hT1 (by omega)
  have e4 : JJ * T ^ 3 ≤ JJ * T ^ (b0Of B1 B2 + 3) := Nat.mul_le_mul_left _ e2
  have e5 : T ^ (b0Of B1 B2 + 3) ≤ JJ * T ^ (b0Of B1 B2 + 3) := Nat.le_mul_of_pos_left _ hJJ1
  have e6 : (8 + 4 * zeta) * JJ * T ^ (b0Of B1 B2 + 3) = 8 * (JJ * T ^ (b0Of B1 B2 + 3)) +
      4 * (zeta * (JJ * T ^ (b0Of B1 B2 + 3))) := by ring
  have e7 : zeta * T ^ b0Of B1 B2 ≤ zeta * (JJ * T ^ (b0Of B1 B2 + 3)) := Nat.mul_le_mul_left _ (e3.trans e5)
  have e8 : 1 ≤ T ^ (b0Of B1 B2 + 3) := Nat.one_le_pow _ _ hT1
  refine le_trans (Nat.add_le_add h1 h2) ?_
  rw [e6]
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
