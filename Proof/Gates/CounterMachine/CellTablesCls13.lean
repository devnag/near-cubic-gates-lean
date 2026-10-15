import Proof.Gates.CounterMachine.CellTablesCls12

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

/-- The set-up costs by one size `V` (`V` dominates every size constant and register value). -/
theorem setup_le (z : Sz) (L V : ℕ) (hV : z.W L + z.Lk L + z.Bk L + z.a1 + z.a2 + z.a3 + z.c1 + z.c2 + z.c3 + 1 ≤ V) :
    costA z L + 1 + (costB VV MM (z.W L) (z.Lk L) (z.Bk L) + 1 + costC L (z.W L) (z.Lk L) (z.Bk L)) ≤
      8000 * (L + 1) * V := by
  unfold costA costB costC
  have h1 : L * (60 * z.W L + 11 * z.c1 + 8) ≤ L * (71 * V) := Nat.mul_le_mul_left _ (by omega)
  have h2 : L * (60 * z.Lk L + 11 * z.c2 + 8) ≤ L * (71 * V) := Nat.mul_le_mul_left _ (by omega)
  have h3 : L * (60 * z.Bk L + 11 * z.c3 + 8) ≤ L * (71 * V) := Nat.mul_le_mul_left _ (by omega)
  have e : 8000 * (L + 1) * V = 8000 * (L * V) + 8000 * V := by ring
  have e2 : L * (71 * V) = 71 * (L * V) := by ring
  have hLV : L ≤ L * V := Nat.le_mul_of_pos_right _ (by omega)
  simp only [VV, MM] at *
  omega

def Kwv (B1 B2 C0 e0 cT : ℕ) : ℕ :=
  Kwb B1 B2 C0 e0 + Klb B1 B2 + 2 * Kbk C0 e0 cT + (C0 + 100 * zeta ^ 2 + 16) + 20 * zeta ^ 2 + 3 * (e0 + 2 * b0Of B1 B2) + 1

theorem V_le (r : CellReq B1 B2 cT) (C0 e0 : ℕ) :
    let z := zK (zOf B1 B2 C0 e0) cT r.c.n (natBitLength r.c.n)
    z.W (natBitLength r.c.n) + z.Lk (natBitLength r.c.n) + z.Bk (natBitLength r.c.n) + z.a1 + z.a2 + z.a3 + z.c1 +
      z.c2 + z.c3 + 1 ≤ Kwv B1 B2 C0 e0 cT * 2 ^ (r.c.n - r.p.k) * (r.c.n + 1) ^ (e0 + 2 * b0Of B1 B2 + 6) := by
  intro z
  have hW := W_le r C0 e0
  have hLk := Lk_le r C0 e0
  have hB := Bk_le r C0 e0
  set T := r.c.n + 1 with hT
  set S := 2 ^ (r.c.n - r.p.k) with hS
  have hT1 : 1 ≤ T := by omega
  have hS1 : 1 ≤ S := Nat.one_le_two_pow
  set d := e0 + 2 * b0Of B1 B2 + 6 with hd
  have hz3 : z.a3 ≤ z.Bk (natBitLength r.c.n) := by
    show 2 ^ (r.c.n - kLow cT (natBitLength r.c.n)) * (C0 + 1) ≤
      2 ^ (e0 * natBitLength r.c.n) * (2 ^ (r.c.n - kLow cT (natBitLength r.c.n)) * (C0 + 1))
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have f1 : z.W (natBitLength r.c.n) ≤ Kwb B1 B2 C0 e0 * S * T ^ d := le_ST hW (by omega) hS1 hT1
  have f2 : z.Lk (natBitLength r.c.n) ≤ Klb B1 B2 * S * T ^ d := le_ST hLk (by omega) hS1 hT1
  have f3 : z.Bk (natBitLength r.c.n) ≤ Kbk C0 e0 cT * S * T ^ d := le_ST' (by unfold Kbk; exact hB) (by omega) hT1
  have hU : 1 ≤ S * T ^ d := Nat.mul_le_mul hS1 (Nat.one_le_pow _ _ hT1)
  have c : (C0 + 100 * zeta ^ 2 + 16) + 20 * zeta ^ 2 + 3 * (e0 + 2 * b0Of B1 B2) + 1 ≤
      ((C0 + 100 * zeta ^ 2 + 16) + 20 * zeta ^ 2 + 3 * (e0 + 2 * b0Of B1 B2) + 1) * (S * T ^ d) :=
    Nat.le_mul_of_pos_right _ hU
  have e : Kwv B1 B2 C0 e0 cT * S * T ^ d = Kwb B1 B2 C0 e0 * S * T ^ d + Klb B1 B2 * S * T ^ d +
      2 * (Kbk C0 e0 cT * S * T ^ d) + ((C0 + 100 * zeta ^ 2 + 16) + 20 * zeta ^ 2 + 3 * (e0 + 2 * b0Of B1 B2) + 1) *
        (S * T ^ d) := by unfold Kwv; ring
  have za1 : z.a1 = C0 + 100 * zeta ^ 2 + 16 := rfl
  have za2 : z.a2 = 20 * zeta ^ 2 := rfl
  have zc1 : z.c1 = e0 + 2 * b0Of B1 B2 := rfl
  have zc2 : z.c2 = 2 * b0Of B1 B2 := rfl
  have zc3 : z.c3 = e0 := rfl
  rw [e, za1, za2, zc1, zc2, zc3]
  clear_value z T S d
  omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
