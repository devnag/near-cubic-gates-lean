import Proof.Gates.CellsPack.Mach
import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter

/-- The constant part of the budget bound. -/
def Gof (K : Callee) (z : Sz) (L : ℕ) : ℕ :=
  z.W L + z.Lk L + z.Bk L + L + z.a1 + z.a2 + z.a3 + z.c1 + z.c2 + z.c3 + TSK K + 1

theorem lang_le2 (K : Callee) (z : Sz) (inp : List Bool) (N : ℕ) :
    langBudget K z VV MM inp N ≤ 10 ^ 6 * ((N + 1) * Gof K z (leadOnes inp) ^ 2) + 10 * inp.length := by
  simp only [langBudget, costA, costB, costC, Gof, VV, MM]
  generalize z.W (leadOnes inp) = W
  generalize z.Lk (leadOnes inp) = Lk
  generalize z.Bk (leadOnes inp) = Bk
  generalize leadOnes inp = L
  generalize inp.length = I
  generalize TSK K = T
  generalize z.a1 = a1
  generalize z.a2 = a2
  generalize z.a3 = a3
  generalize z.c1 = c1
  generalize z.c2 = c2
  generalize z.c3 = c3
  set G := W + Lk + Bk + L + a1 + a2 + a3 + c1 + c2 + c3 + T + 1 with hG
  have hS1 : 1 ≤ (N + 1) * G ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have base : ∀ x, x ≤ G → x ≤ (N + 1) * G ^ 2 := by
    intro x hx
    calc x ≤ G ^ 2 := hx.trans (Nat.le_self_pow (by omega) _)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have prod : ∀ x y, x ≤ G → y ≤ G → x * y ≤ (N + 1) * G ^ 2 := by
    intro x y hx hy
    calc x * y ≤ G ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hx hy
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have nprod : ∀ x, x ≤ G → N * x ≤ (N + 1) * G ^ 2 := by
    intro x hx
    exact Nat.mul_le_mul (by omega) (hx.trans (Nat.le_self_pow (by omega) _))
  have nW2 : N * (W + 1) ^ 2 ≤ (N + 1) * G ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  have f1 := base L (by omega)
  have f2 := base W (by omega)
  have f3 := base Lk (by omega)
  have f4 := base Bk (by omega)
  have f5 := base (a1 + a2 + a3 + c1 + c2 + c3) (by omega)
  have f6 := prod L W (by omega) (by omega)
  have f7 := prod L c1 (by omega) (by omega)
  have f8 := prod L Lk (by omega) (by omega)
  have f9 := prod L c2 (by omega) (by omega)
  have f10 := prod L Bk (by omega) (by omega)
  have f11 := prod L c3 (by omega) (by omega)
  have f12 := nprod W (by omega)
  have f13 := nprod T (by omega)
  have f14 := nprod 1 (by omega)
  generalize (N + 1) * G ^ 2 = Sx at *
  nlinarith

theorem leadOnes_pkIn {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : leadOnes (pkIn r) = natBitLength r.c.n := by
  unfold pkIn cellInput callWord; simp only [List.append_assoc]; exact CounterMachine.PrefixProg.leadOnes_natWord _ _

end NearCubicGates.Close.CellsPack
