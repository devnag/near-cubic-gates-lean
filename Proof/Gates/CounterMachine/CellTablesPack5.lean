import Proof.Gates.CounterMachine.CellTablesPack4
import Proof.Gates.CounterMachine.CellTablesPackSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

variable {V M : ℕ} (K : Callee)

/-- The set-up of the CellTables program. -/
def setupK (hM : 5 ≤ M) (z : Sz) (cT : ℕ) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (.seq (setupA1 K z) (.seq (bkBlk (blockRegs hM) sIN rG rC1 cT) (setupA3 K))) (.seq (setupB K) (setupC K))

/-- The CellTables program. -/
noncomputable def progK (hM : 5 ≤ M) (z : Sz) (cT : ℕ) (main : St V M) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (setupK K hM z cT) (.seq (comp K main) tearP)

theorem zK_W (z : Sz) (cT n0 L : ℕ) : (zK z cT n0 L).W L = z.W L := rfl
theorem zK_Lk (z : Sz) (cT n0 L : ℕ) : (zK z cT n0 L).Lk L = z.Lk L := rfl
theorem zK_Bk (z : Sz) (cT n0 L : ℕ) : (zK z cT n0 L).Bk L = 2 ^ (n0 - kLow cT L) * z.Bk L := by
  unfold zK Sz.Bk; ring

/-- The set-up cost. -/
def setupKCost (V M : ℕ) (z : Sz) (cT n0 L : ℕ) : ℕ :=
  (costA1 z L + 1 + (bkBlkCost L cT n0 (z.Bk L) + 1 + costA3 (z.Lk L) ((zK z cT n0 L).Bk L))) + 1 +
    (costB V M (z.W L) (z.Lk L) ((zK z cT n0 L).Bk L) + 1 + costC L (z.W L) (z.Lk L) ((zK z cT n0 L).Bk L))

theorem setupK_spec (hM : 5 ≤ M) (z : Sz) (cT n0 : ℕ) (rest inp : List Bool) (hinp : inp = natWord n0 ++ rest)
    (cap : ℕ) (hcap : 2 * inp.length + 8 * (z.W (leadOnes inp) + z.Lk (leadOnes inp) + (zK z cT n0 (leadOnes inp)).Bk
      (leadOnes inp)) + 4 * z.a1 + 4 * z.a2 + 4 * z.a3 + 20 ≤ cap)
    (hcap1 : 2 ^ (leadOnes inp + 2) + 8 * leadOnes inp + 10 ≤ cap)
    (hcap2 : (leadOnes inp + 1) * (2 + cT + 3 * leadOnes inp) + 4 * leadOnes inp + cT + 2 * n0 + 30 ≤ cap) :
    WXExec cap (setupK (V := V) K hM z cT) (Interfaces.startState (NS M (TSK K) V) (NR M) inp)
      (initSt (t := TSK K) (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) ((zK z cT n0 (leadOnes inp)).Bk (leadOnes inp))
        inp) (setupKCost V M z cT n0 (leadOnes inp)) := by
  have hLn : leadOnes inp = natBitLength n0 := by rw [hinp]; exact leadOnes_natWord n0 rest
  have hBk := zK_Bk z cT n0 (leadOnes inp)
  have hBa : z.a3 ≤ z.Bk (leadOnes inp) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hBB : z.Bk (leadOnes inp) ≤ (zK z cT n0 (leadOnes inp)).Bk (leadOnes inp) := by
    rw [hBk]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have a1 := setupA1_spec (V := V) (M := M) K z inp cap (by omega)
  have a2 := blk_spec (V := V) K hM cT n0 rest inp hinp (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp))
    (z.Bk (leadOnes inp)) cap hLn hcap1 hcap2 (by rw [← hBk]; omega)
  rw [← hBk] at a2
  have a3 := setupA3_spec (V := V) (M := M) K (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp))
    ((zK z cT n0 (leadOnes inp)).Bk (leadOnes inp)) inp cap (by omega)
  have b := setupB_spec (V := V) (M := M) K (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp))
    ((zK z cT n0 (leadOnes inp)).Bk (leadOnes inp)) inp cap (by omega)
  have c := setupC_spec (V := V) (M := M) K (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp))
    ((zK z cT n0 (leadOnes inp)).Bk (leadOnes inp)) inp cap (by have := leadOnes_le inp; omega)
  exact WXExec.seq (WXExec.seq a1 (WXExec.seq a2 a3)) (WXExec.seq b c)

end NearCubicGates.Close.CounterMachine.CellTablesProg
