import Proof.Gates.CounterMachine.TabCallSpec
import Proof.Gates.CounterMachine.UnpackNats

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces.Formats

def SelSpec (selP : ∀ {ns nr : ℕ}, Fin (ns + 1) → Fin (ns + 1) → Fin nr → (Fin 4 ↪ Fin nr) → WM ns nr) : Prop :=
  ∀ {ns nr : ℕ} (cap : ℕ) (POUT PFX : Fin (ns + 1)) (I : Fin nr) (U : Fin 4 ↪ Fin nr) (σ : WState ns nr)
    (ws : List (List Bool)) (rest : List Bool) (idx : ℕ),
    POUT ≠ PFX → (∀ j, U j ≠ I) → σ.st POUT = ws.flatMap RepairOrdinary.frame ++ rest → σ.sh POUT = 0 →
    (h : idx < ws.length) → σ.st PFX = [] → σ.sh PFX = 0 → σ.val I = idx → (∀ j, σ.val (U j) = 0) →
    (ws.flatMap RepairOrdinary.frame).length + 10 ≤ cap →
    WExec cap (selP POUT PFX I U) σ ((σ.sets PFX (RepairOrdinary.frame ws[idx])).setv I 0)
      (100 * ((ws.flatMap RepairOrdinary.frame).length + 1))

def tabSize (R : TabReq) : ℕ :=
  R.n + R.G + R.B + R.V + (formulaWord ⟨R.V, R.F⟩).length + R.F.size + R.F.weight + 1

def TabCallSize (B1 B2 cT : ℕ) : Prop :=
  ∃ C e : ℕ, ∀ x : TabCallReq B1 B2 cT, tabSize (tabCallTab x) ≤ C * (x.r.c.n + 1) ^ e

end NearCubicGates.Close.CounterMachine
