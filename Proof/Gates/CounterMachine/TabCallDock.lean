import Proof.Gates.WordPrograms.WMX
import Proof.Gates.CheckedPCPP.Harness
import Proof.Gates.CounterMachine.TabCallSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The input tape (index `0`) of a program. -/
def tape0 (p : Program) : Fin p.tapeCount := ⟨0, by have := p.twoTapes; omega⟩

theorem wfDock_exact {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ)
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (hin : σ.st (tmap (tape0 f.program)) = RepairOrdinary.frame (input req))
    (hblank : ∀ j, j ≠ tape0 f.program → σ.st (tmap j) = []) (h0 : ∀ j, σ.sh (tmap j) = 0) (lcap : ℕ)
    (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : budget req ≤ lcap) :
    ∃ τ, WXExec cap (WMX.machZ f.program.machine tmap L) σ τ (2 * budget req + 2) ∧
      τ.st (tmap f.program.outputTape) = output req ∧ (∀ j, τ.sh (tmap j) = 0) ∧
      (∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  have htapes : (fun j => σ.st (tmap j)) = f.program.inputTapes (input req) := by
    funext j
    rw [CheckedPCPP.program_inputTapes]
    by_cases hj : j.val = 0
    · have : j = tape0 f.program := Fin.ext hj
      subst this; rw [hin]; rfl
    · rw [if_neg hj, hblank j (fun h => hj (by rw [h]; rfl))]
  rw [← htapes] at hrun
  obtain ⟨τ, e, hd⟩ := WXExec.machZ_run cap hinj hL σ hrun h0 hLst hLsh hn
  exact ⟨τ, e, by rw [hd.st, hout], fun j => hd.sh j, hd.other, hd.val⟩

end NearCubicGates.Close.CounterMachine
