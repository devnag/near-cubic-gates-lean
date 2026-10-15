import Proof.Gates.CheckedPCPP.Dock
import Proof.Gates.CheckedPCPP.WMXSim

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.Dock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicWires.ExtDecompositionBatch

variable {ns nr : ℕ} (cap : ℕ)

theorem ready_mach_rd {t s fuel : ℕ} {M : Machine t s} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun M fuel input out) {tmap : Fin t → Fin (ns + 1)} (hinj : Function.Injective tmap)
    (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0) (hin : ∀ j, RdEq (σ.st (tmap j)) (input j)) :
    ∃ τ tout, WXExec cap (.mach M tmap) σ τ fuel ∧ Docked tmap σ τ (fun _ => 0) tout ∧ ∀ j, RdEq (tout j) (out j) := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  have hs : Step M fuel (fun _ => 0) input (fun _ => 0) out := Step.of_run hr (funext hh) ht
  obtain ⟨tout, hs', hrd⟩ := CheckedPCPP.step_sim hs (fun j => σ.st (tmap j)) (fun j => (hin j).symm)
  have e : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext h0
  have hs'' : Step M fuel (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j)) (fun _ => 0) tout := by
    rw [e]; exact hs'
  obtain ⟨τ, hx, hd⟩ := WXExec.mach_ex cap hinj σ hs''
  exact ⟨τ, tout, hx, hd, fun j => (hrd j).symm⟩

end NearCubicGates.Close.CheckedPCPP.Dock
