import Proof.Gates.CheckedPCPP.WMXSim
import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} {cap : ℕ}

/-- Stream `X` reads like `w`, its head just past `w`. -/
def OutAt (σ : WState ns nr) (X : Fin (ns + 1)) (w : List Bool) : Prop := RdEq (σ.st X) w ∧ σ.sh X = w.length

theorem writeTapeBit_len : ∀ (l : List Bool) (b : Bool), writeTapeBit l l.length b = l ++ [b]
  | [], b => rfl
  | x :: l, b => by simp [writeTapeBit, writeTapeBit_len l b]

theorem rdEq_write_end {l w : List Bool} (h : RdEq l w) (b : Bool) :
    RdEq (writeTapeBit l w.length b) (w ++ [b]) := by
  have := rdEq_write h w.length b
  rwa [writeTapeBit_len] at this

/-- Append one bit at the head. -/
def emitB (X : Fin (ns + 1)) (b : Bool) : WMX ns nr := .seq (WMX.wr X b) (WMX.fwd X)

theorem emitB_runs (X : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (w : List Bool) (h : OutAt σ X w) :
    Runs cap (emitB X b) σ 3 (fun τ => OutAt τ X (w ++ [b]) ∧ SameExcept σ τ [X] []) := by
  refine ⟨_, WXExec.seq (WXExec.wr (cap := cap) X b σ) (WXExec.fwd (cap := cap) X _), ⟨?_, ?_⟩, ?_⟩
  · simp only [WState.seth_st, WState.sets_st, Function.update_self, WState.sets_sh]
    rw [h.2]; exact rdEq_write_end h.1 b
  · simp [h.2]
  · exact (sameExcept_sets σ (by simp) _).trans (sameExcept_seth _ (by simp) _)

/-- Append a fixed list. -/
def emitL (X : Fin (ns + 1)) : List Bool → WMX ns nr
  | [] => WMX.skip
  | b :: u => .seq (emitB X b) (emitL X u)

theorem emitL_runs (X : Fin (ns + 1)) : ∀ (u : List Bool) (σ : WState ns nr) (w : List Bool), OutAt σ X w →
    Runs cap (emitL X u) σ (4 * u.length) (fun τ => OutAt τ X (w ++ u) ∧ SameExcept σ τ [X] [])
  | [], σ, w, h => ⟨σ, WXExec.skip cap σ, by simpa using h, SameExcept.refl _ _ _⟩
  | b :: u, σ, w, h => by
    refine Runs.seq' (emitB_runs X b σ w h) (fun τ hτ => (emitL_runs X u τ (w ++ [b]) hτ.1).post
      (fun ρ hρ => ⟨by simpa using hρ.1, hτ.2.trans hρ.2⟩)) (by simp; omega)

/-- Move the head of `X` left `R` times (`R` kept; `C`, `T` scratch `0`). -/
def rewindBy (X : Fin (ns + 1)) (R C T : Fin nr) : WMX ns nr :=
  .seq (addR R C T) (.whr C (.seq (WMX.dec C) (WMX.bwd X)))

theorem rewindBy_runs (X : Fin (ns + 1)) {R C T : Fin nr} (hRC : R ≠ C) (hRT : R ≠ T) (hCT : C ≠ T)
    (σ : WState ns nr) (hC : σ.val C = 0) (hT : σ.val T = 0) (hR : σ.val R ≤ cap) (hX : σ.sh X ≤ σ.val R) :
    Runs cap (rewindBy X R C T) σ (18 * σ.val R + 3 + 1 + (σ.val R * (1 + 4) + 1))
      (fun τ => τ.sh X = 0 ∧ τ.val C = 0 ∧ τ.st X = σ.st X ∧ SameExcept σ τ [X] [C]) := by
  have h1 := addR_spec cap hRC hRT hCT σ hT (by rw [hC]; omega)
  rw [hC, Nat.zero_add] at h1
  set n := σ.val R with hn
  refine Runs.seqE h1 ?_
  have key := Runs.count (cap := cap) (K := C) (body := WMX.bwd X) 1 n
    (fun k τ => τ.sh X = σ.sh X - k ∧ τ.st X = σ.st X ∧ SameExcept σ τ [X] [C]) hR
    (fun k _ τ hτ _ => ⟨_, WXExec.bwd (cap := cap) X _, ⟨by simp [hτ.1]; omega, by simp [hτ.2.1], by
        refine (hτ.2.2.trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_seth _ (by simp) _) |>.weaken
          (by simp) (by simp)⟩, by simp⟩)
    (σ.setv C n) ⟨by simp, by simp, sameExcept_setv _ (by simp) _⟩ (by simp)
  refine key.post (fun τ hτ => ⟨by rw [hτ.1.1]; omega, hτ.2, hτ.1.2.1, hτ.1.2.2⟩)

end NearCubicGates.Close.CheckedPCPP
