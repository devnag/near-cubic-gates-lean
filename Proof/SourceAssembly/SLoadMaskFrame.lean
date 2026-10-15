import Proof.SourceAssembly.SLoadFrames
import Proof.SourceAssembly.SLoadWords

/-! Framing the mask worker's output.

`MaskProducer.correct` promises only the bare `q`-bit word on tape 4 of an
arbitrary compatible final bank; `Request.input` needs it framed. This module
pays for that with the existing raw framer `AppendFrameKernel.machine`, driven
by a retained unary domain word, writing onto a zero-backed scratch slot. No
private tape of the mask worker is read, and the mask slot itself is left
exactly as the callee returned it. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-- A `ClockJoin.ReadyRun` receipt is a `Step` receipt. -/
theorem step_of_clockReady {t s n : Nat} {p : Machine t s} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n input output) :
    Step p n (fun _ => 0) input (fun _ => 0) output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, funext hh, ht, hs⟩
  change runFrom p n (initialConfiguration p input) = some r at hr
  exact hr

theorem quad_injective {u : Nat} (a b c d : Fin u) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → Fin u) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exact absurd hij hab) | (exact absurd hij.symm hab)
      | (exact absurd hij hac) | (exact absurd hij.symm hac)
      | (exact absurd hij had) | (exact absurd hij.symm had)
      | (exact absurd hij hbc) | (exact absurd hij.symm hbc)
      | (exact absurd hij hbd) | (exact absurd hij.symm hbd)
      | (exact absurd hij hcd) | (exact absurd hij.symm hcd)

/-- Bare payload, retained unary driver, framed target, paid rewind log. -/
def entry (capS capD cap capL : Nat) (bits : List Bool) : Fin 4 → List Bool :=
  ![ZeroPadding.pad capS bits, ZeroPadding.pad capD (List.replicate bits.length true),
    List.replicate cap false, List.replicate capL false]

def exit (capS capD cap capL : Nat) (bits : List Bool) : Fin 4 → List Bool :=
  ![ZeroPadding.pad capS bits, ZeroPadding.pad capD (List.replicate bits.length true),
    ZeroPadding.pad cap (frame bits), List.replicate capL false]

theorem local_step (capS capD cap capL : Nat) (bits : List Bool)
    (hlog : 2 * bits.length + 1 ≤ capL) :
    Step AppendFrameKernel.machine (4 * bits.length + 4) (fun _ => 0)
      (entry capS capD cap capL bits) (fun _ => 0) (exit capS capD cap capL bits) := by
  have base := (step_of_clockReady (AppendFrameKernel.ready bits)).pad ![capS, capD, cap, capL]
  refine base.congr_in rfl ?_ |>.congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change ZeroPadding.pad cap ([] : List Bool) = _
      rw [Words.pad_nil]
      rfl
    · change ZeroPadding.pad capL ([] : List Bool) = _
      rw [Words.pad_nil]
      rfl
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change ZeroPadding.pad capL (List.replicate (2 * bits.length + 1) false) = _
      rw [Words.pad_false capL (2 * bits.length + 1) hlog]
      rfl

/-- The docked mask framer. -/
noncomputable def machine {U : Nat} (src drv dst log : Fin U) : Machine U 5 :=
  RecoveryFocus.machine (![src, drv, dst, log] : Fin 4 → Fin U) AppendFrameKernel.machine

/-- One paid framing of the mask worker's returned bitmap onto a zero-backed
scratch slot. The mask slot and the retained unary driver are unchanged and
no head moves. -/
theorem mask_frame_step {U : Nat} (src drv dst log : Fin U)
    (h1 : src ≠ drv) (h2 : src ≠ dst) (h3 : src ≠ log)
    (h4 : drv ≠ dst) (h5 : drv ≠ log) (h6 : dst ≠ log)
    (capS capD cap capL : Nat) (bits : List Bool) (hlog : 2 * bits.length + 1 ≤ capL)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHs : H src = 0) (hHd : H drv = 0) (hHt : H dst = 0) (hHl : H log = 0)
    (hAs : A src = ZeroPadding.pad capS bits)
    (hAd : A drv = ZeroPadding.pad capD (List.replicate bits.length true))
    (hAt : A dst = List.replicate cap false) (hAl : A log = List.replicate capL false) :
    Step (machine src drv dst log) (4 * bits.length + 4) H A H
      (Function.update A dst (ZeroPadding.pad cap (frame bits))) := by
  have hinj := quad_injective src drv dst log h1 h2 h3 h4 h5 h6
  exact SLoad.step_update (local_step capS capD cap capL bits hlog) 2
    (by
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd rfl hi
      · rfl)
    _ hinj H A
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i
      fin_cases i
      · exact hAs
      · exact hAd
      · exact hAt
      · exact hAl)

end
end SLoad.MaskFrame
