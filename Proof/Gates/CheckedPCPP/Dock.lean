import Proof.Gates.WordPrograms.WMX
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.Dock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

theorem writeTapeBit_len : ∀ (tape : List Bool) (position : ℕ) (value : Bool),
    (writeTapeBit tape position value).length = max tape.length (position + 1)
  | [], 0, _ => rfl
  | [], p + 1, v => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_len [] p v, List.length_nil]; omega
  | _ :: _, 0, _ => by simp [writeTapeBit]
  | _ :: tl, p + 1, v => by
    simp only [writeTapeBit, List.length_cons, writeTapeBit_len tl p v]; omega

theorem step_len {t s : ℕ} (M : Machine t s) (c c' : Configuration t s) (h : step M c = some c') (A : ℕ)
    (hc : ∀ i, (c.tapes i).length ≤ A ∧ c.heads i ≤ A) : ∀ i, (c'.tapes i).length ≤ A + 1 ∧ c'.heads i ≤ A + 1 := by
  intro i
  unfold step at h
  cases hr : M.rule c.control c.scanned with
  | none => rw [hr] at h; simp at h
  | some a =>
    rw [hr] at h
    simp only [Option.map_some] at h
    cases h
    obtain ⟨h1, h2⟩ := hc i
    constructor
    · simp only [applyAction]
      cases hw : a.write i with
      | none => simp only; omega
      | some v => simp only; rw [writeTapeBit_len]; omega
    · simp only [applyAction]
      cases a.move i <;> simp [HeadMove.apply] <;> omega

theorem runFrom_len {t s : ℕ} (M : Machine t s) :
    ∀ (fuel : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s) (A : ℕ), runFrom M fuel c = some r →
      (∀ i, (c.tapes i).length ≤ A ∧ c.heads i ≤ A) → ∀ i, (r.final.tapes i).length ≤ A + r.steps
  | 0, c, r, A, h, hc, i => by
    simp only [runFrom] at h
    split at h
    · cases h; simpa using (hc i).1
    · cases h
  | fuel + 1, c, r, A, h, hc, i => by
    simp only [runFrom] at h
    split at h
    · cases h; simpa using (hc i).1
    · cases hs : step M c with
      | none => rw [hs] at h; cases h
      | some next =>
        rw [hs] at h
        simp only at h
        cases hn : runFrom M fuel next with
        | none => rw [hn] at h; cases h
        | some suffix =>
          rw [hn] at h
          simp only [Option.some.injEq] at h
          subst h
          have := runFrom_len M fuel next suffix (A + 1) hn (step_len M c next hs A hc) i
          simp only
          omega

/-- **Output length.** Every tape of a ready run is at most the longest input tape plus the fuel long. -/
theorem ready_len {t s : ℕ} {M : Machine t s} {fuel : ℕ} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun M fuel input out) (A : ℕ) (hA : ∀ i, (input i).length ≤ A) :
    ∀ i, (out i).length ≤ A + fuel := by
  obtain ⟨r, hr, ht, _, hs⟩ := h
  intro i
  have := runFrom_len M fuel _ r A hr (fun j => ⟨hA j, by simp [initialConfiguration]⟩) i
  rw [ht] at this
  omega

variable {ns nr : ℕ} (cap : ℕ)

theorem ready_mach {t s fuel : ℕ} {M : Machine t s} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun M fuel input out) {tmap : Fin t → Fin (ns + 1)} (hinj : Function.Injective tmap)
    (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0) (hin : ∀ j, σ.st (tmap j) = input j) :
    ∃ τ, WXExec cap (.mach M tmap) σ τ fuel ∧ Docked tmap σ τ (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  have hin' : (fun j => σ.st (tmap j)) = input := funext hin
  obtain ⟨τ, e, hd⟩ := WXExec.mach_run cap hinj σ h0 (r := r) (by rw [hin']; exact hr)
  have hh' : r.final.heads = fun _ => 0 := funext hh
  rw [hh', ht] at hd
  exact ⟨τ, e, hd⟩

end NearCubicGates.Close.CheckedPCPP.Dock
