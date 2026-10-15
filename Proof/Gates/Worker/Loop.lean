import Proof.Gates.Worker.Dock

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.WireExponent3_5

variable {ns nr : ℕ}

/-- The counted WMX loop: while `C ≠ 0`, decrement `C` and run `body`. -/
def repLoopX (C : Fin nr) (body : WMX ns nr) : WMX ns nr := .whr C (.seq (.wm (.dec C)) body)

theorem simW_setv {σ σ' : WState ns nr} (hs : SimW σ σ') (r : Fin nr) (v : ℕ) : SimW (σ.setv r v) (σ'.setv r v) :=
  ⟨by simp [hs.sh], by simp [hs.val], by simp [hs.cell], fun i => by simpa using hs.st i⟩

/-- **`m` passes along ideal states `g 0, …, g m`, on read-alike states.** -/
theorem repLoopX_sim {cap : ℕ} (C : Fin nr) (body : WMX ns nr) (m c : ℕ) (g : ℕ → WState ns nr)
    (hC : ∀ i ≤ m, (g i).val C = m - i) (hcap : m ≤ cap)
    (hbody : ∀ i < m, ∃ τ, WXExec cap body ((g i).setv C (m - i - 1)) τ c ∧ SimW (g (i + 1)) τ) :
    ∀ σ, SimW (g 0) σ → ∃ τ, WXExec cap (repLoopX C body) σ τ (m * (c + 4) + 1) ∧ SimW (g m) τ := by
  suffices h : ∀ k, k ≤ m → ∀ σ, SimW (g (m - k)) σ →
      ∃ τ, WXExec cap (repLoopX C body) σ τ (k * (c + 4) + 1) ∧ SimW (g m) τ by
    intro σ hs
    exact h m le_rfl σ (by simpa using hs)
  intro k
  induction k with
  | zero =>
    intro _ σ hs
    have h0 : σ.val C = 0 := by rw [hs.val, Nat.sub_zero, hC m le_rfl]; simp
    refine ⟨σ, ?_, by simpa using hs⟩
    simpa [repLoopX] using (WXExec.whrF (cap := cap) (P := .seq (.wm (.dec C)) body) (σ := σ) h0)
  | succ k ih =>
    intro hk σ hs
    have hi : m - (k + 1) < m := by omega
    have hval : σ.val C = m - (m - (k + 1)) := by rw [hs.val]; exact hC _ (by omega)
    have e1 := WExec.dec (cap := cap) C σ (by rw [hval]; omega)
    obtain ⟨τ0, eb, sb⟩ := hbody (m - (k + 1)) hi
    have hss : SimW ((g (m - (k + 1))).setv C (m - (m - (k + 1)) - 1)) (σ.setv C (σ.val C - 1)) := by
      rw [hval]; exact simW_setv hs C _
    obtain ⟨τ1, eb', sb'⟩ := wxexec_sim eb _ hss
    have hidx : m - (k + 1) + 1 = m - k := by omega
    rw [hidx] at sb
    obtain ⟨τ, e3, s3⟩ := ih (by omega) τ1 (CheckedPCPP.SimW.trans sb sb')
    refine ⟨τ, WXExec.mono (WXExec.whrT (by rw [hval]; omega) (WXExec.seq (WXExec.wm e1) eb') e3) ?_, s3⟩
    ring_nf
    omega

end NearCubicGates.Close.Worker
