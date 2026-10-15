import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

theorem step_sim {t s n : ℕ} {M : Machine t s} {hin : Fin t → ℕ} {tin : Fin t → List Bool} {hout : Fin t → ℕ}
    {tout : Fin t → List Bool} (h : Step M n hin tin hout tout) (tin' : Fin t → List Bool)
    (hr : ∀ j, RdEq (tin j) (tin' j)) : ∃ tout', Step M n hin tin' hout tout' ∧ ∀ j, RdEq (tout j) (tout' j) := by
  obtain ⟨r, hrun, hh, ht, hs⟩ := h
  have hrel : ConfRel (fun _ => False) (⟨M.start, hin, tin⟩ : Configuration t s) ⟨M.start, hin, tin'⟩ :=
    ⟨rfl, rfl, hr, fun _ h => h.elim⟩
  obtain ⟨r', hr', hrel', hst⟩ := runFrom_rel M _ n hrel r hrun
  refine ⟨r'.final.tapes, ⟨r', hr', ?_, rfl, by omega⟩, ?_⟩
  · rw [← hrel'.heads, hh]
  · intro j; rw [← ht]; exact hrel'.read j

variable {ns nr : ℕ}

theorem simW_updS {t' : ℕ} (tmap : Fin t' → Fin (ns + 1)) (hinj : Function.Injective tmap) {σ σ' : WState ns nr}
    (hs : SimW σ σ') (hout : Fin t' → ℕ) {tout tout' : Fin t' → List Bool} (ht : ∀ j, RdEq (tout j) (tout' j)) :
    SimW (updS tmap σ hout tout) (updS tmap σ' hout tout') := by
  classical
  refine ⟨?_, by simp only [updS_val]; exact hs.val, by simp only [updS_cell]; exact hs.cell, ?_⟩
  · funext i
    by_cases h : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := h
      rw [updS_sh_slot tmap σ hout tout hinj, updS_sh_slot tmap σ' hout tout' hinj]
    · have h' : ∀ j, tmap j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [updS_sh_other tmap σ hout tout i h', updS_sh_other tmap σ' hout tout' i h', hs.sh]
  · intro i
    by_cases h : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := h
      rw [updS_st_slot tmap σ hout tout hinj, updS_st_slot tmap σ' hout tout' hinj]
      exact ht j
    · have h' : ∀ j, tmap j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [updS_st_other tmap σ hout tout i h', updS_st_other tmap σ' hout tout' i h']
      exact hs.st i

theorem wxexec_sim {cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    ∀ σ' : WState ns nr, SimW σ σ' → ∃ τ', WXExec cap P σ' τ' n ∧ SimW τ τ' := by
  induction h with
  | wm h =>
    intro σ' hs
    obtain ⟨τ', h', hs'⟩ := wexec_sim h σ' hs
    exact ⟨τ', WXExec.wm h', hs'⟩
  | @mach t s n M tmap σ hout tout hinj hstep =>
    intro σ' hs
    have hstep' : Step M n (fun j => σ'.sh (tmap j)) (fun j => σ.st (tmap j)) hout tout := by
      simpa [hs.sh] using hstep
    obtain ⟨tout', h', ht⟩ := step_sim hstep' (fun j => σ'.st (tmap j)) (fun j => hs.st (tmap j))
    exact ⟨_, WXExec.mach σ' hinj h', simW_updS tmap hinj hs hout ht⟩
  | seq _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih1 σ' hs
    obtain ⟨ρ', h2, hs2⟩ := ih2 τ' hs1
    exact ⟨ρ', WXExec.seq h1 h2, hs2⟩
  | ifrT hv _ ih =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih σ' hs
    exact ⟨τ', WXExec.ifrT (by rw [hs.val]; exact hv) h1, hs1⟩
  | ifrF hv _ ih =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih σ' hs
    exact ⟨τ', WXExec.ifrF (by rw [hs.val]; exact hv) h1, hs1⟩
  | ifsT hv _ ih =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih σ' hs
    exact ⟨τ', WXExec.ifsT (by rw [hs.bit]; exact hv) h1, hs1⟩
  | ifsF hv _ ih =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih σ' hs
    exact ⟨τ', WXExec.ifsF (by rw [hs.bit]; exact hv) h1, hs1⟩
  | whrF hv =>
    intro σ' hs
    exact ⟨σ', WXExec.whrF (by rw [hs.val]; exact hv), hs⟩
  | whrT hv _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih1 σ' hs
    obtain ⟨ρ', h2, hs2⟩ := ih2 τ' hs1
    exact ⟨ρ', WXExec.whrT (by rw [hs.val]; exact hv) h1 h2, hs2⟩
  | whsF hv =>
    intro σ' hs
    exact ⟨σ', WXExec.whsF (by rw [hs.bit]; exact hv), hs⟩
  | whsT hv _ _ ih1 ih2 =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih1 σ' hs
    obtain ⟨ρ', h2, hs2⟩ := ih2 τ' hs1
    exact ⟨ρ', WXExec.whsT (by rw [hs.bit]; exact hv) h1 h2, hs2⟩
  | mono _ hnm ih =>
    intro σ' hs
    obtain ⟨τ', h1, hs1⟩ := ih σ' hs
    exact ⟨τ', WXExec.mono h1 hnm, hs1⟩

theorem SimW.symm {σ σ' : WState ns nr} (h : SimW σ σ') : SimW σ' σ :=
  ⟨h.sh.symm, h.val.symm, h.cell.symm, fun i => (h.st i).symm⟩

theorem SimW.trans {σ σ' σ'' : WState ns nr} (h1 : SimW σ σ') (h2 : SimW σ' σ'') : SimW σ σ'' :=
  ⟨h2.sh.trans h1.sh, h2.val.trans h1.val, h2.cell.trans h1.cell, fun i => (h1.st i).trans (h2.st i)⟩

end NearCubicGates.Close.CheckedPCPP
