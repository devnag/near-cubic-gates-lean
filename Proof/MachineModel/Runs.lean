import Proof.MachineModel.Basic
import Proof.Amplification.RecoveryReadyCalls
import Proof.Amplification.RecoveryRowLookupTapes
import Proof.MachineModel.OrdinaryMaskedReset

namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Step {t s : ℕ} (p : Machine t s) (n : ℕ) (hin : Fin t → ℕ) (tin : Fin t → List Bool)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) : Prop :=
  ∃ r : ExecutionReceipt t s, runFrom p n ⟨p.start, hin, tin⟩ = some r ∧
    r.final.heads = hout ∧ r.final.tapes = tout ∧ r.steps ≤ n

theorem Step.of_run {t s : ℕ} {p : Machine t s} {n : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {hout : Fin t → ℕ} {tout : Fin t → List Bool} {r : ExecutionReceipt t s}
    (hr : runFrom p n ⟨p.start, hin, tin⟩ = some r) (hh : r.final.heads = hout)
    (ht : r.final.tapes = tout) : Step p n hin tin hout tout :=
  ⟨r, hr, hh, ht, runFrom_steps_le p n _ r hr⟩

theorem Step.enlarge {t s : ℕ} {p : Machine t s} {n m : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {hout : Fin t → ℕ} {tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (hnm : n ≤ m) :
    Step p m hin tin hout tout := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hmore := runFrom_moreFuel p n (m-n) _ r hr
  rw [Nat.add_sub_of_le hnm] at hmore
  exact ⟨r, hmore, hh, ht, hs.trans hnm⟩

/-- Sequential composition: exactly `Composition.run_join`, one paid bridge step. -/
theorem Step.seq {t sp sq : ℕ} {p : Machine t sp} {q : Machine t sq} {np nq : ℕ}
    {h0 h1 h2 : Fin t → ℕ} {t0 t1 t2 : Fin t → List Bool}
    (hp : Step p np h0 t0 h1 t1) (hq : Step q nq h1 t1 h2 t2) :
    Step (Composition.machine p q) (np+1+nq) h0 t0 h2 t2 := by
  obtain ⟨r1, hr1, hh1, ht1, hs1⟩ := hp
  obtain ⟨r2, hr2, hh2, ht2, hs2⟩ := hq
  have hrestart : Composition.restart r1.final q.start = (⟨q.start, h1, t1⟩ : Configuration t sq) := by
    apply configuration_ext
    · rfl
    · exact hh1
    · exact ht1
  rw [← hrestart] at hr2
  have hjoin := Composition.run_join p q np nq _ r1 r2 hr1 hr2
  refine ⟨Composition.joinedReceipt r1 r2, hjoin, ?_, ?_, by
    change r1.steps + 1 + r2.steps ≤ np + 1 + nq; omega⟩
  · exact hh2
  · exact ht2

/-- Docking a worker into an ambient layout by an injective slot map. -/
noncomputable def dockH {t u : ℕ} (slots : Fin t → Fin u) (ambient : Fin u → ℕ) (local' : Fin t → ℕ) :
    Fin u → ℕ := fun i => match RecoveryFocus.pick slots i with | some j => local' j | none => ambient i

@[simp] theorem dockH_slot {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (ambient : Fin u → ℕ) (local' : Fin t → ℕ) (j : Fin t) : dockH slots ambient local' (slots j) = local' j := by
  simp [dockH, RecoveryFocus.pick_slot slots hi]

theorem dockH_other {t u : ℕ} (slots : Fin t → Fin u) (ambient : Fin u → ℕ) (local' : Fin t → ℕ)
    (i : Fin u) (hn : ∀ j, slots j ≠ i) : dockH slots ambient local' i = ambient i := by
  classical
  have he : ¬∃ j, slots j = i := by rintro ⟨j, hj⟩; exact hn j hj
  simp [dockH, RecoveryFocus.pick, he]

theorem Step.focus {t u s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (ambientH : Fin u → ℕ) (ambientT : Fin u → List Bool) :
    Step (RecoveryFocus.machine slots p) n (dockH slots ambientH hin) (install slots ambientT tin)
      (dockH slots ambientH hout) (install slots ambientT tout) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨result, hres, hfinal, hsteps⟩ :=
    RecoveryFocus.run_config slots hi p ambientH ambientT n ⟨p.start, hin, tin⟩ r hr
  have hentry : RecoveryFocus.config slots ambientH ambientT (⟨p.start, hin, tin⟩ : Configuration t s) =
      (⟨(RecoveryFocus.machine slots p).start, dockH slots ambientH hin, install slots ambientT tin⟩ :
        Configuration u s) := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [hentry] at hres
  refine ⟨result, hres, ?_, ?_, by omega⟩
  · rw [hfinal]
    funext i
    change (match RecoveryFocus.pick slots i with | some j => r.final.heads j | none => ambientH i) = _
    rw [hh]; rfl
  · rw [hfinal]
    funext i
    change (match RecoveryFocus.pick slots i with | some j => r.final.tapes j | none => ambientT i) = _
    rw [ht]; rfl

theorem Step.embed {t e s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (eh : Fin e → ℕ) (et : Fin e → List Bool) :
    Step (TapeEmbedding.machine e p) n (Fin.addCases hin eh) (Fin.addCases tin et)
      (Fin.addCases hout eh) (Fin.addCases tout et) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hrun := TapeEmbedding.run_embed p eh et n _ r hr
  have hentry : TapeEmbedding.config eh et (⟨p.start, hin, tin⟩ : Configuration t s) =
      (⟨(TapeEmbedding.machine e p).start, Fin.addCases hin eh, Fin.addCases tin et⟩ :
        Configuration (t+e) s) := rfl
  rw [hentry] at hrun
  refine ⟨TapeEmbedding.receipt eh et r, hrun, ?_, ?_, hs⟩
  · show Fin.addCases (motive := fun _ => ℕ) r.final.heads eh = _
    rw [hh]
  · show Fin.addCases (motive := fun _ => List Bool) r.final.tapes et = _
    rw [ht]

theorem Step.pad {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (cap : Fin t → ℕ) :
    Step p n hin (fun i => ZeroPadding.pad (cap i) (tin i)) hout
      (fun i => ZeroPadding.pad (cap i) (tout i)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨result, hres, hfinal, hsteps, _⟩ := ZeroPadding.run_config p cap n _ r hr
  have hentry : ZeroPadding.config cap (⟨p.start, hin, tin⟩ : Configuration t s) =
      (⟨p.start, hin, fun i => ZeroPadding.pad (cap i) (tin i)⟩ : Configuration t s) := rfl
  rw [hentry] at hres
  refine ⟨result, hres, ?_, ?_, by omega⟩
  · rw [hfinal]; change r.final.heads = _; exact hh
  · rw [hfinal]; funext i; change ZeroPadding.pad (cap i) (r.final.tapes i) = _; rw [ht]

theorem Step.congr {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hout hout' : Fin t → ℕ}
    {tin tout tout' : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (hh : hout = hout') (ht : tout = tout') : Step p n hin tin hout' tout' := by
  subst hh; subst ht; exact h

theorem Step.congr_in {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hin' hout : Fin t → ℕ}
    {tin tin' tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (hh : hin = hin') (ht : tin = tin') : Step p n hin' tin' hout tout := by
  subst hh; subst ht; exact h

/-- A `ReadyRun` is the all-heads-zero special case. -/
theorem Step.of_ready {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : ReadyRun p n input output) : Step p n (fun _ => 0) input (fun _ => 0) output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, ?_, ht, le_of_eq hs⟩
  · change runFrom p n (initialConfiguration p input) = some r at hr
    exact hr
  · funext i; exact hh i

/-- Masked reset of one composed stage: the selected heads return to zero and
the tapes are unchanged. This is `MaskedReset.workspace_run`, restated. -/
theorem Step.mask {t s : ℕ} {p : Machine t s} {n cap : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (selected : Fin t → Bool)
    (hstart : ∀ i, selected i = true → hin i = 0) (hcap : n ≤ cap) :
    Step (MaskedReset.machine p selected) (2*n+2)
      (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (fun i => if selected i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate cap false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨result, hres, hfinal, hsteps, _⟩ := MaskedReset.workspace_run p selected n cap _ r hr
    (by intro i hi; exact hstart i hi) (by omega)
  have hentry : ZeroPadding.config (Rewind.Workspace.capacities t cap)
      (Rewind.recording (⟨p.start, hin, tin⟩ : Configuration t s) 0) =
      (⟨(MaskedReset.machine p selected).start, Fin.addCases hin (fun _ : Fin 1 => 0),
        Fin.addCases tin (fun _ : Fin 1 => List.replicate cap false)⟩ :
        Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [ZeroPadding.config, Rewind.recording, Rewind.config, Fin.addCases_left,
          Rewind.Workspace.capacities, ZeroPadding.pad_zero]
      · have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp only [ZeroPadding.config, Rewind.recording, Rewind.config, Fin.addCases_right,
          Rewind.Workspace.capacities, List.replicate_zero, ZeroPadding.pad, List.nil_append,
          List.length_nil, Nat.sub_zero]
  rw [hentry] at hres
  have hfuel : 2*r.steps+2 ≤ 2*n+2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p selected) (2*r.steps+2) (2*n+2-(2*r.steps+2)) _ result hres
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨result, hmore, ?_, ?_, by omega⟩
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, hh]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, ht]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]

end NearCubicWires.ExtDecompositionBatch
