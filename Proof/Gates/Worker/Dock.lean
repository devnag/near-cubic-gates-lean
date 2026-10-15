import Proof.Gates.CheckedPCPP.Clear
import Proof.Gates.Codec.Unframe
import Proof.Gates.CheckedPCPP.WMXSim

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.WireExponent3_5
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm.DockW

variable {ns nr : ℕ}

theorem readyRun_machZ {t s : ℕ} (M : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool)
    (h : ClockJoin.ReadyRun M n tin tout) {cap : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (L : Fin (ns + 1)) (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (tin j)) (lcap : ℕ) (hLst : σ.st L = List.replicate lcap false)
    (hLsh : σ.sh L = 0) (hn : n ≤ lcap) :
    ∃ τ tout', WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ Docked tmap σ τ (fun _ => 0) tout' ∧
      ∀ j, RdEq (τ.st (tmap j)) (tout j) := by
  obtain ⟨receipt, hrun, htapes, _, _⟩ := h
  have hrel : ConfRel (fun _ => False) (initialConfiguration M tin)
      ⟨M.start, fun _ => 0, fun j => σ.st (tmap j)⟩ :=
    ⟨rfl, rfl, fun j => (hin j).symm, fun _ h => h.elim⟩
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel M _ n hrel receipt hrun
  obtain ⟨τ, hτ, hd⟩ := WXExec.machZ_ex cap hinj hL σ (Step.of_run (r := r') hr' rfl rfl) h0 hLst hLsh hn
  refine ⟨τ, r'.final.tapes, hτ, hd, fun j => ?_⟩
  rw [hd.st]
  exact (hrel'.read j).symm.trans (by rw [htapes]; exact RdEq.refl _)

theorem frameDonor_run {t s : ℕ} (M : Machine t s) (n : ℕ) (a : Fin t) (x : List Bool) (tout : Fin t → List Bool)
    (h : ClockJoin.ReadyRun M n (fun j => if j = a then RepairOrdinary.frame x else []) tout) {cap : ℕ}
    (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (X L : Fin (ns + 1)) (hXm : ∀ j, tmap j ≠ X)
    (hL : ∀ j, tmap j ≠ L) (OP T D : Fin nr) (hOT : OP ≠ T) (hOD : OP ≠ D) (hTD : T ≠ D)
    (rest : List Bool) (σ : WState ns nr) (hX : σ.st X = RepairOrdinary.frame x ++ rest) (hXh : σ.sh X = 0)
    (hb : ∀ j, σ.st (tmap j) = []) (h0 : ∀ j, σ.sh (tmap j) = 0) (hO : σ.val OP = 0) (hT : σ.val T = 0)
    (hD : σ.val D = 0) (hc : 4 * x.length + 4 ≤ cap) (lcap : ℕ) (hLst : σ.st L = List.replicate lcap false)
    (hLsh : σ.sh L = 0) (hn : n ≤ lcap) :
    ∃ τ, WXExec cap (.seq (.wm (Codec.copyRW X (tmap a) OP T D)) (WMX.machZ M tmap L)) σ τ
        (22 * x.length + 1 + 1 + 7 + 1 + (18 * (2 * x.length + 1) + 3 + 1 + (5 * (2 * x.length + 1) + 1 + 1 +
          (5 * (2 * x.length + 1) + 1))) + 1 + (2 * n + 2)) ∧
      (∀ j, RdEq (τ.st (tmap j)) (tout j)) ∧ (∀ j, τ.sh (tmap j) = 0) ∧
      (∀ i, (∀ j, tmap j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have e1 := Codec.copyRW_spec cap X (tmap a) (fun h => hXm a h.symm) OP T D hOT hOD hTD x rest σ hX hXh (hb a) (h0 a)
    hO hT hD hc
  set σ1 := σ.sets (tmap a) (RepairOrdinary.frame x) with hσ1
  obtain ⟨τ, tout', e2, hd, hrd⟩ := readyRun_machZ M n _ tout h tmap hinj L hL σ1
    (fun j => by simp [hσ1, h0 j])
    (fun j => by
      by_cases hj : j = a
      · subst hj; simp [hσ1]; exact RdEq.refl _
      · simp [hσ1, Function.update_of_ne (hinj.ne hj), hb j, hj]; exact RdEq.refl _)
    lcap (by simp [hσ1, Function.update_of_ne (hL a).symm, hLst]) (by simp [hσ1, hLsh]) hn
  refine ⟨τ, WXExec.seq (WXExec.wm e1) e2, hrd, fun j => hd.sh j, fun i hi => ?_, ?_, ?_⟩
  · have := hd.other i hi
    rw [this.1, this.2]
    simp [hσ1, Function.update_of_ne (hi a).symm]
  · rw [hd.val]; rfl
  · rw [hd.cell]; rfl

theorem simW_sets (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) (h : RdEq (σ.st i) l) :
    SimW σ (σ.sets i l) := by
  refine ⟨rfl, rfl, rfl, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simpa using h
  · simp [Function.update_of_ne hj]; exact RdEq.refl _

/-- A run from an exact state transfers to every state reading like it. -/
theorem run_of_simW {cap : ℕ} {P : WMX ns nr} {σ σ' τ' : WState ns nr} {n : ℕ} (hs : SimW σ' σ)
    (h : WXExec cap P σ' τ' n) : ∃ τ, WXExec cap P σ τ n ∧ SimW τ' τ :=
  wxexec_sim h σ hs

/-- A stream reads blank everywhere. -/
def Blank (l : List Bool) : Prop := ∀ p, readTapeBit l p = false

theorem blank_rdEq (l : List Bool) (h : Blank l) (m : ℕ) : RdEq l (List.replicate m false) := by
  intro p; rw [h p]; unfold readTapeBit; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

/-- **`readyRun_machZ` with a log that only reads blank** (an empty stream will do): the run is proved on the state
whose log holds exactly `n` blanks and transferred by `wxexec_sim`. -/
theorem readyRun_machZ_blank {t s : ℕ} (M : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool)
    (h : ClockJoin.ReadyRun M n tin tout) {cap : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (L : Fin (ns + 1)) (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (tin j)) (hLb : Blank (σ.st L)) (hLsh : σ.sh L = 0) :
    ∃ τ, WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ (∀ j, RdEq (τ.st (tmap j)) (tout j)) ∧
      (∀ j, τ.sh (tmap j) = 0) ∧ (∀ i, (∀ j, tmap j ≠ i) → RdEq (τ.st i) (σ.st i) ∧ τ.sh i = σ.sh i) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell := by
  set σ' := σ.sets L (List.replicate n false) with hσ'
  have hs : SimW σ σ' := simW_sets σ L _ (blank_rdEq _ hLb n)
  obtain ⟨τ', tout', e, hd, hrd⟩ := readyRun_machZ M n tin tout h tmap hinj L hL σ'
    (fun j => by simp [hσ', h0 j]) (fun j => by simp [hσ', Function.update_of_ne (hL j)]; exact hin j)
    n (by simp [hσ']) (by simp [hσ', hLsh]) le_rfl
  obtain ⟨τ, e', hs'⟩ := run_of_simW (CheckedPCPP.SimW.symm hs) e
  refine ⟨τ, e', fun j => (hs'.st (tmap j)).symm.trans (hrd j), fun j => by rw [hs'.sh]; exact hd.sh j,
    fun i hi => ⟨?_, ?_⟩, by rw [hs'.val, hd.val]; rfl, by rw [hs'.cell, hd.cell]; rfl⟩
  · have h1 := (hd.other i hi).1
    refine (hs'.st i).symm.trans ?_
    rw [h1]
    by_cases hiL : i = L
    · subst hiL; simp [hσ']; exact (blank_rdEq _ hLb n).symm
    · simp [hσ', Function.update_of_ne hiL]; exact RdEq.refl _
  · rw [hs'.sh, (hd.other i hi).2]; simp [hσ']

theorem donor_ideal {t s : ℕ} (M : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool)
    (h : ClockJoin.ReadyRun M n tin tout) {cap : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (L : Fin (ns + 1)) (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (tin j)) (hLb : Blank (σ.st L)) (hLsh : σ.sh L = 0) :
    ∃ τ, WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ SimW (updS tmap σ (fun _ => 0) tout) τ := by
  obtain ⟨τ, e, hrd, hsh, hoth, hval, hcell⟩ := readyRun_machZ_blank M n tin tout h tmap hinj L hL σ h0 hin hLb hLsh
  refine ⟨τ, e, ⟨?_, by rw [hval]; rfl, by rw [hcell]; rfl, fun i => ?_⟩⟩
  · funext i
    by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hsh j, updS_sh_slot tmap σ (fun _ => 0) tout hinj]
    · have hi' : ∀ j, tmap j ≠ i := fun j hj => hi ⟨j, hj⟩
      rw [(hoth i hi').2, updS_sh_other tmap σ (fun _ => 0) tout i hi']
  · by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [updS_st_slot tmap σ (fun _ => 0) tout hinj]; exact (hrd j).symm
    · have hi' : ∀ j, tmap j ≠ i := fun j hj => hi ⟨j, hj⟩
      rw [updS_st_other tmap σ (fun _ => 0) tout i hi']; exact (hoth i hi').1.symm

/-- **Sequencing in ideal form.** -/
theorem seq_sim {cap : ℕ} {P Q : WMX ns nr} {σ τ1 ι1 ι2 : WState ns nr} {n m : ℕ} (h1 : WXExec cap P σ τ1 n)
    (s1 : SimW ι1 τ1) (h2 : ∃ τ2, WXExec cap Q ι1 τ2 m ∧ SimW ι2 τ2) :
    ∃ τ, WXExec cap (.seq P Q) σ τ (n + 1 + m) ∧ SimW ι2 τ := by
  obtain ⟨τ2, e2, s2⟩ := h2
  obtain ⟨τ, e, s⟩ := wxexec_sim e2 τ1 s1
  exact ⟨τ, WXExec.seq h1 e, CheckedPCPP.SimW.trans s2 s⟩

theorem updS_sets {t : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr) (a : Fin t)
    (l : List Bool) (hout : Fin t → ℕ) (tout : Fin t → List Bool) :
    updS tmap (σ.sets (tmap a) l) hout tout = updS tmap σ hout tout := by
  apply updS_eq tmap (σ.sets (tmap a) l) hout tout hinj (updS tmap σ hout tout)
  · intro j; exact updS_st_slot tmap _ hout tout hinj j
  · intro j; exact updS_sh_slot tmap _ hout tout hinj j
  · intro i hi
    rw [updS_st_other tmap _ hout tout i hi, updS_sh_other tmap _ hout tout i hi]
    simp [Function.update_of_ne (hi a).symm]
  · rfl
  · rfl

/-- **Ideal form of `frameDonor_run`.** -/
theorem frameDonor_ideal {t s : ℕ} (M : Machine t s) (n : ℕ) (a : Fin t) (x : List Bool) (tout : Fin t → List Bool)
    (h : ClockJoin.ReadyRun M n (fun j => if j = a then RepairOrdinary.frame x else []) tout) {cap : ℕ}
    (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (X L : Fin (ns + 1)) (hXm : ∀ j, tmap j ≠ X)
    (hL : ∀ j, tmap j ≠ L) (OP T D : Fin nr) (hOT : OP ≠ T) (hOD : OP ≠ D) (hTD : T ≠ D)
    (rest : List Bool) (σ : WState ns nr) (hX : σ.st X = RepairOrdinary.frame x ++ rest) (hXh : σ.sh X = 0)
    (hb : ∀ j, σ.st (tmap j) = []) (h0 : ∀ j, σ.sh (tmap j) = 0) (hO : σ.val OP = 0) (hT : σ.val T = 0)
    (hD : σ.val D = 0) (hc : 4 * x.length + 4 ≤ cap) (hLb : Blank (σ.st L)) (hLsh : σ.sh L = 0) :
    ∃ τ, WXExec cap (.seq (.wm (Codec.copyRW X (tmap a) OP T D)) (WMX.machZ M tmap L)) σ τ
        (22 * x.length + 1 + 1 + 7 + 1 + (18 * (2 * x.length + 1) + 3 + 1 + (5 * (2 * x.length + 1) + 1 + 1 +
          (5 * (2 * x.length + 1) + 1))) + 1 + (2 * n + 2)) ∧
      SimW (updS tmap σ (fun _ => 0) tout) τ := by
  have e1 := Codec.copyRW_spec cap X (tmap a) (fun h => hXm a h.symm) OP T D hOT hOD hTD x rest σ hX hXh (hb a) (h0 a)
    hO hT hD hc
  set σ1 := σ.sets (tmap a) (RepairOrdinary.frame x) with hσ1
  obtain ⟨τ, e2, hs⟩ := donor_ideal M n _ tout h tmap hinj L hL σ1
    (fun j => by simp [hσ1, h0 j])
    (fun j => by
      by_cases hj : j = a
      · subst hj; simp [hσ1]; exact RdEq.refl _
      · simp [hσ1, Function.update_of_ne (hinj.ne hj), hb j, hj]; exact RdEq.refl _)
    (by simp [hσ1, Function.update_of_ne (hL a).symm]; exact hLb) (by simp [hσ1, hLsh])
  refine ⟨τ, WXExec.seq (WXExec.wm e1) e2, ?_⟩
  rw [hσ1, updS_sets tmap hinj σ a] at hs
  exact hs

end NearCubicGates.Close.Worker
