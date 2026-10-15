import Proof.Gates.Expand.Setup2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def GLr : Fin NR := GR 5

def flagS (A Z : Fin 53) : WMX NS NR :=
  .seq (BinW.lt (NB Z) (NB A) F0 R0) (.ifr F0 (.seq (WMX.dec F0) (WMX.inc GLr)) WMX.skip)

def toReg (A Z E : Fin 53) (T : Fin NR) : WMX NS NR :=
  .seq (flagS A Z) (.whr GLr (.seq (WMX.dec GLr) (.seq (BinW.sub (NB A) (NB E) F0 R0) (.seq (WMX.inc T) (flagS A Z)))))

def flagCost (Wb : ℕ) : ℕ := (41 * Wb + 3) + 1 + ((1 + 1 + 3) + 1)

def toRegCost (Wb a : ℕ) : ℕ :=
  flagCost Wb + 1 + (a * ((1 + 1 + ((41 * Wb + 9) + 1 + (3 + 1 + flagCost Wb))) + 2) + 1)

def TS (T : Fin NR) (σ τ : WState NS NR) (g t : ℕ) : Prop :=
  τ.val F0 = 0 ∧ τ.val R0 = 0 ∧ τ.val GLr = g ∧ τ.val T = t ∧ ∀ q, q ≠ GLr → q ≠ T → q ≠ F0 → τ.val q = σ.val q

theorem flagS_spec (cap Wb : ℕ) (A Z : Fin 53) (hAZ : Z ≠ A) (T : Fin NR) (hT1 : T ≠ GLr) (hT2 : T ≠ F0)
    (σ τ : WState NS NR) (w : Fin 53 → ℕ) (hw : MV NB Wb w τ) (hz : w Z = 0) (ha : w A < 2 ^ Wb) (t : ℕ)
    (hs : TS T σ τ 0 t) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (flagS A Z) τ (flagCost Wb) (fun ρ => MV NB Wb w ρ ∧ TS T σ ρ (decide (0 < w A)).toNat t ∧
      ∀ x, ρ.st x = τ.st x ∧ ρ.sh x = τ.sh x) := by
  obtain ⟨h0, h1, hg, ht, ho⟩ := hs
  have hFR : F0 ≠ R0 := grN (by decide)
  have gF : GLr ≠ F0 := grN (by decide)
  have gR : GLr ≠ R0 := grN (by decide)
  refine Runs.seq (mLt cap Wb Z A hAZ hFR hw h0 h1 (by rw [hz]; exact Nat.two_pow_pos Wb) ha (by omega))
    (fun τ1 ⟨m1, v1, f1⟩ => ?_)
  rw [hz] at v1
  refine Runs.ifr (c := 1 + 1 + 3) (fun hT => ?_) (fun hF => ?_)
  · have hp : 0 < w A := by by_contra hc; exact hT (by rw [v1, decide_eq_false hc]; rfl)
    rw [decide_eq_true hp] at v1 ⊢
    have e := WXExec.seq (WXExec.dec cap F0 τ1 (by rw [v1]; simp; omega))
      (WXExec.inc cap GLr _ (by simp [Function.update_of_ne gF, f1.val (show GLr ∉ [F0] by simp [gF]), hg]; omega))
    refine Runs.of e ⟨m1.frame' ((sameExcept_setv (S := []) (Rg := [F0, GLr]) _ (by simp) _).trans
      (sameExcept_setv _ (by simp) _)) (by simp), ⟨?_, ?_, ?_, ?_, ?_⟩, fun x => by simp [f1.st (by simp : x ∉ []),
        f1.sh (by simp : x ∉ [])]⟩
    · simp [Function.update_of_ne gF.symm, v1]
    · simp [Function.update_of_ne gR.symm, Function.update_of_ne hFR.symm, f1.val (show R0 ∉ [F0] by simp [hFR.symm]), h1]
    · simp [Function.update_of_ne gF, f1.val (show GLr ∉ [F0] by simp [gF]), hg]
    · simp [Function.update_of_ne hT1, Function.update_of_ne hT2, f1.val (show T ∉ [F0] by simp [hT2]), ht]
    · intro q q1 q2 q3
      simp [Function.update_of_ne q1, Function.update_of_ne q3, f1.val (show q ∉ [F0] by simp [q3]), ho q q1 q2 q3]
  · have hp : ¬ 0 < w A := by intro hc; rw [v1, decide_eq_true hc] at hF; exact absurd hF (by decide)
    rw [decide_eq_false hp]
    refine (Runs.of (WXExec.skip cap τ1) ⟨m1, ⟨by rw [v1, decide_eq_false hp]; rfl, ?_, ?_, ?_, ?_⟩,
      fun x => ⟨f1.st (by simp), f1.sh (by simp)⟩⟩).cost (by omega)
    · rw [f1.val (by simp [hFR.symm])]; exact h1
    · rw [f1.val (by simp [gF])]; exact hg
    · rw [f1.val (by simp [hT2])]; exact ht
    · intro q q1 q2 q3; rw [f1.val (by simp [q3])]; exact ho q q1 q2 q3

theorem toReg_spec (cap Wb : ℕ) (A Z E : Fin 53) (hAZ : Z ≠ A) (hAE : A ≠ E) (T : Fin NR) (hT1 : T ≠ GLr)
    (hT2 : T ≠ F0) (hT3 : T ≠ R0) (σ : WState NS NR) (w : Fin 53 → ℕ) (hw : MV NB Wb w σ) (hz : w Z = 0)
    (he : w E = 1) (ha : w A < 2 ^ Wb) (t : ℕ) (hs : TS T σ σ 0 t) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapT : t + w A + 1 ≤ cap) :
    Runs cap (toReg A Z E T) σ (toRegCost Wb (w A)) (fun ρ => MV NB Wb (Function.update w A 0) ρ ∧
      TS T σ ρ 0 (t + w A) ∧ ∀ x, x ≠ NB A → ρ.st x = σ.st x ∧ ρ.sh x = σ.sh x) := by
  set a := w A with hadef
  have hFR : F0 ≠ R0 := grN (by decide)
  have gF : GLr ≠ F0 := grN (by decide)
  have gR : GLr ≠ R0 := grN (by decide)
  have hZ' : Function.update w A 0 Z = 0 := by rw [Function.update_of_ne hAZ]; exact hz
  let Inv : ℕ → WState NS NR → Prop := fun k ρ => k ≤ a ∧ MV NB Wb (Function.update w A k) ρ ∧
    TS T σ ρ (decide (0 < k)).toNat (t + (a - k)) ∧ ∀ x, x ≠ NB A → ρ.st x = σ.st x ∧ ρ.sh x = σ.sh x
  have hupd : ∀ k, Function.update w A k Z = 0 := fun k => by rw [Function.update_of_ne hAZ]; exact hz
  refine Runs.seq ((flagS_spec cap Wb A Z hAZ T hT1 hT2 σ σ w hw hz ha t hs hcap).post
    (fun ρ ⟨m, s, fx⟩ => (show Inv a ρ from ⟨le_rfl, by rw [hadef, Function.update_eq_self]; exact m,
      by simpa using s,
      fun x _ => fx x⟩))) (fun τ1 h1 => ?_)
  refine Runs.whr Inv _ _ (fun ρ h => ⟨by have := h.2.2.1.2.2.1; simpa using this, ?_⟩) (fun k ρ h => ⟨?_, ?_⟩) a τ1 h1
  · obtain ⟨_, m, s, fx⟩ := h
    simp only [Nat.sub_zero, decide_eq_false (lt_irrefl 0)] at s
    exact ⟨m, s, fx⟩
  · rw [h.2.2.1.2.2.1]; simp
  · obtain ⟨hk, m, ⟨s0, s1, sg, st, so⟩, fx⟩ := h
    simp only [show 0 < k + 1 from Nat.succ_pos k, decide_true, Bool.toNat_true] at sg
    have e1 := WXExec.dec cap GLr ρ (by rw [sg]; omega)
    set ρ1 := ρ.setv GLr (ρ.val GLr - 1) with hρ1
    have f1 : SameExcept ρ ρ1 [] [GLr] := sameExcept_setv ρ (by simp) _
    have m1 := m.frame' f1 (by simp)
    refine Runs.seqE e1 ?_
    have hEne : A ≠ E := hAE
    refine Runs.seq (mSub cap Wb A E hAE hFR m1 (by rw [f1.val (by simp [gF.symm])]; exact s0)
      (by rw [f1.val (by simp [gR.symm])]; exact s1) (by rw [Function.update_of_ne hAE.symm, he]; simp)
      (by simp; omega) (by omega)) (fun τ2 ⟨m2, f2⟩ => ?_)
    have v2T : τ2.val T = t + (a - (k + 1)) := by rw [f2.val (by simp), f1.val (by simp [hT1]), st]
    have e3 := WXExec.inc cap T τ2 (by rw [v2T]; omega)
    refine Runs.seqE e3 ?_
    have f3 : SameExcept τ2 (τ2.setv T (τ2.val T + 1)) [] [T] := sameExcept_setv τ2 (by simp) _
    have hm3 : MV NB Wb (Function.update w A k) (τ2.setv T (τ2.val T + 1)) := by
      have := m2.frame' f3 (by simp); simpa [Function.update_of_ne hAE.symm, he] using this
    refine (flagS_spec cap Wb A Z hAZ T hT1 hT2 σ _ (Function.update w A k) hm3 (hupd k) (by simp; omega)
      (t + (a - k)) ⟨?_, ?_, ?_, ?_, ?_⟩ hcap).post (fun ρ' ⟨m', s', fx'⟩ => ⟨by omega, m', by simpa using s', ?_⟩)
    · rw [f3.val (by simp [hT2.symm]), f2.val (by simp), f1.val (by simp [gF.symm])]; exact s0
    · rw [f3.val (by simp [hT3.symm]), f2.val (by simp), f1.val (by simp [gR.symm])]; exact s1
    · rw [f3.val (by simp [hT1.symm]), f2.val (by simp), hρ1]; simp [sg]
    · simp [v2T]; omega
    · intro q q1 q2 q3
      rw [f3.val (by simp [q2]), f2.val (by simp), f1.val (by simp [q1])]; exact so q q1 q2 q3
    · intro x hx
      have := fx x hx
      obtain ⟨a1, a2⟩ := fx' x
      have hx' : x ∉ [NB A] := by simp [hx]
      exact ⟨by rw [a1, f3.st (by simp), f2.st hx', f1.st (by simp), this.1],
        by rw [a2, f3.sh (by simp), f2.sh hx', f1.sh (by simp), this.2]⟩

end NearCubicGates.Close.Expand.Layout
