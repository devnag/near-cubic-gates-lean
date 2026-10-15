import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicWires.ExtDecompositionBatch

/-- One tape of a run stays blank beyond the starting bound plus the steps taken. -/
theorem runFrom_far {t s : ℕ} (M : Machine t s) (i : Fin t) :
    ∀ (fuel : ℕ) (c : Configuration t s) (B : ℕ) (r : ExecutionReceipt t s),
      runFrom M fuel c = some r → c.heads i ≤ B → (∀ q, B < q → readTapeBit (c.tapes i) q = false) →
      r.final.heads i ≤ B + r.steps ∧ ∀ q, B + r.steps < q → readTapeBit (r.final.tapes i) q = false
  | 0, c, B, r, hr, hh, hq => by
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨by simpa using hh, by simpa using hq⟩
    · contradiction
  | fuel + 1, c, B, r, hr, hh, hq => by
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact ⟨by simpa using hh, by simpa using hq⟩
    · cases hs : step M c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom M fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst hr
          unfold step at hs
          cases ha : M.rule c.control c.scanned with
          | none => simp [ha] at hs
          | some a =>
            simp only [ha, Option.map_some, Option.some.injEq] at hs
            subst hs
            have hdh : (applyAction c a).heads i ≤ B + 1 := by
              simp only [applyAction]
              cases a.move i <;> simp [HeadMove.apply] <;> omega
            have hdq : ∀ q, B + 1 < q → readTapeBit ((applyAction c a).tapes i) q = false := by
              intro q hqB
              simp only [applyAction]
              cases a.write i with
              | none => exact hq q (by omega)
              | some v =>
                rw [readTapeBit_write, if_neg (by omega)]
                exact hq q (by omega)
            obtain ⟨h1, h2⟩ := runFrom_far M i fuel _ (B + 1) tail ht hdh hdq
            refine ⟨by simp only; omega, fun q hqB => h2 q (by simp only at hqB; omega)⟩

/-- **Far blank.** After a `Step` of at most `n` steps from head `0` on a tape that reads blank, the tape reads
`false` beyond `n`. -/
theorem step_far {t s n : ℕ} {M : Machine t s} {hin : Fin t → ℕ} {tin : Fin t → List Bool} {hout : Fin t → ℕ}
    {tout : Fin t → List Bool} (h : Step M n hin tin hout tout) (i : Fin t) (h0 : hin i = 0)
    (hb : RdEq (tin i) []) : ∀ q, n < q → readTapeBit (tout i) q = false := by
  obtain ⟨r, hr, _, ht, hs⟩ := h
  have := runFrom_far M i n _ 0 r hr (by simpa using h0) (fun q _ => by
    simp only
    rw [hb q]
    rfl)
  intro q hq
  rw [← ht]
  exact this.2 q (by omega)

/-- Overwrite the first `m` cells with `false`. -/
def clearPrefix (m : ℕ) (l : List Bool) : List Bool := List.replicate m false ++ l.drop m

theorem clearPrefix_blank (m : ℕ) (l : List Bool) (hl : ∀ q, m ≤ q → readTapeBit l q = false) :
    RdEq (clearPrefix m l) [] := by
  intro q
  unfold clearPrefix readTapeBit
  by_cases hq : q < m
  · rw [List.getD_append _ _ _ _ (by simpa using hq)]
    simp [hq]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have := hl q (by omega)
    unfold readTapeBit at this
    simp only [List.length_replicate, List.getD_eq_getElem?_getD, List.getElem?_drop] at this ⊢
    rw [show m + (q - m) = q by omega, this]
    simp

theorem write_clear (p : ℕ) (l : List Bool) :
    writeTapeBit (List.replicate p false ++ l.drop p) p false = List.replicate (p + 1) false ++ l.drop (p + 1) := by
  induction p generalizing l with
  | zero =>
    cases l with
    | nil => rfl
    | cons b t => rfl
  | succ p ih =>
    cases l with
    | nil =>
      simp only [List.replicate_succ, List.drop_nil, List.cons_append, writeTapeBit]
      have := ih []
      simp only [List.drop_nil] at this
      rw [this]
      simp [List.replicate_succ]
    | cons b t =>
      simp only [List.replicate_succ, List.drop_succ_cons, List.cons_append, writeTapeBit]
      rw [ih t]
      simp [List.replicate_succ]

variable {ns nr : ℕ}

/-- Clear the first `m` cells of stream `X`, driven by stream `T = 1^m`, counting in register `R`. -/
def clearOne (X T : Fin (ns + 1)) (R : Fin nr) : WMX ns nr :=
  .seq (.whs T (.seq (WMX.wr X false) (.seq (WMX.fwd X) (.seq (WMX.fwd T) (WMX.inc R)))))
    (.whr R (.seq (WMX.bwd X) (.seq (WMX.bwd T) (WMX.dec R))))

section ClearOne
variable {cap : ℕ} (X T : Fin (ns + 1)) (R : Fin nr) (hXT : X ≠ T)
include hXT

theorem clear_forward (m : ℕ) (hm : m ≤ cap) (X0 : List Bool) :
    ∀ k p, p + k = m → ∀ σ : WState ns nr, σ.st T = List.replicate m true → σ.sh T = p → σ.sh X = p →
      σ.val R = p → σ.st X = List.replicate p false ++ X0.drop p →
      WXExec cap (.whs T (.seq (WMX.wr X false) (.seq (WMX.fwd X) (.seq (WMX.fwd T) (WMX.inc R))))) σ
        ((((σ.sets X (List.replicate m false ++ X0.drop m)).seth X m).seth T m).setv R m) (k * 11 + 1)
  | 0, p, hpk, σ, hT, hTh, hXh, hR, hX => by
    have hp : p = m := by omega
    subst hp
    have hb : wbit σ T = false := by
      simp only [wbit, hT, hTh]
      unfold readTapeBit
      rw [List.getD_eq_default _ _ (by simp)]
    have e : (((σ.sets X (List.replicate p false ++ X0.drop p)).seth X p).seth T p).setv R p = σ := by
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all
      · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        split_ifs with h1 <;> subst_vars <;> simp_all
      · funext j; simp only [WState.setv_val, Function.update_apply]; split_ifs with h1 <;> subst_vars <;> simp_all
      · rfl
    rw [e]
    exact WXExec.mono (WXExec.whsF hb) (by omega)
  | k + 1, p, hpk, σ, hT, hTh, hXh, hR, hX => by
    have hb : wbit σ T = true := by
      simp only [wbit, hT, hTh]
      unfold readTapeBit
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    let σ1 := σ.sets X (writeTapeBit (σ.st X) (σ.sh X) false)
    let σ2 := σ1.seth X (σ1.sh X + 1)
    let σ3 := σ2.seth T (σ2.sh T + 1)
    have hlt : σ3.val R < cap := by simp [σ3, σ2, σ1, hR]; omega
    have hbody := WXExec.seq (WXExec.wr (cap := cap) X false σ) (WXExec.seq (WXExec.fwd (cap := cap) X σ1)
      (WXExec.seq (WXExec.fwd (cap := cap) T σ2) (WXExec.inc (cap := cap) R σ3 hlt)))
    let σ4 := σ3.setv R (σ3.val R + 1)
    have ih := clear_forward m hm X0 k (p + 1) (by omega) σ4
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hXT.symm, hT])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hTh])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hXT, hXh])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hR])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hX, hXh, write_clear])
    refine WXExec.mono (WXExec.cast cap (WXExec.whsT hb hbody ih) ?_ le_rfl) (by nlinarith)
    apply WState.eq
    · funext j; simp only [σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> rfl
    · funext j; simp only [σ4, σ3, σ2, σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> rfl
    · funext j; simp only [σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> rfl
    · rfl

theorem clear_back : ∀ k, ∀ σ : WState ns nr, σ.val R = k → σ.sh X = k → σ.sh T = k → k ≤ cap →
    WXExec cap (.whr R (.seq (WMX.bwd X) (.seq (WMX.bwd T) (WMX.dec R)))) σ
      (((σ.seth X 0).seth T 0).setv R 0) (k * 7 + 1)
  | 0, σ, hR, hX, hT, _ => by
    have e : ((σ.seth X 0).seth T 0).setv R 0 = σ := by
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all
      · rfl
      · funext j; simp only [WState.setv_val, Function.update_apply]; split_ifs with h1 <;> subst_vars <;> simp_all
      · rfl
    rw [e]
    exact WXExec.whrF hR
  | k + 1, σ, hR, hX, hT, hk => by
    let σ1 := σ.seth X (σ.sh X - 1)
    let σ2 := σ1.seth T (σ1.sh T - 1)
    have hbody := WXExec.seq (WXExec.bwd (cap := cap) X σ) (WXExec.seq (WXExec.bwd (cap := cap) T σ1)
      (WXExec.dec (cap := cap) R σ2 (by simp [σ2, σ1, hR]; omega)))
    let σ3 := σ2.setv R (σ2.val R - 1)
    have ih := clear_back k σ3 (by simp [σ3, σ2, σ1, hR]) (by simp [σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hXT, hX])
      (by simp [σ3, σ2, σ1, Function.update_apply, hXT, hXT.symm, hT]) (by omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by rw [hR]; omega) hbody ih) ?_ le_rfl) (by nlinarith)
    apply WState.eq
    · funext j; simp only [σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> rfl
    · rfl
    · funext j; simp only [σ3, σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> rfl
    · rfl

/-- **Clear.** From heads `0`, `T = 1^m`, `R = 0`: the first `m` cells of `X` become `false`; nothing else changes. -/
theorem clearOne_exec (m : ℕ) (hm : m ≤ cap) (σ : WState ns nr) (hT : σ.st T = List.replicate m true)
    (hTh : σ.sh T = 0) (hXh : σ.sh X = 0) (hR : σ.val R = 0) :
    WXExec cap (clearOne X T R) σ (σ.sets X (clearPrefix m (σ.st X))) (m * 18 + 3) := by
  have h1 := clear_forward X T R hXT m hm (σ.st X) m 0 (by omega) σ hT hTh hXh hR (by simp)
  set σ1 := (((σ.sets X (List.replicate m false ++ (σ.st X).drop m)).seth X m).seth T m).setv R m
  have h2 := clear_back X T R hXT m σ1 (by simp [σ1]) (by simp [σ1, Function.update_apply, hXT, hXT.symm, hXT])
    (by simp [σ1]) hm
  refine WXExec.mono (WXExec.cast cap (WXExec.seq h1 h2) ?_ le_rfl) (by nlinarith)
  apply WState.eq
  · funext j; simp only [σ1, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  · funext j; simp only [σ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply, clearPrefix]
  · funext j; simp only [σ1, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with h1 <;> subst_vars <;> simp_all
  · rfl

end ClearOne

theorem readTapeBit_beyond (l : List Bool) (q : ℕ) (h : l.length ≤ q) : readTapeBit l q = false := by
  unfold readTapeBit
  rw [List.getD_eq_default _ _ h]

theorem wordFunction_machZ_far {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) {cap : ℕ}
    (tmap : Fin f.program.tapeCount → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1))
    (hL : ∀ j, tmap j ≠ L) (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0)
    (hin : ∀ j, RdEq (σ.st (tmap j)) (f.program.inputTapes (input req) j))
    (lcap : ℕ) (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hn : budget req ≤ lcap) :
    ∃ τ tout, WXExec cap (WMX.machZ f.program.machine tmap L) σ τ (2 * budget req + 2) ∧
      Docked tmap σ τ (fun _ => 0) tout ∧ RdEq (τ.st (tmap f.program.outputTape)) (output req) ∧
      ∀ j q, (f.program.inputTapes (input req) j).length + budget req < q → readTapeBit (τ.st (tmap j)) q = false := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes req
  have hrel : ConfRel (fun _ => False) (initialConfiguration f.program.machine (f.program.inputTapes (input req)))
      ⟨f.program.machine.start, fun _ => 0, fun j => σ.st (tmap j)⟩ :=
    ⟨rfl, rfl, fun j => (hin j).symm, fun _ h => h.elim⟩
  obtain ⟨r', hr', hrel', hs⟩ := runFrom_rel f.program.machine _ (budget req) hrel receipt hrun
  obtain ⟨τ, hτ, hd⟩ := WXExec.machZ_ex cap hinj hL σ (Step.of_run (r := r') hr' rfl rfl) h0 hLst hLsh hn
  refine ⟨τ, r'.final.tapes, hτ, hd, ?_, ?_⟩
  · rw [hd.st]
    exact (hrel'.read f.program.outputTape).symm.trans (by rw [hout]; exact RdEq.refl _)
  · intro j q hq
    have hsteps : r'.steps ≤ budget req := hs ▸ runFrom_steps_le _ _ _ receipt hrun
    have hfar := runFrom_far f.program.machine j (budget req) _ (f.program.inputTapes (input req) j).length r' hr'
      (by simp) (fun q hq => by
        simp only
        rw [hin j q]
        exact readTapeBit_beyond _ _ (by omega))
    rw [hd.st]
    exact hfar.2 q (by omega)

end NearCubicGates.Close.CheckedPCPP
