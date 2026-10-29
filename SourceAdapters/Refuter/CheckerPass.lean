import SourceAdapters.Refuter.CheckerPassSegs

/-!
# One pass of the checker (input 7, F01 machine layer, part 12)

SFM78 l.227–230: "This can be checked independently for each tape in turn". Pass `i` copies the
prefix of simulated tape `i` (`copyPrefix`), runs the trace loop (`passLoop`), checks the final
control (`finalChk`), restores the heads and accumulates its verdict into `ALL`.

`pass_spec`: from a reset state (`RestEnc`), `ALL := ALL ∧ passOk v r i (copied tape) ds VD`, where
`ds` is the parsed trace, within `passCost v r n = 60(r+1) + n(stepCost v + 240(|code|+1)) +
1000(|code|+1)` steps for `n` parsed steps; the state is reset again (same `RestEnc`).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

def pass : Pg := .seq copyPrefix (.seq passSetup (.seq passLoop (.seq finalChk (.seq restore accum))))

/-- The reset state between passes (pass index `i`, trace starting at logical position `p`). -/
structure RestEnc (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (wD : List Bool) (p : ℕ)
    (σ : St) : Prop where
  enc : PassEnc v r i wD σ ⟨false, zeroCtl v.machine, σ.st sSIM, 0⟩
  cont : σ.val rCONT = 0
  wp : σ.val rWP = 0
  wit : σ.sh sWIT = 2 * min p wD.length
  start : σ.val rSTART = v.machine.start.val
  vd : σ.val rVD ≤ 1
  r0 : σ.val rR0 = r
  all : σ.val rALL ≤ 1
  i1 : σ.val rI1 = 0
  tg : σ.val rTG = 0
  ws : σ.val rWS ≤ witMoves wD p (gend wD v.tapeCount (wD.length + 1) p)
  xh : σ.sh sXS = 0
  yh : σ.sh sYS = 0
  zh : σ.sh sZ = 0

/-- The parsed trace of a pass. -/
def ptrace (wD : List Bool) (t p : ℕ) : List (Fin t → Bool) := gtrace wD t (wD.length + 1) p

/-- The position after the parsed trace. -/
def pend (wD : List Bool) (t p : ℕ) : ℕ := gend wD t (wD.length + 1) p

def passCost (v : RepairOrdinary.Verifier) (r n : ℕ) : ℕ :=
  60 * (r + 1) + n * (stepCost v + 240 * ((VerifierEncoding.code v).length + 1)) +
    1000 * ((VerifierEncoding.code v).length + 1)

theorem gend_eq (wD : List Bool) (t : ℕ) :
    ∀ f p, gend wD t f p = p + (gtrace wD t f p).length * (1 + t) + 1
  | 0, p => by simp [gend, gtrace]
  | f + 1, p => by
    simp only [gend, gtrace]
    split
    · rw [gend_eq wD t f]; simp; ring
    · simp

theorem gtrace_length_le (wD : List Bool) (t : ℕ) : ∀ f p, (gtrace wD t f p).length ≤ wD.length - p
  | 0, p => by simp [gtrace]
  | f + 1, p => by
    simp only [gtrace]
    split
    · rename_i hg
      have hp : p < wD.length := by
        by_contra hc; rw [gbit_beyond wD (by omega)] at hg; exact absurd hg (by decide)
      have := gtrace_length_le wD t f (p + 1 + t)
      simp; omega
    · simp

theorem passRun_head_le {t s : ℕ} (m : Machine t s) (r : ℕ) (i : Fin t) :
    ∀ (ds : List (Fin t → Bool)) (st : PassSt s), (passRun m r i st ds).head ≤ st.head + ds.length
  | [], st => by simp [passRun]
  | d :: ds, st => by
    unfold passRun
    rw [List.foldl_cons]
    have := passRun_head_le m r i ds (passStep m r i st d)
    have := passStep_head_le m r i st d
    unfold passRun at *
    simp; omega

abbrev passS : List (Fin (NS + 1)) := [sSIM, sRS, sWIT, sDISP]
abbrev passR : List (Fin NR) :=
  [rOK, rQ, rH, rWP, rMK, rOFF, rQN, rW0, rW1, rM0, rM1, rCONT, rBIT, rALL, rWS, rI1]

set_option maxHeartbeats 400000 in
/-- **One pass.** -/
theorem pass_spec (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (wD : List Bool) (p : ℕ)
    (σ : St) (hR : RestEnc v r i wD p σ)
    (hcap : 64 * ((VerifierEncoding.code v).length + 4 * wD.length + r + 8) ≤ cap) :
    ∃ τ, WXExec cap pass σ τ (passCost v r (ptrace wD v.tapeCount p).length) ∧ RestEnc v r i wD p τ ∧
      τ.val rALL = (if passOk v r i (wcopy (σ.st sSIM) (srcOf σ i.val) r) (ptrace wD v.tapeCount p)
        (decide (σ.val rVD ≠ 0)) = true then σ.val rALL else 0) ∧
      τ.val rWS = witMoves wD p (pend wD v.tapeCount p) ∧
      SameExcept σ τ passS passR := by
  have hE := hR.enc
  have b1 := pow_t_le_code v
  have b3 := tapeCount_le_code v
  have b5 := hb_le_code v
  have b7 := stateCount_le_code v
  have hst := v.machine.start.isLt
  have hi := i.isLt
  have hntr : (ptrace wD v.tapeCount p).length ≤ wD.length - p := gtrace_length_le wD v.tapeCount _ p
  have hws := hR.ws
  -- copy and setup
  obtain ⟨σ1, e1, h1⟩ := exEq cap (copyPrefix_spec cap σ hE.simh hR.xh hR.yh hR.zh hR.tg hE.zTB hE.zTA hR.i1
    (by rw [hR.r0, hE.ii]; lomega))
  obtain ⟨σ2, e2, h2⟩ := exEq cap (passSetup_spec cap σ1 (by simp [h1, hE.ok]) (by simp [h1, hE.q, zeroCtl])
    (by simp [h1, hR.cont]) (by simp [h1, hE.zTA]) (by simp [h1, hR.start]; lomega))
  have hcopy : σ2.st sSIM = wcopy (σ.st sSIM) (srcOf σ i.val) r := by simp [h2, h1, hE.ii, hR.r0]
  have hE2 : PassEnc v r i wD σ2 ⟨true, v.machine.start, wcopy (σ.st sSIM) (srcOf σ i.val) r, 0⟩ := by
    constructor
    all_goals first
      | exact hcopy
      | (simp [h2, h1, Function.update_apply, hR.start]; done)
      | (simp [h2, h1, Function.update_apply, hE.code, hE.codeh, hE.t, hE.wd, hE.ew, hE.hb, hE.tbl, hE.bs,
          hE.ii, hE.simh, hE.rs, hE.rsh, hE.wit, hE.disph, hE.zQN, hE.zMK, hE.zP, hE.zOFF, hE.zBIT, hE.zTA,
          hE.zTB, hE.zTC, hE.zPT, hE.zW0, hE.zW1, hE.zM0, hE.zM1, hE.zDI, hE.zA2, hE.h])
  -- the loop
  obtain ⟨σ3, e3, hE3, hc3, hw3, hwp3, hf3⟩ := passLoop_spec cap v r i wD p (by lomega) (wD.length + 1) p σ2 _
    hE2 (by simp [h2]) (by simp [h2, h1, hR.wit]) (by simp [h2, h1, Function.update_apply, hR.wp, witMoves])
    le_rfl (by simp) (by omega)
  set stF := passRun v.machine r i ⟨true, v.machine.start, wcopy (σ.st sSIM) (srcOf σ i.val) r, 0⟩
    (gtrace wD v.tapeCount (wD.length + 1) p) with hstF
  have hhF : stF.head ≤ (ptrace wD v.tapeCount p).length := by
    have := passRun_head_le v.machine r i (gtrace wD v.tapeCount (wD.length + 1) p)
      ⟨true, v.machine.start, wcopy (σ.st sSIM) (srcOf σ i.val) r, 0⟩
    simpa [ptrace] using this
  have hqF := stF.q.isLt
  have hwmF : witMoves wD p (gend wD v.tapeCount (wD.length + 1) p) ≤ 2 * wD.length := by
    unfold witMoves; omega
  have hwmF2 : witMoves wD p (gend wD v.tapeCount (wD.length + 1) p) ≤
      2 * ((ptrace wD v.tapeCount p).length * (1 + v.tapeCount) + 1) := by
    have := gend_eq wD v.tapeCount (wD.length + 1) p
    unfold witMoves ptrace at *; omega
  have fv3 : ∀ x, x ∉ loopR → σ3.val x = σ2.val x := fun x hx => hf3.2.1 x hx
  -- final check, restore, accumulate
  obtain ⟨σ4, e4, h4⟩ := exEq cap (finalChk_spec cap σ3 hE3.zOFF hE3.zTA hE3.zTB hE3.zBIT
    (by rw [hE3.ok]; cases stF.ok <;> simp) (by rw [hE3.hb, hE3.q]; lomega))
  obtain ⟨σ5, e5, h5⟩ := exEq cap (restore_spec cap σ4 (by simp [h4, hE3.zTB]) (by simp [h4, hE3.zTA])
    (by
      have hws3 : σ3.val rWS = σ.val rWS := by
        rw [fv3 _ (by decide)]; simp [h2, h1, Function.update_apply]
      simp [h4, Function.update_apply, hE3.h, hwp3, hws3, hE3.q]
      lomega))
  obtain ⟨σ6, e6, h6⟩ := exEq cap (accum_spec cap σ5
    (by
      have : σ3.val rALL = σ.val rALL := by rw [fv3 _ (by decide)]; simp [h2, h1, Function.update_apply]
      simp [h5, h4, Function.update_apply, this, hR.all])
    (by
      have hok3 : σ3.val rOK ≤ 1 := by rw [hE3.ok]; cases stF.ok <;> simp
      simp [h5, h4, Function.update_apply]; lomega) (by lomega))

  -- frame
  have hF : SameExcept σ σ6 passS passR := by
    have a : SameExcept σ σ2 passS passR := by rw [h2, h1]; peel
    have b : SameExcept σ3 σ6 passS passR := by rw [h6, h5, h4]; peel
    exact (a.trans (hf3.weaken (by decide) (by decide))).trans b
  have fv6 : ∀ x, x ∉ passR → σ6.val x = σ.val x := fun x hx => hF.2.1 x hx
  have fs6 : ∀ x, x ∉ passS → σ6.st x = σ.st x := fun x hx => (hF.1 x hx).1
  have fsh6 : ∀ x, x ∉ passS → σ6.sh x = σ.sh x := fun x hx => (hF.1 x hx).2
  have hvd3 : σ3.val rVD = σ.val rVD := by rw [fv3 _ (by decide)]; simp [h2, h1, Function.update_apply]
  have hall3 : σ3.val rALL = σ.val rALL := by rw [fv3 _ (by decide)]; simp [h2, h1, Function.update_apply]
  have hws3 : σ3.val rWS = σ.val rWS := by rw [fv3 _ (by decide)]; simp [h2, h1, Function.update_apply]
  have hH : readTapeBit (code v) (cHb v + ↑stF.q + ↑stF.q) = v.machine.halted stF.q := by
    rw [show cHb v + ↑stF.q + ↑stF.q = cHb v + 2 * ↑stF.q by ring]; exact code_halted v stF.q
  have hA : readTapeBit (code v) (cHb v + ↑stF.q + ↑stF.q + 1) = v.accepting stF.q := by
    rw [show cHb v + ↑stF.q + ↑stF.q + 1 = cHb v + 2 * ↑stF.q + 1 by ring]; exact code_accepting v stF.q
  have hgend := gend_ge wD v.tapeCount (wD.length + 1) p
  refine ⟨σ6, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).mono ?_,
    ?_, ?_, ?_, hF⟩
  · -- cost
    have hn1 : (ptrace wD v.tapeCount p).length * (1 + v.tapeCount) ≤
        (ptrace wD v.tapeCount p).length * ((code v).length + 1) := Nat.mul_le_mul_left _ (by omega)
    have hx1 : (ptrace wD v.tapeCount p).length * (stepCost v + 40) =
        (ptrace wD v.tapeCount p).length * stepCost v + 40 * (ptrace wD v.tapeCount p).length := by ring
    have hx2 : (ptrace wD v.tapeCount p).length * (stepCost v + 240 * ((code v).length + 1)) =
        (ptrace wD v.tapeCount p).length * stepCost v +
          240 * ((ptrace wD v.tapeCount p).length * ((code v).length + 1)) := by ring
    have hR0 := hR.r0
    have hst1 := hR.start
    have c2 : σ3.val rWP ≤ 2 * ((gtrace wD v.tapeCount (wD.length + 1) p).length * (1 + v.tapeCount) + 1) := by
      rw [hwp3]; exact hwmF2
    have c1 : σ3.val rWS ≤ 2 * ((gtrace wD v.tapeCount (wD.length + 1) p).length * (1 + v.tapeCount) + 1) := by
      rw [hws3]; exact hR.ws.trans hwmF2
    have c3 : stF.head ≤ (gtrace wD v.tapeCount (wD.length + 1) p).length := hhF
    have c4 : (gtrace wD v.tapeCount (wD.length + 1) p).length ≤
        (gtrace wD v.tapeCount (wD.length + 1) p).length * ((code v).length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    unfold passCost
    simp only [ptrace] at hx1 hx2 hn1 hhF hwmF2 ⊢
    simp [h5, h4, h1, Function.update_apply, hE3.hb, hE3.q, hE3.h, hR.r0, hE.ii, hR.start]
    lomega
  · exact {
      enc := {
        code := (by simp [h6, h5, h4, Function.update_apply, hE3.code]),
        codeh := (by simp [h6, h5, h4, Function.update_apply, hE3.codeh]),
        t := (by simp [h6, h5, h4, Function.update_apply, hE3.t]),
        wd := (by simp [h6, h5, h4, Function.update_apply, hE3.wd]),
        ew := (by simp [h6, h5, h4, Function.update_apply, hE3.ew]),
        hb := (by simp [h6, h5, h4, Function.update_apply, hE3.hb]),
        tbl := (by simp [h6, h5, h4, Function.update_apply, hE3.tbl]),
        bs := (by simp [h6, h5, h4, Function.update_apply, hE3.bs]),
        ii := (by simp [h6, h5, h4, Function.update_apply, hE3.ii]),
        ok := (by simp [h6]),
        q := (by simp [h6, h5, Function.update_apply, zeroCtl]),
        h := (by simp [h6, h5, Function.update_apply]),
        sim := rfl,
        simh := (by simp [h6, h5, h4, Function.update_apply, hE3.simh, hE3.h]),
        rs := (by simp [h6, h5, h4, Function.update_apply, hE3.rs]),
        rsh := (by simp [h6, h5, h4, Function.update_apply, hE3.rsh, hE3.h]),
        wit := (by simp [h6, h5, h4, Function.update_apply, hE3.wit]),
        disph := (by simp [h6, h5, h4, Function.update_apply, hE3.disph]),
        zQN := (by simp [h6, h5, h4, Function.update_apply, hE3.zQN]),
        zMK := (by simp [h6, h5, h4, Function.update_apply, hE3.zMK]),
        zP := (by simp [h6, h5, h4, Function.update_apply, hE3.zP]),
        zOFF := (by simp [h6, h5, h4, Function.update_apply, hE3.zOFF]),
        zBIT := (by simp [h6, h5, h4, Function.update_apply, hE3.zBIT]),
        zTA := (by simp [h6, h5, h4, Function.update_apply, hE3.zTA]),
        zTB := (by simp [h6, h5, h4, Function.update_apply, hE3.zTB]),
        zTC := (by simp [h6, h5, h4, Function.update_apply, hE3.zTC]),
        zPT := (by simp [h6, h5, h4, Function.update_apply, hE3.zPT]),
        zW0 := (by simp [h6, h5, h4, Function.update_apply, hE3.zW0]),
        zW1 := (by simp [h6, h5, h4, Function.update_apply, hE3.zW1]),
        zM0 := (by simp [h6, h5, h4, Function.update_apply, hE3.zM0]),
        zM1 := (by simp [h6, h5, h4, Function.update_apply, hE3.zM1]),
        zDI := (by simp [h6, h5, h4, Function.update_apply, hE3.zDI]),
        zA2 := (by simp [h6, h5, h4, Function.update_apply, hE3.zA2]) },
      cont := (by simp [h6, h5, h4, Function.update_apply, hc3]),
      wp := (by simp [h6, h5, Function.update_apply]),
      wit := (by simp [h6, h5, h4, Function.update_apply, hw3, hwp3, witMoves]; omega),
      start := (by rw [fv6 _ (by decide)]; exact hR.start),
      vd := (by rw [fv6 _ (by decide)]; exact hR.vd),
      r0 := (by rw [fv6 _ (by decide)]; exact hR.r0),
      all := (by simp [h6, Function.update_apply]; split <;> simp [h5, h4, Function.update_apply, hall3, hR.all]),
      i1 := (by simp [h6, h5, h4, Function.update_apply, fv3 rI1 (by decide), h2, h1, hR.i1]),
      tg := (by rw [fv6 _ (by decide)]; exact hR.tg),
      ws := (by simp [h6, h5, h4, Function.update_apply, hwp3]),
      xh := (by rw [fsh6 _ (by decide)]; exact hR.xh),
      yh := (by rw [fsh6 _ (by decide)]; exact hR.yh),
      zh := (by rw [fsh6 _ (by decide)]; exact hR.zh) }
  · -- the verdict
    have hok : σ3.val rOK = stF.ok.toNat := hE3.ok
    simp only [h6, h5, h4, WState.setv_val, WState.seth_st, WState.setv_st, WState.seth_sh, WState.setv_sh,
      Function.update_apply]
    simp [hE3.code, hE3.codeh, hE3.hb, hE3.q, hH, hA, hvd3, hall3, hok, passOk, ptrace, ← hstF]
    generalize stF.ok = b1
    generalize v.machine.halted stF.q = b2
    generalize v.accepting stF.q = b3
    by_cases hv : σ.val rVD = 0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp [hv]
  · simp [h6, h5, h4, Function.update_apply, hwp3, pend]

end NearCubicGates.Adapters.Refuter.Mach
