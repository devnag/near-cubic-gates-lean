import SourceAdapters.Refuter.CheckerReplay
import SourceAdapters.Refuter.CheckerBounds

/-!
# One checking step realizes `passStep` (input 7, F01 machine layer, part 8)

`stepBody` is one guessed step of pass `i`: read the display, check the control is not halted, look
the action up in the table, read its next control and tape `i`'s write and move codes, check the
cutoff and the scanned cell, apply the write and the move, adopt the next control.

`stepBody_spec`: from a state encoding the pass state `st` (`PassEnc`), with the witness head at
logical position `p`, the step ends in a state encoding `passStep st d` for the guessed display
`d = gdisp wD p t`, the witness head at `p + t`, within `stepCost v = 3000(|code(M)|+1)^2` steps —
a constant of the simulated machine (the `b_M` of proof of `cor:framed-refuter`), independent of the input, the
witness and the clock.
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

def stepBody : Pg :=
  .seq dispLoop (.seq haltChk (.seq entry (.seq nextCtl (.seq actBits
    (.seq replayChk (.seq replayWr (.seq replayMv (.seq clears finish))))))))

/-- **The encoding of a pass state** on the checker's layout (scratch registers zero). -/
structure PassEnc (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (wD : List Bool)
    (σ : St) (st : PassSt v.stateCount) : Prop where
  code : σ.st sCODE = VerifierEncoding.code v
  codeh : σ.sh sCODE = 0
  t : σ.val rT = v.tapeCount
  wd : σ.val rWD = cWd v
  ew : σ.val rEW = cEw v
  hb : σ.val rHB = cHb v
  tbl : σ.val rAT = cAt v
  bs : σ.val rBS = cBs v
  ii : σ.val rI = i.val
  ok : σ.val rOK = st.ok.toNat
  q : σ.val rQ = st.q.val
  h : σ.val rH = st.head
  sim : σ.st sSIM = st.tape
  simh : σ.sh sSIM = st.head
  rs : ∀ h, readTapeBit (σ.st sRS) h = decide (h < r)
  rsh : σ.sh sRS = st.head
  wit : σ.st sWIT = RepairOrdinary.frame wD
  disph : σ.sh sDISP = 0
  zQN : σ.val rQN = 0
  zMK : σ.val rMK = 0
  zP : σ.val rP = 0
  zOFF : σ.val rOFF = 0
  zBIT : σ.val rBIT = 0
  zTA : σ.val rTA = 0
  zTB : σ.val rTB = 0
  zTC : σ.val rTC = 0
  zPT : σ.val rPT = 0
  zW0 : σ.val rW0 = 0
  zW1 : σ.val rW1 = 0
  zM0 : σ.val rM0 = 0
  zM1 : σ.val rM1 = 0
  zDI : σ.val rDI = 0
  zA2 : σ.val rA2 = 0

/-- The per-step cost bound `b_M`. -/
def stepCost (v : RepairOrdinary.Verifier) : ℕ := 3000 * ((VerifierEncoding.code v).length + 1) ^ 2

theorem rd_replicate_true (r h : ℕ) : readTapeBit (List.replicate r true) h = decide (h < r) := by
  by_cases hh : h < r
  · rw [rd_replicate _ _ hh]; simp [hh]
  · rw [rd_beyond _ (by simp; omega)]; simp [hh]

/-- The write code of tape `i`, as the machine applies it. -/
theorem writeCode_apply (o : Option Bool) (tape : List Bool) (h : ℕ) :
    (if (readTapeBit (writeCode o ++ moveCode .stay) 0).toNat ≠ 0 then
      writeTapeBit tape h (decide ((readTapeBit (writeCode o ++ moveCode .stay) 1).toNat ≠ 0))
      else tape) = (match o with | none => tape | some b => writeTapeBit tape h b) := by
  rcases o with _ | _ | _ <;> rfl

theorem moveCode_apply (o : Option Bool) (mv : HeadMove) (h : ℕ) :
    mvHead (readTapeBit (writeCode o ++ moveCode mv) 2).toNat
      (readTapeBit (writeCode o ++ moveCode mv) 3).toNat h = mv.apply h := by
  rcases o with _ | _ | _ <;> cases mv <;> rfl

theorem writeBits_indep (o : Option Bool) (mv mv' : HeadMove) (k : ℕ) (hk : k < 2) :
    readTapeBit (writeCode o ++ moveCode mv) k = readTapeBit (writeCode o ++ moveCode mv') k := by
  interval_cases k <;> rcases o with _ | _ | _ <;> rfl

theorem ok_combine (ok hlt sm cut eq : Bool) :
    (if cut = true ∧ eq = true then
      (if sm = true then (if hlt = true then 0 else ok.toNat) else 0) else 0) =
      (ok && !hlt && sm && cut && eq).toNat := by
  cases ok <;> cases hlt <;> cases sm <;> cases cut <;> cases eq <;> rfl

section Frames
variable {σ τ : St} {S : List (Fin (NS + 1))} {Rg : List (Fin NR)}

theorem se_setv (h : SameExcept σ τ S Rg) {r : Fin NR} (hr : r ∈ Rg) (v : ℕ) :
    SameExcept σ (τ.setv r v) S Rg :=
  h.trans (sameExcept_setv τ hr v)

theorem se_seth (h : SameExcept σ τ S Rg) {X : Fin (NS + 1)} (hX : X ∈ S) (n : ℕ) :
    SameExcept σ (τ.seth X n) S Rg := h.trans (sameExcept_seth τ hX n)

theorem se_sets (h : SameExcept σ τ S Rg) {X : Fin (NS + 1)} (hX : X ∈ S) (l : List Bool) :
    SameExcept σ (τ.sets X l) S Rg := h.trans (sameExcept_sets τ hX l)

end Frames

/-- Prove a frame `SameExcept σ τ S Rg` for an explicit update chain `τ` of `σ`, layer by layer. -/
macro "peel" : tactic => `(tactic| repeat (first
  | exact SameExcept.refl _ _ _
  | refine se_setv ?_ (by decide) _
  | refine se_seth ?_ (by decide) _
  | refine se_sets ?_ (by decide) _))

/-- The streams and registers a step may change. -/
abbrev stepS : List (Fin (NS + 1)) := [sSIM, sRS, sWIT, sDISP]
abbrev stepR : List (Fin NR) := [rOK, rQ, rH, rWP, rMK, rOFF, rQN, rW0, rW1, rM0, rM1]

theorem exEq {P : Pg} {σ τ : St} {c : ℕ} (h : WXExec cap P σ τ c) :
    ∃ τ', WXExec cap P σ τ' c ∧ τ' = τ := ⟨_, h, rfl⟩

set_option maxHeartbeats 400000 in
/-- **One step realizes `passStep`** within `stepCost v` steps (SFM78 l.222–233 per step). -/
theorem stepBody_spec (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (wD : List Bool)
    (σ : St) (st : PassSt v.stateCount) (p : ℕ) (hE : PassEnc v r i wD σ st)
    (hp : σ.sh sWIT = 2 * min p wD.length)
    (hcap : 64 * ((VerifierEncoding.code v).length + wD.length + st.head + σ.val rWP + 8) ≤ cap) :
    ∃ τ, WXExec cap stepBody σ τ (stepCost v) ∧
      PassEnc v r i wD τ (passStep v.machine r i st (gdisp wD p v.tapeCount)) ∧
      τ.sh sWIT = 2 * min (p + v.tapeCount) wD.length ∧
      τ.val rWP = σ.val rWP + witMoves wD p (p + v.tapeCount) ∧
      SameExcept σ τ stepS stepR := by
  have hq := st.q.isLt
  have hmklt : mkA wD p v.tapeCount < 2 ^ v.tapeCount := mkA_lt wD p v.tapeCount
  have b1 := pow_t_le_code v
  have b2 := pow_wd_le_code v
  have b3 := tapeCount_le_code v
  have b4 := wd_le_code v
  have b5 := hb_le_code v
  have b6 := entry_end_le v st.q.val hq _ hmklt
  have b7 := stateCount_le_code v
  have b8 := ctl_lt_pow v st.q
  have hwm : witMoves wD p (p + v.tapeCount) ≤ 2 * wD.length := by unfold witMoves; omega
  have hi := i.isLt
  obtain ⟨σ1, e1, h1⟩ := exEq cap (dispLoop_spec cap σ wD p v.tapeCount hE.wit hp hE.t hE.zBIT hE.zPT
    hE.zTA hE.zMK hE.zP hE.zTC hE.zTB hE.disph (by lomega))
  obtain ⟨σ2, e2, h2⟩ := exEq cap (haltChk_spec cap σ1 (by simp [h1, Function.update_apply, hE.zOFF])
    (by simp [h1, Function.update_apply, hE.zTA]) (by simp [h1, Function.update_apply, hE.zTB])
    (by simp [h1, Function.update_apply, hE.zBIT]) (by simp [h1, Function.update_apply, hE.ok]; lomega)
    (by simp [h1, Function.update_apply, hE.hb, hE.q]; lomega))
  obtain ⟨σ3, e3, h3⟩ := exEq cap (entry_spec cap σ2 (by simp [h2, h1, Function.update_apply, hE.zOFF])
    (by simp [h2, h1, Function.update_apply, hE.zTA]) (by simp [h2, h1, Function.update_apply, hE.zTB])
    (by simp [h2, h1, Function.update_apply, hE.zBIT]) (by simp [h2, h1, Function.update_apply, hE.zA2])
    (by simp [h2, h1, Function.update_apply, hE.ok]; lomega)
    (by simp [entryOff, h2, h1, Function.update_apply, hE.tbl, hE.q, hE.bs, hE.ew]; lomega))
  obtain ⟨σ4, e4, h4⟩ := exEq cap (nextCtl_spec cap σ3 (cWd v)
    (by simp [h3, h2, h1, Function.update_apply, hE.wd])
    (by simp [h3, h2, h1, Function.update_apply, hE.zBIT]) (by simp [h3, h2, h1, Function.update_apply, hE.zPT])
    (by simp [h3, h2, h1, Function.update_apply, hE.zTA]) (by simp [h3, h2, h1, Function.update_apply, hE.zTB])
    (by simp [h3, h2, h1, Function.update_apply, hE.zQN]) (by simp [h3, h2, h1, Function.update_apply, hE.zP])
    (by simp [h3, h2, h1, Function.update_apply, hE.zTC])
    (by simp [entryOff, h3, h2, h1, Function.update_apply, hE.tbl, hE.q, hE.bs, hE.ew]; lomega))
  have hacc := accBits_lt (σ3.st sCODE) (σ3.sh sCODE + σ3.val rOFF) (cWd v)
  simp [h3, h2, h1, Function.update_apply, entryOff, hE.tbl, hE.q, hE.bs, hE.ew, hE.code, hE.codeh] at hacc
  obtain ⟨σ5, e5, h5⟩ := exEq cap (actBits_spec cap σ4
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zTA])
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zTB])
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zW0])
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zW1])
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zM0])
    (by simp [h4, h3, h2, h1, Function.update_apply, hE.zM1])
    (by simp [entryOff, h4, h3, h2, h1, Function.update_apply, hE.tbl, hE.q, hE.bs, hE.ew, hE.ii]; lomega))
  obtain ⟨σ6, e6, h6⟩ := exEq cap (replayChk_spec cap σ5
    (by simp [h5, h4, h3, h2, h1, Function.update_apply, hE.ok]; lomega)
    (by simp [h5, h4, h3, h2, h1, Function.update_apply, hE.zDI])
    (by simp [h5, h4, h3, h2, h1, Function.update_apply, hE.zTB])
    (by simp [h5, h4, h3, h2, h1, Function.update_apply, hE.ii]; lomega))
  obtain ⟨σ7, e7, h7⟩ := exEq cap (replayWr_spec cap σ6)
  obtain ⟨σ8, e8, h8⟩ := exEq cap (replayMv_spec cap σ7 st.head
    (by simp [h7, h6, h5, h4, h3, h2, h1, hE.simh]) (by simp [h7, h6, h5, h4, h3, h2, h1, hE.rsh])
    (by simp [h7, h6, h5, h4, h3, h2, h1, Function.update_apply, hE.h]) (by lomega))
  obtain ⟨σ9, e9, h9⟩ := exEq cap (clears_spec cap σ8
    (by simp [h8, h7, h6, h5, Function.update_apply]; lomega)
    (by simp [h8, h7, h6, h5, Function.update_apply]; lomega)
    (by simp [h8, h7, h6, h5, Function.update_apply]; lomega)
    (by simp [h8, h7, h6, h5, Function.update_apply]; lomega) (by lomega))
  obtain ⟨σ10, e10, h10⟩ := exEq cap (finish_spec cap σ9
    (by simp [h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, hE.q, hE.zMK, entryOff, hE.tbl,
      hE.bs, hE.ew, hE.code, hE.codeh]; lomega))
  -- the semantic facts read by the machine
  have hmkd : maskDisplay v.tapeCount (mkA wD p v.tapeCount) = gdisp wD p v.tapeCount := by
    rw [mkA_eq, maskDisplay_maskL]
  have hH : readTapeBit (code v) (cHb v + 2 * ↑st.q) = v.machine.halted st.q := code_halted v st.q
  have hS : readTapeBit (code v) (cAt v + ↑st.q * cBs v + mkA wD p v.tapeCount * cEw v) =
      (v.machine.rule st.q (gdisp wD p v.tapeCount)).isSome := by
    rw [code_entry_some v st.q _ hmklt, hmkd]
  have hN : accBits (code v) (cAt v + ↑st.q * cBs v + mkA wD p v.tapeCount * cEw v + 1) (cWd v) =
      (decodedAction v.machine st.q (gdisp wD p v.tapeCount)).nextControl.val := by
    rw [accBits_eq]
    have e : (fun j : Fin (cWd v) =>
        readTapeBit (code v) (cAt v + ↑st.q * cBs v + mkA wD p v.tapeCount * cEw v + 1 + j.val)) =
        fun j : Fin (cWd v) =>
          (decodedAction v.machine st.q (gdisp wD p v.tapeCount)).nextControl.val.testBit j.val := by
      funext j; rw [code_nextBit v st.q _ hmklt j.val j.isLt, hmkd]
    rw [e, maskL_ofFn_testBit _ _ (ctl_lt_pow v _)]
  have hW : ∀ k < 4, readTapeBit (code v)
      (cAt v + ↑st.q * cBs v + mkA wD p v.tapeCount * cEw v + 1 + cWd v + 4 * ↑i + k) =
      readTapeBit (writeCode ((decodedAction v.machine st.q (gdisp wD p v.tapeCount)).write i) ++
        moveCode ((decodedAction v.machine st.q (gdisp wD p v.tapeCount)).move i)) k := by
    intro k hk; rw [code_actBit v st.q _ hmklt i k hk, hmkd]
  have hW0 := hW 0 (by norm_num)
  have hW1 := hW 1 (by norm_num)
  have hW2 := hW 2 (by norm_num)
  have hW3 := hW 3 (by norm_num)
  simp only [Nat.add_zero] at hW0
  have hD : readTapeBit (dispA wD p (σ.st 7) v.tapeCount) ↑i = gdisp wD p v.tapeCount i := by
    rw [dispA_read wD p _ v.tapeCount i.val i.isLt]; rfl
  have hR := rd_replicate_true r st.head
  have hF : SameExcept σ σ10 stepS stepR := by
    rw [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
    peel
  have fs : ∀ x, x ∉ stepS → σ10.st x = σ.st x := fun x hx => (hF.1 x hx).1
  have fsh : ∀ x, x ∉ stepS → σ10.sh x = σ.sh x := fun x hx => (hF.1 x hx).2
  have fv : ∀ x, x ∉ stepR → σ10.val x = σ.val x := fun x hx => hF.2.1 x hx
  have fok : σ10.val rOK = (passStep v.machine r i st (gdisp wD p v.tapeCount)).ok.toNat := by
    simp only [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, WState.setv_val, WState.sets_st, WState.seth_sh,
      WState.setv_st, WState.setv_sh, WState.seth_st, WState.sets_sh, Function.update_apply, entryOff, wbit]
    simp [hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh, hE.ok, hE.sim, hE.simh, hE.rs, hE.rsh,
      hE.disph, hH, hS, hD, hR, passStep]
    generalize st.ok = b1
    generalize v.machine.halted st.q = b2
    generalize (v.machine.rule st.q (gdisp wD p v.tapeCount)).isSome = b3
    generalize readTapeBit st.tape st.head = b4
    generalize gdisp wD p v.tapeCount i = b5
    by_cases hr : st.head < r <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [hr]
  have fq : σ10.val rQ = (passStep v.machine r i st (gdisp wD p v.tapeCount)).q.val := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh,
      hN, passStep]
  have fsim : σ10.st sSIM = (passStep v.machine r i st (gdisp wD p v.tapeCount)).tape := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh,
      hE.sim, hE.simh, hW0, hW1, passStep]
    unfold replayWrite
    rcases hw : (decodedAction v.machine st.q (gdisp wD p v.tapeCount)).write i with _ | _ | _ <;>
      simp [writeCode, readTapeBit]
  have fh : σ10.val rH = (passStep v.machine r i st (gdisp wD p v.tapeCount)).head := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh,
      hE.h, hW2, hW3, passStep, moveCode_apply]
  have fsh2 : σ10.sh sSIM = (passStep v.machine r i st (gdisp wD p v.tapeCount)).head := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh,
      hE.simh, hW2, hW3, passStep, moveCode_apply]
  have frh : σ10.sh sRS = (passStep v.machine r i st (gdisp wD p v.tapeCount)).head := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.code, hE.codeh,
      hE.rsh, hW2, hW3, passStep, moveCode_apply]
  have hcost : (v.tapeCount * (57 * 2 ^ v.tapeCount + 65) + 7 * v.tapeCount + 3 + 16 * v.tapeCount + 3 +
      3 * 2 ^ v.tapeCount + 10) + 1 + ((110 * (σ1.val rHB + σ1.val rQ) + 60) + 1 +
      ((60 * (entryOff σ2 + σ2.val rQ + σ2.val rMK) + 60) + 1 +
      ((cWd v * (32 * (σ3.val rOFF + cWd v) + 60 * 2 ^ cWd v + 48) + 7 * cWd v + 3 * 2 ^ cWd v + 10) + 1 +
      ((200 * σ4.val rOFF + 600 * σ4.val rI + 300) + 1 + ((32 * σ5.val rI + 40) + 1 + (3 + 1 + (8 + 1 +
      (23 + 1 + (3 * σ9.val rQ + 7 * σ9.val rQN + 3 * σ9.val rMK + 6))))))))) ≤ stepCost v := by
    have hew : cEw v = 1 + cWd v + 4 * v.tapeCount := rfl
    unfold stepCost
    simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply, entryOff, hE.hb, hE.q, hE.tbl, hE.bs, hE.ew, hE.ii, hE.zMK, hE.zOFF,
      hE.zQN, hE.code, hE.codeh]
    have p1 : v.tapeCount * (57 * 2 ^ v.tapeCount + 65) ≤
        (code v).length * (57 * (code v).length + 65) := Nat.mul_le_mul b3 (by omega)
    have p2 : cWd v * (32 * (cAt v + ↑st.q * cBs v + mkA wD p v.tapeCount * cEw v + 1 + cWd v) +
        60 * 2 ^ cWd v + 48) ≤ (code v).length * (152 * (code v).length + 48) :=
      Nat.mul_le_mul b4 (by omega)
    have p3 : (code v).length * (57 * (code v).length + 65) =
        57 * ((code v).length * (code v).length) + 65 * (code v).length := by ring
    have p4 : (code v).length * (152 * (code v).length + 48) =
        152 * ((code v).length * (code v).length) + 48 * (code v).length := by ring
    have p5 : 3000 * ((code v).length + 1) ^ 2 =
        3000 * ((code v).length * (code v).length) + 6000 * (code v).length + 3000 := by ring
    lomega
  refine ⟨σ10, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 e10))))))))).mono hcost, ?_, ?_, ?_, hF⟩
  · exact {
      code := (by rw [fs _ (by decide)]; exact hE.code),
      codeh := (by rw [fsh _ (by decide)]; exact hE.codeh),
      t := (by rw [fv _ (by decide)]; exact hE.t),
      wd := (by rw [fv _ (by decide)]; exact hE.wd),
      ew := (by rw [fv _ (by decide)]; exact hE.ew),
      hb := (by rw [fv _ (by decide)]; exact hE.hb),
      tbl := (by rw [fv _ (by decide)]; exact hE.tbl),
      bs := (by rw [fv _ (by decide)]; exact hE.bs),
      ii := (by rw [fv _ (by decide)]; exact hE.ii),
      ok := fok, q := fq, h := fh, sim := fsim, simh := fsh2, rsh := frh,
      rs := (by simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, hE.rs]),
      wit := (by simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, hE.wit]),
      disph := (by simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, hE.disph]),
      zQN := (by simp [h10, Function.update_apply]),
      zMK := (by simp [h10, Function.update_apply]),
      zP := (by rw [fv _ (by decide)]; exact hE.zP),
      zOFF := (by simp [h10, h9, h8, h7, h6, h5, Function.update_apply]),
      zBIT := (by rw [fv _ (by decide)]; exact hE.zBIT),
      zTA := (by rw [fv _ (by decide)]; exact hE.zTA),
      zTB := (by rw [fv _ (by decide)]; exact hE.zTB),
      zTC := (by rw [fv _ (by decide)]; exact hE.zTC),
      zPT := (by rw [fv _ (by decide)]; exact hE.zPT),
      zW0 := (by simp [h10, h9, Function.update_apply]),
      zW1 := (by simp [h10, h9, Function.update_apply]),
      zM0 := (by simp [h10, h9, Function.update_apply]),
      zM1 := (by simp [h10, h9, Function.update_apply]),
      zDI := (by rw [fv _ (by decide)]; exact hE.zDI),
      zA2 := (by rw [fv _ (by decide)]; exact hE.zA2) }
  · simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
  · simp [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, Function.update_apply]

end NearCubicGates.Adapters.Refuter.Mach
