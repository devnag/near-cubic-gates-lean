import SourceAdapters.Refuter.CheckerLayout

/-!
# The segments of one checking step (input 7, F01 machine layer, part 5)

One guessed step of pass `i` (SFM78 l.222–230; proof of `lem:multitape-refuter`): after the display is read
(`dispLoop`), the machine

* `haltChk`: clears the flag if the current control is halted (table read at `hb + 2q`);
* `entry`: clears the flag if the table entry at `(q, MK)` is not an action (`at + q·bs + MK·ew`);
* `nextCtl`: reads the `wd` bits of the entry's next control into `QN`;
* `actBits`: reads tape `i`'s write and move codes into `W0 W1 M0 M1`;
* `replayChk`: clears the flag unless the head is before the cutoff (`RS`) and the work tape's cell
  equals display bit `i`;
* `replayWr`, `replayMv`: apply the write and the move to the work tape (and the cutoff stream);
* `finish`: `Q := QN`, scratch cleared.

Each segment has an exact-state specification. Every read of the code stream is a `peek` at an
offset computed in registers; the costs are linear in the offsets, i.e. `O(|code(M)|)` per read.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

@[simp] theorem toNat_ne_zero_iff (b : Bool) : b.toNat ≠ 0 ↔ b = true := by cases b <;> simp

@[simp] theorem toNat_eq_zero_iff (b : Bool) : b.toNat = 0 ↔ b = false := by cases b <;> simp

/-! ## Halted check -/

def haltChk : Pg :=
  .seq (addR rHB rOFF rTA) (.seq (addR rQ rOFF rTA) (.seq (addR rQ rOFF rTA)
  (.seq (peek sCODE rOFF rTB rBIT) (.seq (ifClr rBIT rOK) (.seq (clr rBIT) (clr rOFF))))))

theorem haltChk_spec (σ : St) (hOFF : σ.val rOFF = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0)
    (hBIT : σ.val rBIT = 0) (hOK : σ.val rOK ≤ 1) (hcap : 4 * (σ.val rHB + 2 * σ.val rQ) + 4 ≤ cap) :
    WXExec cap haltChk σ
      (σ.setv rOK (if readTapeBit (σ.st sCODE) (σ.sh sCODE + (σ.val rHB + 2 * σ.val rQ)) then 0
        else σ.val rOK))
      (110 * (σ.val rHB + σ.val rQ) + 60) := by
  have e1 := addR_spec cap (A := rHB) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by lomega)
  set σ1 := σ.setv rOFF (σ.val rOFF + σ.val rHB) with hσ1
  have e2 := addR_spec cap (A := rQ) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ1
    (by simp [σ1, Function.update_apply, hTA]) (by simp [σ1, Function.update_apply]; lomega)
  set σ2 := σ1.setv rOFF (σ1.val rOFF + σ1.val rQ) with hσ2
  have e3 := addR_spec cap (A := rQ) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ2
    (by simp [σ2, σ1, Function.update_apply, hTA]) (by simp [σ2, σ1, Function.update_apply]; lomega)
  set σ3 := σ2.setv rOFF (σ2.val rOFF + σ2.val rQ) with hσ3
  have e4 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rBIT) (by decide) (by decide)
    (by decide) σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ3, σ2, σ1, Function.update_apply]; lomega) (by simp [σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ4 := σ3.setv rBIT (σ3.val rBIT + (readTapeBit (σ3.st sCODE) (σ3.sh sCODE + σ3.val rOFF)).toNat)
    with hσ4
  have e5 := ifClr_spec cap rBIT rOK σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by lomega)
  set σ5 := σ4.setv rOK (if σ4.val rBIT ≠ 0 then 0 else σ4.val rOK) with hσ5
  have e6 := clr_spec cap rBIT σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ6 := σ5.setv rBIT 0 with hσ6
  have e7 := clr_spec cap rOFF σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 e7)))))).cast cap ?_ (by
      simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  simp only [σ6, σ5, σ4, σ3, σ2, σ1]
  rw [show σ.val rHB + 2 * σ.val rQ = σ.val rHB + σ.val rQ + σ.val rQ by ring]
  wsta

/-! ## The table entry -/

def entry : Pg :=
  .seq (addR rAT rOFF rTA) (.seq (mulR rQ rA2 rBS rOFF rTA) (.seq (mulR rMK rA2 rEW rOFF rTA)
  (.seq (peek sCODE rOFF rTB rBIT) (.seq (ifNotClr rBIT rOK) (.seq (clr rBIT) (WMX.inc rOFF))))))

/-- The offset of the entry at `(Q, MK)`. -/
def entryOff (σ : St) : ℕ := σ.val rAT + σ.val rQ * σ.val rBS + σ.val rMK * σ.val rEW

theorem entry_spec (σ : St) (hOFF : σ.val rOFF = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0)
    (hBIT : σ.val rBIT = 0) (hA2 : σ.val rA2 = 0) (hOK : σ.val rOK ≤ 1)
    (hcap : 4 * (entryOff σ + σ.val rQ + σ.val rMK) + 4 ≤ cap) :
    WXExec cap entry σ
      ((σ.setv rOK (if readTapeBit (σ.st sCODE) (σ.sh sCODE + entryOff σ) then σ.val rOK else 0)).setv
        rOFF (entryOff σ + 1))
      (60 * (entryOff σ + σ.val rQ + σ.val rMK) + 60) := by
  unfold entryOff at hcap ⊢
  have e1 := addR_spec cap (A := rAT) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by lomega)
  set σ1 := σ.setv rOFF (σ.val rOFF + σ.val rAT) with hσ1
  have e2 := mulR_spec cap (A := rQ) (A2 := rA2) (B := rBS) (C := rOFF) (T := rTA) (by decide) σ1
    (by simp [σ1, Function.update_apply, hA2]) (by simp [σ1, Function.update_apply, hTA])
    (by simp [σ1, Function.update_apply]; lomega) (by simp [σ1, Function.update_apply]; lomega)
  set σ2 := σ1.setv rOFF (σ1.val rOFF + σ1.val rQ * σ1.val rBS) with hσ2
  have e3 := mulR_spec cap (A := rMK) (A2 := rA2) (B := rEW) (C := rOFF) (T := rTA) (by decide) σ2
    (by simp [σ2, σ1, Function.update_apply, hA2]) (by simp [σ2, σ1, Function.update_apply, hTA])
    (by simp [σ2, σ1, Function.update_apply]; lomega) (by simp [σ2, σ1, Function.update_apply]; lomega)
  set σ3 := σ2.setv rOFF (σ2.val rOFF + σ2.val rMK * σ2.val rEW) with hσ3
  have e4 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rBIT) (by decide) (by decide)
    (by decide) σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ3, σ2, σ1, Function.update_apply]; lomega) (by simp [σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ4 := σ3.setv rBIT (σ3.val rBIT + (readTapeBit (σ3.st sCODE) (σ3.sh sCODE + σ3.val rOFF)).toNat)
    with hσ4
  have e5 := ifNotClr_spec cap rBIT rOK σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by lomega)
  set σ5 := σ4.setv rOK (if σ4.val rBIT = 0 then 0 else σ4.val rOK) with hσ5
  have e6 := clr_spec cap rBIT σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ6 := σ5.setv rBIT 0 with hσ6
  have e7 := WXExec.inc cap rOFF σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 e7)))))).cast cap ?_ (by
      simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]
      ring_nf; ring_nf at hcap; lomega)
  simp only [σ6, σ5, σ4, σ3, σ2, σ1]
  wsta

/-! ## The next control -/

/-- Bits `o, o+1, …` of a list accumulated least significant first. -/
def accBits (c : List Bool) (o : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => accBits c o k + if readTapeBit c (o + k) then 2 ^ k else 0

theorem accBits_eq (c : List Bool) (o : ℕ) :
    ∀ w, accBits c o w = maskL (List.ofFn fun j : Fin w => readTapeBit c (o + j.val))
  | 0 => rfl
  | w + 1 => by
    rw [List.ofFn_succ', List.concat_eq_append, maskL_append_single, accBits, accBits_eq c o w]
    simp

theorem accBits_lt (c : List Bool) (o w : ℕ) : accBits c o w < 2 ^ w := by
  rw [accBits_eq]
  have := maskL_lt (List.ofFn fun j : Fin w => readTapeBit c (o + j.val))
  simpa using this

def nextBit : Pg :=
  .seq (peek sCODE rOFF rTB rBIT) (.seq (.ifr rBIT (addR rP rQN rTA) WMX.skip)
  (.seq (clr rBIT) (.seq (WMX.inc rOFF) (dbl rP rPT rTA))))

theorem nextBit_spec (σ : St) (hBIT : σ.val rBIT = 0) (hPT : σ.val rPT = 0) (hTA : σ.val rTA = 0)
    (hTB : σ.val rTB = 0) (hcap : 4 * (σ.val rQN + σ.val rP + σ.val rOFF) + 4 ≤ cap) :
    WXExec cap nextBit σ
      (((σ.setv rQN (σ.val rQN + if readTapeBit (σ.st sCODE) (σ.sh sCODE + σ.val rOFF) then σ.val rP
        else 0)).setv rP (2 * σ.val rP)).setv rOFF (σ.val rOFF + 1))
      (32 * σ.val rOFF + 60 * σ.val rP + 40) := by
  have e1 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rBIT) (by decide) (by decide)
    (by decide) σ hTB (by lomega) (by lomega)
  set σ1 := σ.setv rBIT (σ.val rBIT + (readTapeBit (σ.st sCODE) (σ.sh sCODE + σ.val rOFF)).toNat)
    with hσ1
  cases hc : readTapeBit (σ.st sCODE) (σ.sh sCODE + σ.val rOFF)
  · have hb : σ1.val rBIT = 0 := by simp [σ1, hBIT, hc, Function.update_apply]
    have e2 : WXExec cap (.ifr rBIT (addR rP rQN rTA) WMX.skip) σ1 σ1 1 :=
      WXExec.ifrF hb (WXExec.skip cap σ1)
    have e3 := clr_spec cap rBIT σ1 (by rw [hb]; lomega)
    set σ3 := σ1.setv rBIT 0 with hσ3
    have e4 := WXExec.inc cap rOFF σ3 (by simp [σ3, σ1, Function.update_apply]; lomega)
    set σ4 := σ3.setv rOFF (σ3.val rOFF + 1) with hσ4
    have e5 := dbl_spec cap (P := rP) (PT := rPT) (TA := rTA) (by decide) (by decide) (by decide) σ4
      (by simp [σ4, σ3, σ1, Function.update_apply, hPT]) (by simp [σ4, σ3, σ1, Function.update_apply, hTA])
      (by simp [σ4, σ3, σ1, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_
      (by simp [σ4, σ3, σ1, Function.update_apply, hb]; lomega)
    simp only [σ4, σ3, σ1]
    wst
  · have hb : σ1.val rBIT = 1 := by simp [σ1, hBIT, hc, Function.update_apply]
    have ea := addR_spec cap (A := rP) (B := rQN) (T := rTA) (by decide) (by decide) (by decide) σ1
      (by simp [σ1, Function.update_apply, hTA]) (by simp [σ1, Function.update_apply]; lomega)
    have e2 : WXExec cap (.ifr rBIT (addR rP rQN rTA) WMX.skip) σ1
        (σ1.setv rQN (σ1.val rQN + σ1.val rP)) (18 * σ1.val rP + 4) :=
      WXExec.ifrT (by rw [hb]; lomega) ea
    set σ2 := σ1.setv rQN (σ1.val rQN + σ1.val rP) with hσ2
    have e3 := clr_spec cap rBIT σ2 (by simp [σ2, σ1, Function.update_apply, hBIT, hc]; lomega)
    set σ3 := σ2.setv rBIT 0 with hσ3
    have e4 := WXExec.inc cap rOFF σ3 (by simp [σ3, σ2, σ1, Function.update_apply]; lomega)
    set σ4 := σ3.setv rOFF (σ3.val rOFF + 1) with hσ4
    have e5 := dbl_spec cap (P := rP) (PT := rPT) (TA := rTA) (by decide) (by decide) (by decide) σ4
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hPT])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hTA])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hBIT, hc]; lomega)
    simp only [σ4, σ3, σ2, σ1]
    wst

def nextCtl : Pg := .seq (WMX.inc rP) (.seq (repK rWD rTC nextBit) (clr rP))

theorem nextCtl_spec (σ : St) (w : ℕ) (hWD : σ.val rWD = w) (hBIT : σ.val rBIT = 0)
    (hPT : σ.val rPT = 0) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0) (hQN : σ.val rQN = 0)
    (hP : σ.val rP = 0) (hTC : σ.val rTC = 0)
    (hcap : 8 * 2 ^ w + 4 * (σ.val rOFF + w) + 2 * w + 8 ≤ cap) :
    WXExec cap nextCtl σ
      ((σ.setv rQN (accBits (σ.st sCODE) (σ.sh sCODE + σ.val rOFF) w)).setv rOFF (σ.val rOFF + w))
      (w * (32 * (σ.val rOFF + w) + 60 * 2 ^ w + 48) + 7 * w + 3 * 2 ^ w + 10) := by
  have e1 := WXExec.inc cap rP σ (by rw [hP]; lomega)
  set σ1 := σ.setv rP (σ.val rP + 1) with hσ1
  let st : ℕ → St := fun k =>
    ((σ1.setv rQN (accBits (σ.st sCODE) (σ.sh sCODE + σ.val rOFF) k)).setv rP (2 ^ k)).setv rOFF
      (σ.val rOFF + k)
  have hst0 : st 0 = σ1 := by
    simp only [st, σ1, accBits, pow_zero, Nat.add_zero]
    wst
  have hloop := Runs.repE (cap := cap) (K := rWD) (K2 := rTC) (body := nextBit) (by decide)
    (32 * (σ.val rOFF + w) + 60 * 2 ^ w + 40) w st (by lomega)
    (fun k => by simp [st, Function.update_apply]) (fun k => by simp [st, Function.update_apply])
    (fun k hk v1 v2 => by
      have h2 : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hk.le
      have hb := nextBit_spec cap (((st k).setv rWD v1).setv rTC v2)
        (by simp [st, σ1, Function.update_apply, hBIT]) (by simp [st, σ1, Function.update_apply, hPT])
        (by simp [st, σ1, Function.update_apply, hTA]) (by simp [st, σ1, Function.update_apply, hTB])
        (by
          simp [st, Function.update_apply]
          have := accBits_lt (σ.st sCODE) (σ.sh sCODE + σ.val rOFF) k
          lomega)
      refine hb.cast cap ?_ (by simp [st, Function.update_apply]; lomega)
      simp only [st, σ1, accBits, pow_succ]
      wsta)
    (by simp [st, σ1, Function.update_apply, hWD]) (by simp [st, σ1, Function.update_apply, hTC])
  rw [hst0] at hloop
  have e3 := clr_spec cap rP (st w) (by simp [st, Function.update_apply]; lomega)
  have hm : w * (32 * (σ.val rOFF + w) + 60 * 2 ^ w + 40 + 8) ≤
      w * (32 * (σ.val rOFF + w) + 60 * 2 ^ w + 48) := le_refl _
  refine (WXExec.seq e1 (WXExec.seq hloop e3)).cast cap ?_ (by
    simp [st, σ1, Function.update_apply, hP]; lomega)
  simp only [st, σ1]
  wsta

/-! ## Write and move codes of tape `i` -/

def actBits : Pg :=
  .seq (addR rI rOFF rTA) (.seq (addR rI rOFF rTA) (.seq (addR rI rOFF rTA) (.seq (addR rI rOFF rTA)
  (.seq (peek sCODE rOFF rTB rW0) (.seq (WMX.inc rOFF) (.seq (peek sCODE rOFF rTB rW1) (.seq (WMX.inc rOFF)
  (.seq (peek sCODE rOFF rTB rM0) (.seq (WMX.inc rOFF) (.seq (peek sCODE rOFF rTB rM1) (clr rOFF)))))))))))

theorem actBits_spec (σ : St) (hTA : σ.val rTA = 0) (hTB : σ.val rTB = 0) (hW0 : σ.val rW0 = 0)
    (hW1 : σ.val rW1 = 0) (hM0 : σ.val rM0 = 0) (hM1 : σ.val rM1 = 0)
    (hcap : 4 * (σ.val rOFF + 4 * σ.val rI) + 16 ≤ cap) :
    WXExec cap actBits σ
      (let o := σ.sh sCODE + (σ.val rOFF + 4 * σ.val rI)
       ((((σ.setv rW0 (readTapeBit (σ.st sCODE) o).toNat).setv rW1
        (readTapeBit (σ.st sCODE) (o + 1)).toNat).setv rM0 (readTapeBit (σ.st sCODE) (o + 2)).toNat).setv
          rM1 (readTapeBit (σ.st sCODE) (o + 3)).toNat).setv rOFF 0)
      (200 * σ.val rOFF + 600 * σ.val rI + 300) := by
  have e1 := addR_spec cap (A := rI) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by lomega)
  set σ1 := σ.setv rOFF (σ.val rOFF + σ.val rI) with hσ1
  have e2 := addR_spec cap (A := rI) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ1
    (by simp [σ1, Function.update_apply, hTA]) (by simp [σ1, Function.update_apply]; lomega)
  set σ2 := σ1.setv rOFF (σ1.val rOFF + σ1.val rI) with hσ2
  have e3 := addR_spec cap (A := rI) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ2
    (by simp [σ2, σ1, Function.update_apply, hTA]) (by simp [σ2, σ1, Function.update_apply]; lomega)
  set σ3 := σ2.setv rOFF (σ2.val rOFF + σ2.val rI) with hσ3
  have e4 := addR_spec cap (A := rI) (B := rOFF) (T := rTA) (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, Function.update_apply, hTA]) (by simp [σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ4 := σ3.setv rOFF (σ3.val rOFF + σ3.val rI) with hσ4
  have e5 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rW0) (by decide) (by decide)
    (by decide) σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by simp [σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ5 := σ4.setv rW0 (σ4.val rW0 + (readTapeBit (σ4.st sCODE) (σ4.sh sCODE + σ4.val rOFF)).toNat)
    with hσ5
  have e6 := WXExec.inc cap rOFF σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ6 := σ5.setv rOFF (σ5.val rOFF + 1) with hσ6
  have e7 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rW1) (by decide) (by decide)
    (by decide) σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ7 := σ6.setv rW1 (σ6.val rW1 + (readTapeBit (σ6.st sCODE) (σ6.sh sCODE + σ6.val rOFF)).toNat)
    with hσ7
  have e8 := WXExec.inc cap rOFF σ7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ8 := σ7.setv rOFF (σ7.val rOFF + 1) with hσ8
  have e9 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rM0) (by decide) (by decide)
    (by decide) σ8 (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ9 := σ8.setv rM0 (σ8.val rM0 + (readTapeBit (σ8.st sCODE) (σ8.sh sCODE + σ8.val rOFF)).toNat)
    with hσ9
  have e10 := WXExec.inc cap rOFF σ9
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ10 := σ9.setv rOFF (σ9.val rOFF + 1) with hσ10
  have e11 := peek_spec cap (S := sCODE) (K := rOFF) (K2 := rTB) (RES := rM1) (by decide) (by decide)
    (by decide) σ10 (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hTB])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  set σ11 := σ10.setv rM1
    (σ10.val rM1 + (readTapeBit (σ10.st sCODE) (σ10.sh sCODE + σ10.val rOFF)).toNat) with hσ11
  have e12 := clr_spec cap rOFF σ11
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11
      e12))))))))))).cast cap ?_ (by
        simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]; lomega)
  simp only [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  rw [show σ.val rOFF + 4 * σ.val rI = σ.val rOFF + σ.val rI + σ.val rI + σ.val rI + σ.val rI by ring]
  wsta

end NearCubicGates.Adapters.Refuter.Mach
