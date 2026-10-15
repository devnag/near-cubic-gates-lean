import Proof.Gates.Codec.FieldNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A counted loop -/

/-- Run `body` while `C ≠ 0`, decrementing `C` first. -/
def repLoop (C : Fin nr) (body : WM ns nr) : WM ns nr := .whr C (.seq (.dec C) body)

/-- `m` iterations along a family of states `g 0, …, g m` (`C = m − i` at `g i`; the body takes `g i` with `C`
decremented to `g (i + 1)`). -/
theorem repLoop_spec (C : Fin nr) (body : WM ns nr) (m c : ℕ) (g : ℕ → WState ns nr)
    (hC : ∀ i ≤ m, (g i).val C = m - i) (hcap : m ≤ cap)
    (hbody : ∀ i < m, WExec cap body ((g i).setv C (m - i - 1)) (g (i + 1)) c) :
    WExec cap (repLoop C body) (g 0) (g m) (m * (c + 4) + 1) := by
  suffices h : ∀ k, k ≤ m → WExec cap (repLoop C body) (g (m - k)) (g m) (k * (c + 4) + 1) by
    simpa using h m le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    have h := WExec.whrF (cap := cap) (P := .seq (.dec C) body) (σ := g m) (by rw [hC m le_rfl]; simp)
    simpa [repLoop] using h
  | succ k ih =>
    intro hk
    have hi : m - (k + 1) < m := by omega
    have hval := hC (m - (k + 1)) (by omega)
    have e1 := WExec.dec (cap := cap) C (g (m - (k + 1))) (by rw [hval]; omega)
    have hd : (g (m - (k + 1))).val C - 1 = m - (m - (k + 1)) - 1 := by rw [hval]
    rw [hd] at e1
    have e2 := hbody (m - (k + 1)) hi
    have hidx : m - (k + 1) + 1 = m - k := by omega
    rw [hidx] at e2
    refine WExec.mono (WExec.whrT (by rw [hval]; omega) (WExec.seq e1 e2) (ih (by omega))) ?_
    have : (k + 1) * (c + 4) = k * (c + 4) + c + 4 := by ring
    omega

/-! ## The integer transcoder -/

theorem natWord_one : natWord 1 = [true, false, true] := by decide

/-- `F := F + [scanned bit]`, then step. -/
def readSign (W : Fin (ns + 1)) (F : Fin nr) : WM ns nr := .seq (.ifs W (.inc F) .skip) (.fwd W)

theorem readSign_spec (W : Fin (ns + 1)) (F : Fin nr) (σ : WState ns nr) (hF : σ.val F = 0) (hcap : 1 ≤ cap) :
    WExec cap (readSign W F) σ ((σ.setv F (if wbit σ W then 1 else 0)).seth W (σ.sh W + 1)) 6 := by
  rcases hb : wbit σ W with _ | _
  · have e1 : WExec cap (.ifs W (.inc F) .skip) σ σ 1 := WExec.ifsF hb (WExec.skip σ)
    refine WExec.cast cap (WExec.seq e1 (WExec.fwd W σ)) ?_ (by omega)
    apply WState.eq <;> simp [← hF]
  · have e1 : WExec cap (.ifs W (.inc F) .skip) σ (σ.setv F 1) 4 := by
      have := WExec.ifsT (Q := .skip) hb (WExec.inc (cap := cap) F σ (by omega))
      rwa [hF] at this
    refine WExec.cast cap (WExec.seq e1 (WExec.fwd W (σ.setv F 1))) ?_ (by omega)
    apply WState.eq <;> simp

/-- Append `marks (natWord [F ≠ 0 ∧ T ≠ 0])`, then `F := 0`. -/
def signEmit (F T : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.ifr F (.ifr T (emitMarks o OP (natWord 1)) (emitMarks o OP (natWord 0))) (emitMarks o OP (natWord 0)))
    (WM.clear F)

theorem signEmit_spec (F T : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) (hFO : F ≠ OP) (σ : WState ns nr)
    (hF : σ.val F ≤ 1) (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 6 ≤ cap) :
    WExec cap (signEmit F T o OP) σ
      ((appendO σ o OP (marks (natWord (if σ.val F ≠ 0 ∧ σ.val T ≠ 0 then 1 else 0)))).setv F 0) 60 := by
  have hc' : ∀ v, v ≤ 1 → σ.val OP + 2 * (natWord v).length ≤ cap := by
    intro v hv; interval_cases v <;> simp [natWord_zero, natWord_one] <;> omega
  have hclr : ∀ τ : WState ns nr, τ.val F = σ.val F → τ.val F ≤ cap →
      WExec cap (WM.clear F) τ (τ.setv F 0) 4 := by
    intro τ hτ hτc
    exact WExec.mono (wclear_spec cap F (τ.val F) τ rfl hτc) (by omega)
  by_cases hF0 : σ.val F = 0
  · have e1 := emitMarks_spec cap o OP (natWord 0) σ ho (hc' 0 (by omega))
    have e := WExec.ifrF (P := .ifr T (emitMarks o OP (natWord 1)) (emitMarks o OP (natWord 0))) hF0 e1
    have e2 := hclr (appendO σ o OP (marks (natWord 0))) (by simp [appendO, Function.update_apply, hFO])
      (by simp [appendO, Function.update_apply, hFO]; omega)
    refine WExec.cast cap (WExec.seq e e2) (by simp [hF0]) ?_
    simp [natWord_zero]
  · by_cases hT0 : σ.val T = 0
    · have e1 := emitMarks_spec cap o OP (natWord 0) σ ho (hc' 0 (by omega))
      have e := WExec.ifrT (Q := emitMarks o OP (natWord 0)) hF0
        (WExec.ifrF (P := emitMarks o OP (natWord 1)) hT0 e1)
      have e2 := hclr (appendO σ o OP (marks (natWord 0))) (by simp [appendO, Function.update_apply, hFO])
        (by simp [appendO, Function.update_apply, hFO]; omega)
      refine WExec.cast cap (WExec.seq e e2) (by simp [hT0]) ?_
      simp [natWord_zero]
    · have e1 := emitMarks_spec cap o OP (natWord 1) σ ho (hc' 1 le_rfl)
      have e := WExec.ifrT (Q := emitMarks o OP (natWord 0)) hF0
        (WExec.ifrT (Q := emitMarks o OP (natWord 0)) hT0 e1)
      have e2 := hclr (appendO σ o OP (marks (natWord 1))) (by simp [appendO, Function.update_apply, hFO])
        (by simp [appendO, Function.update_apply, hFO]; omega)
      refine WExec.cast cap (WExec.seq e e2) (by simp [hF0, hT0]) ?_
      simp [natWord_one]

theorem value_ne_zero_iff (b : List Bool) : value b ≠ 0 ↔ tz b < b.length := by
  constructor
  · intro h
    by_contra hn
    exact h (value_of_tz b (le_antisymm (tz_le b) (by omega)))
  · intro h
    have hlo := two_pow_le_value _ (getLast_take_tz b h)
    rw [← value_take_tz] at hlo
    exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le Nat.one_le_two_pow hlo)

/-- **The integer transcoder**: sign bit and number field, appended as `marks (Interfaces.intWord z)`. -/
def intW (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (F OP : Fin nr) : WM ns nr :=
  .seq (readSign W F) (.seq (numScan W X) (.seq (signEmit F (X 1) o OP) (numEmit W o X OP)))

/-- The end of an integer field at `p`. -/
def intEnd (w : List Bool) (p : ℕ) : ℕ := p + 1 + fieldLen w (p + 1) + 1 + fieldLen w (p + 1)

theorem readInt_drop (w : List Bool) (p : ℕ) :
    readInt (w.drop p) = (if w.getD p false then -((value (fieldBits w (p + 1 + fieldLen w (p + 1) + 1)
      (fieldLen w (p + 1))) : ℕ) : ℤ) else ((value (fieldBits w (p + 1 + fieldLen w (p + 1) + 1)
      (fieldLen w (p + 1))) : ℕ) : ℤ), w.drop (intEnd w p)) := by
  unfold readInt intEnd
  rw [headD_drop, ← drop_succ_tail, readNum_drop]

theorem intW_spec (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (F OP : Fin nr) (hWo : W ≠ o) (hOP : ∀ i, X i ≠ OP)
    (hFX : ∀ i, X i ≠ F) (hFO : F ≠ OP) (σ : WState ns nr) (hX : ∀ i, σ.val (X i) = 0) (hF : σ.val F = 0)
    (ho : σ.sh o = (σ.st o).length) (hcap : fieldLen (σ.st W) (σ.sh W + 1) + 1 ≤ cap)
    (hOc : σ.val OP + 4 * fieldLen (σ.st W) (σ.sh W + 1) + 12 ≤ cap) :
    WExec cap (intW W o X F OP) σ
      (appendO (σ.seth W (intEnd (σ.st W) (σ.sh W))) o OP
        (marks (Interfaces.intWord (readInt ((σ.st W).drop (σ.sh W))).1)))
      (3 * fieldLen (σ.st W) (σ.sh W + 1) ^ 2 + 100 * fieldLen (σ.st W) (σ.sh W + 1) + 150) := by
  set w := σ.st W with hw
  set p := σ.sh W with hp
  set ℓ := fieldLen w (p + 1) with hℓ
  set b := fieldBits w (p + 1 + ℓ + 1) ℓ with hb
  set sg : ℕ := if wbit σ W then 1 else 0 with hsg
  have hbl : b.length = ℓ := fieldBits_length _ _ _
  -- the sign
  have e1 := readSign_spec cap W F σ hF (by omega)
  set σ1 := (σ.setv F sg).seth W (p + 1) with hσ1
  have h1X : ∀ i, σ1.val (X i) = 0 := fun i => by simp [hσ1, Function.update_of_ne (hFX i), hX]
  have h1W : σ1.st W = w := by simp [hσ1, hw]
  have h1p : σ1.sh W = p + 1 := by simp [hσ1]
  -- the scan
  have e2 := numScan_spec cap W X σ1 h1X (by rw [h1W, h1p]; omega)
  rw [h1W, h1p, ← hℓ, ← hb] at e2
  set σ2 := ((σ1.seth W (p + 1 + ℓ + 1)).setv (X 1) (ℓ - tz b)).setv (X 4) (tz b) with hσ2
  have h2F : σ2.val F = sg := by
    simp [hσ2, hσ1, Function.update_apply, Ne.symm (hFX 1), Ne.symm (hFX 4)]
  have h2T : σ2.val (X 1) = ℓ - tz b := by
    simp [hσ2, Function.update_of_ne (Xne X (show (1 : Fin 5) ≠ 4 by decide))]

  have e3 := signEmit_spec cap F (X 1) o OP hFO σ2 (by rw [h2F, hsg]; split_ifs <;> omega)
    (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hWo, ho])
    (by simp [hσ2, hσ1, Function.update_apply, Ne.symm (hOP 1), Ne.symm (hOP 4), hFO.symm]; omega)
  rw [h2F, h2T] at e3
  set sgn : ℕ := if sg ≠ 0 ∧ ℓ - tz b ≠ 0 then 1 else 0 with hsgn
  set σ3 := (appendO σ2 o OP (marks (natWord sgn))).setv F 0 with hσ3
  have h3W : σ3.st W = w := by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hWo, hw]
  have h3p : σ3.sh W = p + 1 + ℓ + 1 := by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hWo]
  have hsgn1 : (natWord sgn).length ≤ 3 := by rw [hsgn]; split_ifs <;> simp [natWord_zero, natWord_one]
  have hsgnb : natBitLength sgn = 1 := by rw [hsgn]; split_ifs <;> decide
  -- the magnitude
  have e4 := numEmit_spec cap W o X OP hWo hOP σ3 ℓ
    (by simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hFX 0, hOP 0, Xne X (show (0 : Fin 5) ≠ 1 by decide),
      Xne X (show (0 : Fin 5) ≠ 4 by decide), hX])
    (by simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hFX 2, hOP 2, Xne X (show (2 : Fin 5) ≠ 1 by decide),
      Xne X (show (2 : Fin 5) ≠ 4 by decide), hX])
    (by simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hFX 3, hOP 3, Xne X (show (3 : Fin 5) ≠ 1 by decide),
      Xne X (show (3 : Fin 5) ≠ 4 by decide), hX])
    (by rw [h3W, h3p, ← hb]; simp [hσ3, hσ2, appendO, Function.update_apply, hFX 1, hOP 1,
      Xne X (show (1 : Fin 5) ≠ 4 by decide)])
    (by rw [h3W, h3p, ← hb]; simp [hσ3, hσ2, appendO, Function.update_apply, hFX 4, hOP 4])
    (by simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, Ne.symm hWo, ho])
    hcap
    (by simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hFO.symm, Ne.symm (hOP 1), Ne.symm (hOP 4),
      marks_length]; omega)
  rw [h3W, h3p, ← hb] at e4
  -- the integer
  have hread := readInt_drop w p
  rw [← hℓ, ← hb] at hread
  have hint : Interfaces.intWord (readInt (w.drop p)).1 = natWord sgn ++ natWord (value b) := by
    rw [hread]
    have hbit : wbit σ W = w.getD p false := rfl
    have hv := value_ne_zero_iff b
    rw [hbl] at hv
    unfold Interfaces.intWord
    rcases hs : w.getD p false with _ | _
    · have hsg0 : sg = 0 := by rw [hsg, hbit, hs]; rfl
      have h0 : sgn = 0 := by rw [hsgn, hsg0]; simp
      rw [h0]; simp
    · have hsg1 : sg = 1 := by rw [hsg, hbit, hs]; rfl
      by_cases hz : value b = 0
      · have hn : ¬ tz b < ℓ := fun h => hv.2 h hz
        have h0 : sgn = 0 := by rw [hsgn, hsg1]; simp; omega
        rw [h0, hz]; simp
      · have hn : tz b < ℓ := hv.1 hz
        have h1 : sgn = 1 := by rw [hsgn, hsg1]; simp; omega
        rw [h1]
        have hpos : 0 < value b := Nat.pos_of_ne_zero hz
        simp [hpos]
  rw [hint]
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  have hm : marks (natWord sgn ++ natWord (value b)) = marks (natWord sgn) ++ marks (natWord (value b)) := marksApp _ _
  rw [hm, ← appendO_append]
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [hσ3, hσ2, hσ1, appendO, hWo, intEnd, ← hℓ]
    · by_cases hjo : j = o
      · subst hjo; simp [hσ3, hσ2, hσ1, appendO, hj, Ne.symm hWo]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ3, hσ2, hσ1, appendO]
    · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hjo]
  · funext r
    simp only [hσ3, hσ2, hσ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases hr : r = OP
    · simp [hr, hFO.symm, Ne.symm (hOP 1), Ne.symm (hOP 4)]
    by_cases hrF : r = F
    · simp [hr, hrF, hFX 1, hFX 4, Ne.symm (hFX 1), Ne.symm (hFX 4), hF, hFO]
    by_cases hr4 : r = X 4
    · simp [hr, hrF, hr4, Xne X (show (4 : Fin 5) ≠ 1 by decide), hX, hOP 4, hFX 4]
    by_cases hr1 : r = X 1
    · simp [hr, hrF, hr4, hr1, hX, hOP 1, hFX 1, Xne X (show (1 : Fin 5) ≠ 4 by decide)]
    · simp [hr, hrF, hr4, hr1]
  · simp [hσ3, hσ2, hσ1]

end NearCubicGates.Close.Codec
