import Proof.Gates.Codec.Field

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

theorem Xne (X : Fin 5 ↪ Fin nr) {i j : Fin 5} (h : i ≠ j) : X i ≠ X j := X.injective.ne h

/-- The bits of the field at the stream position after its count. -/
def fieldBits (w : List Bool) (p1 ℓ : ℕ) : List Bool := List.ofFn fun j : Fin ℓ => w.getD (p1 + j.val) false

theorem fieldBits_length (w : List Bool) (p1 ℓ : ℕ) : (fieldBits w p1 ℓ).length = ℓ := by simp [fieldBits]

theorem fieldBits_take_succ (w : List Bool) (p1 ℓ i : ℕ) (hi : i < ℓ) :
    (fieldBits w p1 ℓ).take (i + 1) = (fieldBits w p1 ℓ).take i ++ [w.getD (p1 + i) false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [fieldBits_length]; exact hi)]
  simp [fieldBits]

/-! ## The scan -/

/-- The register file during the scan, after `i` of `ℓ` bits. -/
def scanSt (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (σ : WState ns nr) (ℓ i : ℕ) (b : List Bool) : WState ns nr :=
  ⟨Function.update σ.sh W (σ.sh W + i), σ.st,
    fun r => if r = X 0 then ℓ - i else if r = X 1 then i else if r = X 2 then i else
      if r = X 3 then tz (b.take i) else σ.val r, σ.cell⟩

/-- One scan step. -/
def scanBody (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (.dec (X 0)) (.seq (.inc (X 1)) (.seq (.inc (X 2)) (.seq (.ifs W (WM.clear (X 3)) (.inc (X 3))) (.fwd W))))

def scanLoop (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) : WM ns nr := .whr (X 0) (scanBody W X)

theorem scanLoop_spec (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (σ : WState ns nr) (ℓ : ℕ)
    (hcap : ℓ + 1 ≤ cap) :
    ∀ (m i : ℕ), i + m = ℓ →
      WExec cap (scanLoop W X) (scanSt W X σ ℓ i (fieldBits (σ.st W) (σ.sh W) ℓ))
        (scanSt W X σ ℓ ℓ (fieldBits (σ.st W) (σ.sh W) ℓ)) (m * (3 * ℓ + 20) + 1)
  | 0, i, hi => by
    subst hi
    refine WExec.mono (WExec.whrF ?_) (by omega)
    simp [scanSt]
  | m + 1, i, hi => by
    set b := fieldBits (σ.st W) (σ.sh W) ℓ with hb
    set σi := scanSt W X σ ℓ i b with hσi
    have hL : σi.val (X 0) = ℓ - i := by simp [hσi, scanSt]
    have hT : σi.val (X 1) = i := by simp [hσi, scanSt, Xne X (show (1 : Fin 5) ≠ 0 by decide)]
    have hU : σi.val (X 2) = i := by
      simp [hσi, scanSt, Xne X (show (2 : Fin 5) ≠ 0 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide)]
    have hZ : σi.val (X 3) = tz (b.take i) := by
      simp [hσi, scanSt, Xne X (show (3 : Fin 5) ≠ 0 by decide), Xne X (show (3 : Fin 5) ≠ 1 by decide),
        Xne X (show (3 : Fin 5) ≠ 2 by decide)]
    have hZle : tz (b.take i) ≤ i := (tz_le _).trans (by simp)
    -- the body, step by step
    set σ1 := σi.setv (X 0) (σi.val (X 0) - 1) with hσ1
    have e1 := WExec.dec (cap := cap) (X 0) σi (by rw [hL]; omega)
    set σ2 := σ1.setv (X 1) (σ1.val (X 1) + 1) with hσ2
    have e2 := WExec.inc (cap := cap) (X 1) σ1 (by
      simp [hσ1, wsetv_val_ne _ _ (Xne X (show (1 : Fin 5) ≠ 0 by decide)), hT]; omega)
    set σ3 := σ2.setv (X 2) (σ2.val (X 2) + 1) with hσ3
    have e3 := WExec.inc (cap := cap) (X 2) σ2 (by
      simp [hσ2, hσ1, Function.update_apply, Xne X (show (2 : Fin 5) ≠ 0 by decide),
        Xne X (show (2 : Fin 5) ≠ 1 by decide), hU]; omega)
    have hZ3 : σ3.val (X 3) = tz (b.take i) := by
      simp [hσ3, hσ2, hσ1, Function.update_apply, Xne X (show (3 : Fin 5) ≠ 0 by decide),
        Xne X (show (3 : Fin 5) ≠ 1 by decide), Xne X (show (3 : Fin 5) ≠ 2 by decide), hZ]
    have hbit : wbit σ3 W = (σ.st W).getD (σ.sh W + i) false := by
      simp [wbit, readTapeBit, hσ3, hσ2, hσ1, hσi, scanSt]
    have hbi : (σ.st W).getD (σ.sh W + i) false = b[i]'(by rw [hb, fieldBits_length]; omega) := by
      simp [hb, fieldBits]
    set σ4 := σ3.setv (X 3) (tz (b.take (i + 1))) with hσ4
    have e4 : WExec cap (.ifs W (WM.clear (X 3)) (.inc (X 3))) σ3 σ4 (3 * ℓ + 4) := by
      have htake := fieldBits_take_succ (σ.st W) (σ.sh W) ℓ i (by omega)
      rw [← hb] at htake
      rcases hc : (σ.st W).getD (σ.sh W + i) false with _ | _
      · have hz : tz (b.take (i + 1)) = σ3.val (X 3) + 1 := by rw [htake, hc, tz_append_false, hZ3]
        rw [hσ4, hz]
        exact WExec.mono (WExec.ifsF (by rw [hbit, hc]) (WExec.inc (X 3) σ3 (by rw [hZ3]; omega))) (by omega)
      · have hz : tz (b.take (i + 1)) = 0 := by rw [htake, hc, tz_append_true]
        rw [hσ4, hz]
        exact WExec.mono (WExec.ifsT (by rw [hbit, hc]) (wclear_spec cap (X 3) _ σ3 rfl (by rw [hZ3]; omega)))
          (by rw [hZ3]; omega)
    have e5 := WExec.fwd (cap := cap) W σ4
    have hbody : WExec cap (scanBody W X) σi (σ4.seth W (σ4.sh W + 1)) (3 * ℓ + 18) :=
      WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega)
    have hnext : σ4.seth W (σ4.sh W + 1) = scanSt W X σ ℓ (i + 1) b := by
      apply WState.eq
      · funext j; by_cases hj : j = W
        · subst hj; simp [hσ4, hσ3, hσ2, hσ1, hσi, scanSt]; omega
        · simp [hσ4, hσ3, hσ2, hσ1, hσi, scanSt, Function.update_of_ne hj]
      · simp [hσ4, hσ3, hσ2, hσ1, hσi, scanSt]
      · funext r
        simp only [hσ4, hσ3, hσ2, hσ1, hσi, scanSt, WState.seth_val, WState.setv_val, Function.update_apply]
        by_cases h0 : r = X 0
        · subst h0; simp [Xne X (show (0 : Fin 5) ≠ 1 by decide), Xne X (show (0 : Fin 5) ≠ 2 by decide),
            Xne X (show (0 : Fin 5) ≠ 3 by decide)]; omega
        by_cases h1 : r = X 1
        · subst h1; simp [Xne X (show (1 : Fin 5) ≠ 0 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide),
            Xne X (show (1 : Fin 5) ≠ 3 by decide)]
        by_cases h2 : r = X 2
        · subst h2; simp [Xne X (show (2 : Fin 5) ≠ 0 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide),
            Xne X (show (2 : Fin 5) ≠ 3 by decide)]
        by_cases h3 : r = X 3
        · subst h3; simp [Xne X (show (3 : Fin 5) ≠ 0 by decide), Xne X (show (3 : Fin 5) ≠ 1 by decide),
            Xne X (show (3 : Fin 5) ≠ 2 by decide)]
        simp [h0, h1, h2, h3]
      · simp [hσ4, hσ3, hσ2, hσ1, hσi, scanSt]
    rw [hnext] at hbody
    have hrest := scanLoop_spec W X σ ℓ hcap m (i + 1) (by omega)
    refine WExec.mono (WExec.whrT (by rw [hL]; omega) hbody hrest) ?_
    have : m * (3 * ℓ + 20) + (3 * ℓ + 20) = (m + 1) * (3 * ℓ + 20) := by ring
    omega

/-! ## Rewind, subtract, emit, skip -/

/-- `W` back by `U` cells, `U := 0`. -/
def rewindLoop (W : Fin (ns + 1)) (U : Fin nr) : WM ns nr := .whr U (.seq (.dec U) (.bwd W))

theorem rewindLoop_spec (W : Fin (ns + 1)) (U : Fin nr) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val U = m → m ≤ σ.sh W → m ≤ cap →
      WExec cap (rewindLoop W U) σ ((σ.setv U 0).seth W (σ.sh W - m)) (5 * m + 1)
  | 0, σ, h0, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases hr : r = U
      · subst hr; simp [h0]
      · simp [Function.update_of_ne hr]
    · simp
  | m + 1, σ, hm, hle, hc => by
    have e1 := WExec.dec (cap := cap) U σ (by omega)
    have e2 := WExec.bwd (cap := cap) W (σ.setv U (σ.val U - 1))
    have hrest := rewindLoop_spec W U m ((σ.setv U (σ.val U - 1)).seth W ((σ.setv U (σ.val U - 1)).sh W - 1))
      (by simp; omega) (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) hrest) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases hr : r = U
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    · simp

/-- `T := T − Z`, `S := S + Z`, `Z := 0`. -/
def subLoop (Z T S : Fin nr) : WM ns nr := .whr Z (.seq (.dec Z) (.seq (.dec T) (.inc S)))

theorem subLoop_spec (Z T S : Fin nr) (hZT : Z ≠ T) (hZS : Z ≠ S) (hTS : T ≠ S) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val Z = m → m ≤ σ.val T → σ.val T ≤ cap → m ≤ cap → σ.val S + m ≤ cap →
      WExec cap (subLoop Z T S) σ (((σ.setv Z 0).setv T (σ.val T - m)).setv S (σ.val S + m)) (9 * m + 1)
  | 0, σ, h0, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq
    · simp
    · simp
    · funext r
      by_cases hr : r = S
      · subst hr; simp
      by_cases hr' : r = T
      · subst hr'; simp [Function.update_of_ne hr]
      by_cases hr'' : r = Z
      · subst hr''; simp [Function.update_of_ne hr, Function.update_of_ne hr', h0]
      · simp [Function.update_of_ne hr, Function.update_of_ne hr', Function.update_of_ne hr'']
    · simp
  | m + 1, σ, hm, hle, hT, hc, hS => by
    have e1 := WExec.dec (cap := cap) Z σ (by omega)
    set σ1 := σ.setv Z (σ.val Z - 1) with hσ1
    have e2 := WExec.dec (cap := cap) T σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hZT)]; omega)
    set σ2 := σ1.setv T (σ1.val T - 1) with hσ2
    have e3 := WExec.inc (cap := cap) S σ2 (by
      simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hTS), Function.update_of_ne (Ne.symm hZS)]; omega)
    set σ3 := σ2.setv S (σ2.val S + 1) with hσ3
    have hv3 : σ3.val Z = σ.val Z - 1 ∧ σ3.val T = σ.val T - 1 ∧ σ3.val S = σ.val S + 1 := by
      simp [hσ3, hσ2, hσ1, Function.update_apply, hZT, hZS, hTS, Ne.symm hTS, Ne.symm hZT, Ne.symm hZS]
    have hrest := subLoop_spec Z T S hZT hZS hTS m σ3 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    apply WState.eq
    · simp [hσ3, hσ2, hσ1]
    · simp [hσ3, hσ2, hσ1]
    · funext r
      simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
      by_cases hr : r = S
      · subst hr; simp [Ne.symm hTS, Ne.symm hZS]; omega
      by_cases hr' : r = T
      · subst hr'; simp [hr, Ne.symm hZT]; omega
      by_cases hr'' : r = Z
      · subst hr''; simp [hr, hr']
      · simp [hr, hr', hr'']
    · simp [hσ3, hσ2, hσ1]

/-- `W` forward by `S` cells, `S := 0`. -/
def skipLoop (S : Fin nr) (W : Fin (ns + 1)) : WM ns nr := .whr S (.seq (.dec S) (.fwd W))

theorem skipLoop_spec (S : Fin nr) (W : Fin (ns + 1)) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val S = m → m ≤ cap →
      WExec cap (skipLoop S W) σ ((σ.setv S 0).seth W (σ.sh W + m)) (5 * m + 1)
  | 0, σ, h0, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases hr : r = S
      · subst hr; simp [h0]
      · simp [Function.update_of_ne hr]
    · simp
  | m + 1, σ, hm, hc => by
    have e1 := WExec.dec (cap := cap) S σ (by omega)
    have e2 := WExec.fwd (cap := cap) W (σ.setv S (σ.val S - 1))
    have hrest := skipLoop_spec S W m ((σ.setv S (σ.val S - 1)).seth W ((σ.setv S (σ.val S - 1)).sh W + 1))
      (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) hrest) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases hr : r = S
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    · simp

/-- Append `marks (1^T)`, moving `T` into `U`. -/
def onesLoop (T U : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .whr T (.seq (.dec T) (.seq (.inc U) (emitPair o OP true)))

theorem onesLoop_spec (T U : Fin nr) (o : Fin (ns + 1)) (OP : Fin nr) (hTU : T ≠ U) (hTO : T ≠ OP) (hUO : U ≠ OP) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val T = m → σ.sh o = (σ.st o).length → m ≤ cap → σ.val U + m ≤ cap →
      σ.val OP + 2 * m ≤ cap →
      WExec cap (onesLoop T U o OP) σ (appendO ((σ.setv T 0).setv U (σ.val U + m)) o OP
        (marks (List.replicate m true))) (23 * m + 1)
  | 0, σ, h0, ho, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    rw [List.replicate_zero, show marks ([] : List Bool) = [] from rfl, WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
    apply WState.eq
    · simp
    · simp
    · funext r
      by_cases hr : r = U
      · subst hr; simp
      by_cases hr' : r = T
      · subst hr'; simp [Function.update_of_ne hr, h0]
      · simp [Function.update_of_ne hr, Function.update_of_ne hr']
    · simp
  | m + 1, σ, hm, ho, hc, hU, hO => by
    have e1 := WExec.dec (cap := cap) T σ (by omega)
    set σ1 := σ.setv T (σ.val T - 1) with hσ1
    have e2 := WExec.inc (cap := cap) U σ1 (by simp [hσ1, Function.update_of_ne (Ne.symm hTU)]; omega)
    set σ2 := σ1.setv U (σ1.val U + 1) with hσ2
    have e3 := emitPair_spec cap o OP true σ2 (by simpa [hσ2, hσ1] using ho)
      (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hUO), Function.update_of_ne (Ne.symm hTO)]; omega)
    set σ3 := appendO σ2 o OP [true, true] with hσ3
    have hrest := onesLoop_spec T U o OP hTU hTO hUO m σ3
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hTO, Function.update_of_ne hTU]; omega)
      (by simp [hσ3, hσ2, hσ1, ho])
      (by omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hUO, Function.update_of_ne (Ne.symm hTU)]; omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hUO), Function.update_of_ne (Ne.symm hTO)]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    have hmk : marks (List.replicate (m + 1) true) = [true, true] ++ marks (List.replicate m true) := by
      simp [List.replicate_succ, marks]
    apply WState.eq
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, hmk, marks_length]; omega
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, hmk]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
    · funext r
      simp only [hσ3, hσ2, hσ1, appendO_val, WState.setv_val, Function.update_apply, hmk, List.length_append,
        marks_length, List.length_replicate, List.length_cons, List.length_nil]
      split_ifs <;> simp_all <;> omega
    · simp [hσ3, hσ2, hσ1]

/-- Append the scanned bit as `marks [b]`. -/
def emitScanned (W o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := .ifs W (emitPair o OP true) (emitPair o OP false)

theorem emitScanned_spec (W o : Fin (ns + 1)) (OP : Fin nr) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (emitScanned W o OP) σ (appendO σ o OP (marks [wbit σ W])) 16 := by
  rcases hb : wbit σ W with _ | _
  · exact WExec.ifsF hb (emitPair_spec cap o OP false σ ho hc)
  · exact WExec.ifsT hb (emitPair_spec cap o OP true σ ho hc)

/-- Append `marks` of the next `U` bits of `W` (raw, `false` past the end), moving past them, `U := 0`. -/
def copyBitsLoop (U : Fin nr) (W o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .whr U (.seq (.dec U) (.seq (emitScanned W o OP) (.fwd W)))

theorem copyBitsLoop_spec (U : Fin nr) (W o : Fin (ns + 1)) (OP : Fin nr) (hWo : W ≠ o) (hUO : U ≠ OP) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val U = m → σ.sh o = (σ.st o).length → m ≤ cap → σ.val OP + 2 * m ≤ cap →
      WExec cap (copyBitsLoop U W o OP) σ (appendO ((σ.setv U 0).seth W (σ.sh W + m)) o OP
        (marks (List.ofFn fun j : Fin m => (σ.st W).getD (σ.sh W + j.val) false))) (22 * m + 1)
  | 0, σ, h0, ho, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    rw [List.ofFn_zero, show marks ([] : List Bool) = [] from rfl, WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases hr : r = U
      · subst hr; simp [h0]
      · simp [Function.update_of_ne hr]
    · simp
  | m + 1, σ, hm, ho, hc, hO => by
    have e1 := WExec.dec (cap := cap) U σ (by omega)
    set σ1 := σ.setv U (σ.val U - 1) with hσ1
    have e2 := emitScanned_spec cap W o OP σ1 (by simpa [hσ1] using ho)
      (by simp [hσ1, Function.update_of_ne (Ne.symm hUO)]; omega)
    set σ2 := appendO σ1 o OP (marks [wbit σ1 W]) with hσ2
    have e3 := WExec.fwd (cap := cap) W σ2
    set σ3 := σ2.seth W (σ2.sh W + 1) with hσ3
    have hbit : wbit σ1 W = (σ.st W).getD (σ.sh W) false := by simp [hσ1, wbit, readTapeBit]
    have hrest := copyBitsLoop_spec U W o OP hWo hUO m σ3
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hUO]; omega)
      (by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hWo), ho])
      (by omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hUO), marks_length]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) hrest) ?_ (by omega)
    have hW3 : σ3.st W = σ.st W := by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hWo]
    have hsh3 : σ3.sh W = σ.sh W + 1 := by simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hWo]
    have hbits : (List.ofFn fun j : Fin (m + 1) => (σ.st W).getD (σ.sh W + j.val) false) =
        (σ.st W).getD (σ.sh W) false :: List.ofFn fun j : Fin m => (σ3.st W).getD (σ3.sh W + j.val) false := by
      rw [List.ofFn_succ, hW3, hsh3]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1; congr 1; funext j; congr 1; omega
    have hmk : marks ((σ.st W).getD (σ.sh W) false :: List.ofFn fun j : Fin m => (σ3.st W).getD (σ3.sh W + j.val) false)
        = marks [(σ.st W).getD (σ.sh W) false] ++ marks (List.ofFn fun j : Fin m => (σ3.st W).getD (σ3.sh W + j.val) false) := by
      rw [← marksApp]; rfl
    rw [hbits, hmk, hbit.symm]
    apply WState.eq
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hWo), marks_length, ho]; omega
      · by_cases hjW : j = W
        · subst hjW; simp [hσ3, hσ2, hσ1, appendO, hj]; omega
        · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjW]
    · funext j; by_cases hj : j = o
      · subst hj; simp [hσ3, hσ2, hσ1, appendO]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hj]
    · funext r
      simp only [hσ3, hσ2, hσ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply,
        List.length_append, marks_length, List.length_ofFn, List.length_cons, List.length_nil]
      split_ifs <;> simp_all <;> omega
    · simp [hσ3, hσ2, hσ1]

/-! ## The number transcoder -/

/-- Read the count and scan the bits: `T := ℓ − tz b`, `S := tz b`, head back on the first bit. -/
def numScan (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (countW W (X 0)) (.seq (scanLoop W X) (.seq (rewindLoop W (X 2)) (subLoop (X 3) (X 1) (X 4))))

/-- Append `marks (natWord v)` from the scan registers and move past the field. -/
def numEmit (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (OP : Fin nr) : WM ns nr :=
  .ifr (X 1)
    (.seq (onesLoop (X 1) (X 2) o OP) (.seq (emitPair o OP false) (.seq (copyBitsLoop (X 2) W o OP) (skipLoop (X 4) W))))
    (.seq (emitMarks o OP [true, false, false]) (skipLoop (X 4) W))

def numW (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (OP : Fin nr) : WM ns nr := .seq (numScan W X) (numEmit W o X OP)

/-- The field length at position `p`. -/
def fieldLen (w : List Bool) (p : ℕ) : ℕ := (readCount (w.drop p)).1

theorem getD_drop (w : List Bool) (q i : ℕ) : (w.drop q).getD i false = w.getD (q + i) false := by
  simp [List.getD_eq_getElem?_getD]

/-- `readNum` at any position, in terms of `fieldLen` and `fieldBits`. -/
theorem readNum_drop (w : List Bool) (p : ℕ) :
    readNum (w.drop p) = (value (fieldBits w (p + fieldLen w p + 1) (fieldLen w p)),
      w.drop (p + fieldLen w p + 1 + fieldLen w p)) := by
  unfold readNum readField readBits fieldLen
  rw [readCount_drop]
  simp only [List.drop_drop, getD_drop, fieldBits]

theorem numScan_spec (W : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (σ : WState ns nr) (hX : ∀ i, σ.val (X i) = 0)
    (hcap : fieldLen (σ.st W) (σ.sh W) + 1 ≤ cap) :
    WExec cap (numScan W X) σ
      (((σ.seth W (σ.sh W + fieldLen (σ.st W) (σ.sh W) + 1)).setv (X 1)
        (fieldLen (σ.st W) (σ.sh W) - tz (fieldBits (σ.st W) (σ.sh W + fieldLen (σ.st W) (σ.sh W) + 1)
          (fieldLen (σ.st W) (σ.sh W))))).setv (X 4)
        (tz (fieldBits (σ.st W) (σ.sh W + fieldLen (σ.st W) (σ.sh W) + 1) (fieldLen (σ.st W) (σ.sh W)))))
      (3 * fieldLen (σ.st W) (σ.sh W) ^ 2 + 45 * fieldLen (σ.st W) (σ.sh W) + 12) := by
  set ℓ := fieldLen (σ.st W) (σ.sh W) with hℓ
  set p1 := σ.sh W + ℓ + 1 with hp1
  set b := fieldBits (σ.st W) p1 ℓ with hb
  have hz : tz b ≤ ℓ := (tz_le b).trans (by rw [hb, fieldBits_length])
  have e1 := countW_spec cap W (X 0) σ (by rw [hX]; simp [fieldLen] at hℓ ⊢; omega)
  rw [show (readCount ((σ.st W).drop (σ.sh W))).1 = ℓ from rfl] at e1
  set σA := (σ.seth W (σ.sh W + ℓ + 1)).setv (X 0) (σ.val (X 0) + ℓ) with hσA
  have hA0 : scanSt W X σA ℓ 0 (fieldBits (σA.st W) (σA.sh W) ℓ) = σA := by
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [scanSt]
      · simp [scanSt, Function.update_of_ne hj]
    · rfl
    · funext r
      simp only [scanSt, hσA, WState.setv_val, WState.seth_val, Function.update_apply, Nat.sub_zero, List.take_zero]
      split_ifs <;> simp_all [tz_nil]
    · rfl
  have e2 := scanLoop_spec cap W X σA ℓ hcap ℓ 0 (by omega)
  rw [hA0] at e2
  have hbA : fieldBits (σA.st W) (σA.sh W) ℓ = b := by simp [hσA, hb, hp1]
  rw [hbA] at e2
  set σB := scanSt W X σA ℓ ℓ b with hσB
  have hB2 : σB.val (X 2) = ℓ := by
    simp [hσB, scanSt, Xne X (show (2 : Fin 5) ≠ 0 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide)]
  have hBsh : σB.sh W = p1 + ℓ := by simp [hσB, scanSt, hσA, hp1]
  have e3 := rewindLoop_spec cap W (X 2) ℓ σB hB2 (by omega) (by omega)
  set σC := (σB.setv (X 2) 0).seth W (σB.sh W - ℓ) with hσC
  have hbt : b.take ℓ = b := List.take_of_length_le (by rw [hb, fieldBits_length])
  have hC3 : σC.val (X 3) = tz b := by
    simp [hσC, hσB, scanSt, Xne X (show (3 : Fin 5) ≠ 0 by decide), Xne X (show (3 : Fin 5) ≠ 1 by decide),
      Xne X (show (3 : Fin 5) ≠ 2 by decide), hbt]
  have hC1 : σC.val (X 1) = ℓ := by
    simp [hσC, hσB, scanSt, Xne X (show (1 : Fin 5) ≠ 0 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide)]
  have hC4 : σC.val (X 4) = 0 := by
    simp [hσC, hσB, scanSt, hσA, Xne X (show (4 : Fin 5) ≠ 0 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide),
      Xne X (show (4 : Fin 5) ≠ 2 by decide), Xne X (show (4 : Fin 5) ≠ 3 by decide), hX]
  have e4 := subLoop_spec cap (X 3) (X 1) (X 4) (Xne X (by decide)) (Xne X (by decide)) (Xne X (by decide))
    (tz b) σC hC3 (by omega) (by omega) (by omega) (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ ?_
  · apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hσC, hσB, scanSt, hσA, hp1]
      · simp [hσC, hσB, scanSt, hσA, Function.update_of_ne hj]
    · simp [hσC, hσB, scanSt, hσA]
    · funext r
      simp only [hσC, hσB, scanSt, hσA, WState.setv_val, WState.seth_val, Function.update_apply, hbt]
      split_ifs <;> simp_all
    · simp [hσC, hσB, scanSt, hσA]
  · have : ℓ * (3 * ℓ + 20) = 3 * ℓ ^ 2 + 20 * ℓ := by ring
    omega

theorem natWord_zero : natWord 0 = [true, false, false] := by decide

theorem ofFn_getD_take (w : List Bool) (p1 ℓ t : ℕ) (ht : t ≤ ℓ) :
    (List.ofFn fun j : Fin t => w.getD (p1 + j.val) false) = (fieldBits w p1 ℓ).take t := by
  apply List.ext_getElem (by simp [fieldBits_length]; omega)
  intro i h1 h2
  simp [fieldBits]

theorem numEmit_spec (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (OP : Fin nr) (hWo : W ≠ o) (hOP : ∀ i, X i ≠ OP)
    (τ : WState ns nr) (ℓ : ℕ) (_h0 : τ.val (X 0) = 0) (h2 : τ.val (X 2) = 0) (_h3 : τ.val (X 3) = 0)
    (h1 : τ.val (X 1) = ℓ - tz (fieldBits (τ.st W) (τ.sh W) ℓ)) (h4 : τ.val (X 4) = tz (fieldBits (τ.st W) (τ.sh W) ℓ))
    (ho : τ.sh o = (τ.st o).length) (hcap : ℓ + 1 ≤ cap) (hOc : τ.val OP + 4 * ℓ + 6 ≤ cap) :
    WExec cap (numEmit W o X OP) τ
      (appendO ((((τ.setv (X 1) 0).setv (X 4) 0)).seth W (τ.sh W + ℓ)) o OP
        (marks (natWord (value (fieldBits (τ.st W) (τ.sh W) ℓ))))) (50 * ℓ + 60) := by
  set b := fieldBits (τ.st W) (τ.sh W) ℓ with hb
  have hbl : b.length = ℓ := fieldBits_length _ _ _
  have hz : tz b ≤ ℓ := hbl ▸ tz_le b
  set t := ℓ - tz b with ht
  set z := tz b with hzdef
  by_cases htz : t = 0
  · -- the value is `0`
    have hzℓ : z = ℓ := by omega
    have hv : value b = 0 := value_of_tz b (by rw [hbl]; omega)
    rw [hv, natWord_zero]
    have e1 := emitMarks_spec cap o OP [true, false, false] τ ho (by simp; omega)
    set τ1 := appendO τ o OP (marks [true, false, false]) with hτ1
    have e2 := skipLoop_spec cap (X 4) W z τ1 (by simp [hτ1, appendO, Function.update_of_ne (hOP 4), h4]) (by omega)
    refine WExec.cast cap (WExec.ifrF (by rw [h1]; omega) (WExec.seq e1 e2)) ?_ (by simp; omega)
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hτ1, appendO, hWo]; omega
      · by_cases hjo : j = o
        · subst hjo; simp [hτ1, appendO, hj, Ne.symm hWo]
        · simp [hτ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hτ1, appendO]
      · simp [hτ1, appendO, Function.update_of_ne hjo]
    · funext r
      simp only [hτ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hr : r = OP
      · simp [hr, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]
      by_cases hr4 : r = X 4
      · simp [hr, hr4, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]
      by_cases hr1 : r = X 1
      · simp [hr, hr4, hr1, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide), h1]; omega
      · simp [hr, hr4, hr1]
    · simp [hτ1]
  · -- `1^t 0`, the first `t` bits, then skip the `z` trailing zeros
    have hlt : tz b < b.length := by omega
    have hnat := natWord_value b hlt
    rw [hbl, ← ht] at hnat
    rw [hnat]
    have e1 := onesLoop_spec cap (X 1) (X 2) o OP (Xne X (by decide)) (hOP 1) (hOP 2) t τ h1 ho (by omega)
      (by rw [h2]; omega) (by omega)
    set τ1 := appendO ((τ.setv (X 1) 0).setv (X 2) (τ.val (X 2) + t)) o OP (marks (List.replicate t true)) with hτ1
    have e2 := emitPair_spec cap o OP false τ1 (by simp [hτ1, appendO, ho])
      (by simp [hτ1, appendO, Function.update_apply, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide), marks_length]; omega)
    set τ2 := appendO τ1 o OP [true, false] with hτ2
    have e3 := copyBitsLoop_spec cap (X 2) W o OP hWo (hOP 2) t τ2
      (by simp [hτ2, hτ1, appendO, Function.update_apply, hOP 2, h2])
      (by simp [hτ2, hτ1, appendO, ho, marks_length]; omega) (by omega)
      (by simp [hτ2, hτ1, appendO, Function.update_apply, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide), marks_length]; omega)
    set τ3 := appendO ((τ2.setv (X 2) 0).seth W (τ2.sh W + t)) o OP
      (marks (List.ofFn fun j : Fin t => (τ2.st W).getD (τ2.sh W + j.val) false)) with hτ3
    have e4 := skipLoop_spec cap (X 4) W z τ3
      (by simp [hτ3, hτ2, hτ1, appendO, Function.update_of_ne (hOP 4), Function.update_of_ne (Xne X (show (4 : Fin 5) ≠ 1 by decide)),
        Function.update_of_ne (Xne X (show (4 : Fin 5) ≠ 2 by decide)), h4]) (by omega)
    have hW2 : τ2.st W = τ.st W := by simp [hτ2, hτ1, appendO, Function.update_of_ne hWo]
    have hsh2 : τ2.sh W = τ.sh W := by simp [hτ2, hτ1, appendO, Function.update_of_ne hWo]
    have hbits : (List.ofFn fun j : Fin t => (τ2.st W).getD (τ2.sh W + j.val) false) = b.take t := by
      rw [hW2, hsh2, hb]; exact ofFn_getD_take _ _ _ _ (by omega)
    rw [hbits] at hτ3
    refine WExec.cast cap (WExec.ifrT (by rw [h1]; omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)))) ?_ (by omega)
    have hm : marks (List.replicate t true ++ false :: b.take t) =
        marks (List.replicate t true) ++ [true, false] ++ marks (b.take t) := by
      rw [marksApp, show (false :: b.take t) = [false] ++ b.take t from rfl, marksApp]; simp [marks]
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hτ3, hτ2, hτ1, appendO, hWo]; omega
      · by_cases hjo : j = o
        · subst hjo; simp [hτ3, hτ2, hτ1, appendO, hj, Ne.symm hWo, hm, marks_length]; omega
        · simp [hτ3, hτ2, hτ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hτ3, hτ2, hτ1, appendO, hm]
      · simp [hτ3, hτ2, hτ1, appendO, Function.update_of_ne hjo]
    · funext r
      simp only [hτ3, hτ2, hτ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply, hm,
        List.length_append, marks_length, List.length_replicate, List.length_take, List.length_cons, List.length_nil]
      by_cases hr : r = OP
      · simp [hr, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]; omega
      by_cases hr4 : r = X 4
      · simp [hr, hr4, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]
      by_cases hr2 : r = X 2
      · simp [hr, hr4, hr2, h2, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]
      by_cases hr1 : r = X 1
      · simp [hr, hr4, hr2, hr1, Ne.symm (hOP 1), Ne.symm (hOP 2), Ne.symm (hOP 4), hOP 1, hOP 2, hOP 4, Xne X (show (1 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 1 by decide), Xne X (show (1 : Fin 5) ≠ 2 by decide), Xne X (show (2 : Fin 5) ≠ 1 by decide), Xne X (show (2 : Fin 5) ≠ 4 by decide), Xne X (show (4 : Fin 5) ≠ 2 by decide)]
      · simp [hr, hr4, hr2, hr1]
    · simp [hτ3, hτ2, hτ1]

/-- **The number transcoder**, on every stream: the number field at the head of `W` (read by `Format.readNum`) is
appended to `o` as `marks (natWord v)`, and the head moves past the field. -/
theorem numW_spec (W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (OP : Fin nr) (hWo : W ≠ o) (hOP : ∀ i, X i ≠ OP)
    (σ : WState ns nr) (hX : ∀ i, σ.val (X i) = 0) (ho : σ.sh o = (σ.st o).length)
    (hcap : fieldLen (σ.st W) (σ.sh W) + 1 ≤ cap) (hOc : σ.val OP + 4 * fieldLen (σ.st W) (σ.sh W) + 6 ≤ cap) :
    WExec cap (numW W o X OP) σ
      (appendO (σ.seth W (σ.sh W + fieldLen (σ.st W) (σ.sh W) + 1 + fieldLen (σ.st W) (σ.sh W))) o OP
        (marks (natWord (readNum ((σ.st W).drop (σ.sh W))).1)))
      (3 * fieldLen (σ.st W) (σ.sh W) ^ 2 + 100 * fieldLen (σ.st W) (σ.sh W) + 80) := by
  set ℓ := fieldLen (σ.st W) (σ.sh W) with hℓ
  have e1 := numScan_spec cap W X σ hX hcap
  rw [← hℓ] at e1
  set τ := ((σ.seth W (σ.sh W + ℓ + 1)).setv (X 1) (ℓ - tz (fieldBits (σ.st W) (σ.sh W + ℓ + 1) ℓ))).setv (X 4)
    (tz (fieldBits (σ.st W) (σ.sh W + ℓ + 1) ℓ)) with hτ
  have hτW : τ.st W = σ.st W := by simp [hτ]
  have hτsh : τ.sh W = σ.sh W + ℓ + 1 := by simp [hτ]
  have e2 := numEmit_spec cap W o X OP hWo hOP τ ℓ
    (by simp [hτ, Function.update_of_ne (Xne X (show (0 : Fin 5) ≠ 4 by decide)),
      Function.update_of_ne (Xne X (show (0 : Fin 5) ≠ 1 by decide)), hX])
    (by simp [hτ, Function.update_of_ne (Xne X (show (2 : Fin 5) ≠ 4 by decide)),
      Function.update_of_ne (Xne X (show (2 : Fin 5) ≠ 1 by decide)), hX])
    (by simp [hτ, Function.update_of_ne (Xne X (show (3 : Fin 5) ≠ 4 by decide)),
      Function.update_of_ne (Xne X (show (3 : Fin 5) ≠ 1 by decide)), hX])
    (by rw [hτW, hτsh]; simp [hτ, Function.update_of_ne (Xne X (show (1 : Fin 5) ≠ 4 by decide))])
    (by rw [hτW, hτsh]; simp [hτ])
    (by simpa [hτ, Function.update_apply, Ne.symm hWo] using ho) hcap
    (by simp [hτ, Function.update_apply, Ne.symm (hOP 1), Ne.symm (hOP 4)]; omega)
  rw [hτW, hτsh] at e2
  have hread := readNum_drop (σ.st W) (σ.sh W)
  rw [← hℓ] at hread
  rw [hread]
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [hτ, appendO, hWo]
    · by_cases hjo : j = o
      · subst hjo; simp [hτ, appendO, hj]
      · simp [hτ, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · simp [hτ, appendO]
  · funext r
    simp only [hτ, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
    have := hOP 1; have := hOP 4; have := Xne X (show (1 : Fin 5) ≠ 4 by decide)
    have h1 := hX 1; have h4 := hX 4
    split_ifs <;> simp_all
  · simp [hτ]

end NearCubicGates.Close.Codec
