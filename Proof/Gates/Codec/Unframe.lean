import Proof.Gates.Codec.PairFrame
import Proof.Gates.Codec.FieldInt
import Proof.Gates.Codec.FieldGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming

variable {ns nr : ℕ} (cap : ℕ)

/-- The first `m` witness bits, blanks past the end. -/
def prefixBits (bits : List Bool) (m : ℕ) : List Bool := List.ofFn fun i : Fin m => bits.getD i.val false

theorem prefixBits_succ (bits : List Bool) (m : ℕ) :
    prefixBits bits (m + 1) = prefixBits bits m ++ [bits.getD m false] := by
  rw [prefixBits, prefixBits, List.ofFn_succ_last]
  simp

theorem frame_getD_even (bits : List Bool) (j : ℕ) :
    (RepairOrdinary.frame bits).getD (2 * j) false = decide (j < bits.length) := by
  induction bits generalizing j with
  | nil => cases j <;> simp [RepairOrdinary.frame]
  | cons b bs ih =>
    cases j with
    | zero => simp [RepairOrdinary.frame]
    | succ j =>
      have := ih j
      show (true :: b :: RepairOrdinary.frame bs).getD (2 * j + 1 + 1) false = decide (j + 1 < bs.length + 1)
      rw [List.getD_cons_succ, List.getD_cons_succ, this]
      simp

theorem frame_getD_odd (bits : List Bool) (j : ℕ) (hj : j < bits.length) :
    (RepairOrdinary.frame bits).getD (2 * j + 1) false = bits.getD j false := by
  induction bits generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero => simp [RepairOrdinary.frame]
    | succ j =>
      have := ih j (by simpa using hj)
      show (true :: b :: RepairOrdinary.frame bs).getD (2 * j + 1 + 1 + 1) false = (b :: bs).getD (j + 1) false
      rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, this]

/-- One cell: on a marker, copy the data bit and step past the pair; at the end, write a blank. -/
def unframeCell (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .ifs src (.seq (.fwd src) (.seq (.ifs src (emitC dst OP true) (emitC dst OP false)) (.fwd src))) (emitC dst OP false)

theorem unframeCell_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr) (bits : List Bool) (j : ℕ)
    (σ : WState ns nr) (hs : σ.st src = RepairOrdinary.frame bits) (hsh : σ.sh src = 2 * min j bits.length)
    (hd : σ.sh dst = (σ.st dst).length) (hc : σ.val OP < cap) :
    WExec cap (unframeCell src dst OP) σ
      ((appendO σ dst OP [bits.getD j false]).seth src (2 * min (j + 1) bits.length)) 14 := by
  have hfw : ∀ τ : WState ns nr, WExec cap (.fwd src) τ (τ.seth src (τ.sh src + 1)) 1 := fun τ => WExec.fwd src τ
  by_cases hj : j < bits.length
  · have hm : min j bits.length = j := by omega
    have hm1 : min (j + 1) bits.length = j + 1 := by omega
    rw [hm] at hsh
    have hmark : wbit σ src = true := by
      unfold wbit readTapeBit; rw [hs, hsh, frame_getD_even]; simpa using hj
    set σ1 := σ.seth src (σ.sh src + 1) with hσ1
    have hdata : wbit σ1 src = bits.getD j false := by
      unfold wbit readTapeBit; simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hs, hsh, frame_getD_odd bits j hj]
    have hd1 : σ1.sh dst = (σ1.st dst).length := by simp [hσ1, Function.update_of_ne hsd.symm, hd]
    have hc1 : σ1.val OP < cap := by simpa [hσ1] using hc
    have ebit : WExec cap (.ifs src (emitC dst OP true) (emitC dst OP false)) σ1
        (((σ1.sets dst ((σ1.st dst) ++ [bits.getD j false])).seth dst (σ1.sh dst + 1)).setv OP (σ1.val OP + 1)) 8 := by
      cases hb : bits.getD j false
      · exact WExec.mono (WExec.ifsF (by rw [hdata, hb]) (emitC_spec cap dst OP false σ1 hd1 hc1)) (by omega)
      · exact WExec.mono (WExec.ifsT (by rw [hdata, hb]) (emitC_spec cap dst OP true σ1 hd1 hc1)) (by omega)
    set σ2 := ((σ1.sets dst ((σ1.st dst) ++ [bits.getD j false])).seth dst (σ1.sh dst + 1)).setv OP (σ1.val OP + 1)
      with hσ2
    have e := WExec.ifsT (Q := emitC dst OP false) hmark (WExec.seq (hfw σ) (WExec.seq ebit (hfw σ2)))
    refine WExec.cast cap e ?_ (by omega)
    rw [hm1]
    apply WState.eq
    · funext y; by_cases hy : y = src
      · subst hy; simp [hσ2, hσ1, appendO, hsd, hsh]; omega
      · by_cases hyd : y = dst
        · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hy, hsd.symm]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · funext y; by_cases hyd : y = dst
      · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hsd.symm]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hyd]
    · funext r; by_cases hr : r = OP
      · subst hr; simp [hσ2, hσ1, appendO]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hr]
    · simp [hσ2, hσ1, appendO]
  · have hm : min j bits.length = bits.length := by omega
    have hm1 : min (j + 1) bits.length = bits.length := by omega
    rw [hm] at hsh
    have hend : wbit σ src = false := by
      unfold wbit readTapeBit; rw [hs, hsh, frame_getD_even]; simp
    have hg : bits.getD j false = false := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : bits.length ≤ j)]
    have e := WExec.ifsF (P := .seq (.fwd src) (.seq (.ifs src (emitC dst OP true) (emitC dst OP false)) (.fwd src)))
      hend (emitC_spec cap dst OP false σ hd hc)
    refine WExec.cast cap e ?_ (by omega)
    rw [hm1, hg]
    apply WState.eq
    · funext y; by_cases hy : y = src
      · subst hy; simp [appendO, hsd, hsh]
      · by_cases hyd : y = dst
        · subst hyd; simp [appendO, Function.update_apply, hy]
        · simp [appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · rfl
    · rfl
    · rfl

/-- `m` cells (`K = m` counts down). -/
def unframeW (src dst : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr := repLoop K (unframeCell src dst OP)

/-- **c2: the witness prefix.** -/
theorem unframeW_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP) (bits : List Bool)
    (m : ℕ) (σ : WState ns nr) (hs : σ.st src = RepairOrdinary.frame bits) (hsh : σ.sh src = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hK : σ.val K = m) (hm : m ≤ cap) (hc : σ.val OP + m ≤ cap) :
    WExec cap (unframeW src dst OP K) σ
      (((appendO σ dst OP (prefixBits bits m)).seth src (2 * min m bits.length)).setv K 0) (m * (14 + 4) + 1) := by
  set g : ℕ → WState ns nr := fun i =>
    ((appendO σ dst OP (prefixBits bits i)).seth src (2 * min i bits.length)).setv K (m - i) with hg
  have hg0 : g 0 = σ := by
    apply WState.eq
    · funext y; by_cases hy : y = src
      · subst hy; simp [hg, appendO, hsd, hsh]
      · by_cases hyd : y = dst
        · subst hyd; simp [hg, appendO, Function.update_apply, hy, prefixBits]
        · simp [hg, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · funext y; by_cases hyd : y = dst
      · subst hyd; simp [hg, appendO, prefixBits]
      · simp [hg, appendO, Function.update_of_ne hyd]
    · funext r; by_cases hr : r = K
      · subst hr; simp [hg, hK]
      · by_cases hrO : r = OP
        · subst hrO; simp [hg, appendO, hr, prefixBits]
        · simp [hg, appendO, Function.update_of_ne hr, Function.update_of_ne hrO]
    · rfl
  have hstep : ∀ i < m, WExec cap (unframeCell src dst OP) ((g i).setv K (m - i - 1)) (g (i + 1)) 14 := by
    intro i hi
    set τ := (g i).setv K (m - i - 1) with hτ
    have e := unframeCell_spec cap src dst hsd OP bits i τ
      (by simp [hτ, hg, appendO, Function.update_apply, hsd, hs])
      (by simp [hτ, hg, appendO, Function.update_apply, hsd])
      (by simp [hτ, hg, appendO, Function.update_apply, hsd.symm, hd, prefixBits])
      (by simp [hτ, hg, appendO, Function.update_of_ne hKO.symm, prefixBits]; omega)
    refine WExec.cast cap e ?_ le_rfl
    apply WState.eq
    · funext y; by_cases hy : y = src
      · subst hy; simp [hτ, hg, appendO, hsd]
      · by_cases hyd : y = dst
        · subst hyd; simp [hτ, hg, appendO, Function.update_apply, hy, prefixBits_succ]; omega
        · simp [hτ, hg, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · funext y; by_cases hyd : y = dst
      · subst hyd; simp [hτ, hg, appendO, prefixBits_succ]
      · simp [hτ, hg, appendO, Function.update_of_ne hyd]
    · funext r; by_cases hr : r = K
      · subst hr; simp [hτ, hg, appendO, hKO]; omega
      · by_cases hrO : r = OP
        · subst hrO; simp [hτ, hg, appendO, hr, prefixBits_succ, prefixBits]; omega
        · simp [hτ, hg, appendO, Function.update_of_ne hr, Function.update_of_ne hrO]
    · rfl
  have e := repLoop_spec cap K (unframeCell src dst OP) m 14 g (fun i _ => by simp [hg]) hm hstep
  rw [hg0] at e
  refine WExec.cast cap e ?_ le_rfl
  simp [hg]

/-! ## Copying a framed word -/

/-- One marked pair: copy the marker and the data bit. -/
def copyPairW (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (emitC dst OP true) (.seq (.fwd src) (.seq (.ifs src (emitC dst OP true) (emitC dst OP false)) (.fwd src)))

/-- Copy `frame x` from `src` (head at its start) to the end of `dst`. -/
def copyFrameW (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := .seq (.whs src (copyPairW src dst OP)) (emitC dst OP false)

theorem copyFrame_loop (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr) (rest : List Bool) :
    ∀ (x pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ RepairOrdinary.frame x ++ rest →
      σ.sh src = pre.length → σ.sh dst = (σ.st dst).length → σ.val OP + 2 * x.length ≤ cap →
      WExec cap (.whs src (copyPairW src dst OP)) σ
        ((appendO σ dst OP (marks x)).seth src (pre.length + 2 * x.length)) (22 * x.length + 1)
  | [], pre, σ, hst, hsh, hd, _ => by
    have hb : wbit σ src = false := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e : (appendO σ dst OP (marks [])).seth src (pre.length + 2 * ([] : List Bool).length) = σ := by
      apply WState.eq
      · funext y; by_cases hy : y = src
        · subst hy; simp [appendO, hsd, hsh, marks]
        · by_cases hyd : y = dst
          · subst hyd; simp [appendO, Function.update_apply, hy, marks]
          · simp [appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
      · funext y; by_cases hyd : y = dst
        · subst hyd; simp [appendO, marks]
        · simp [appendO, Function.update_of_ne hyd]
      · funext r; by_cases hr : r = OP
        · subst hr; simp [appendO, marks]
        · simp [appendO, Function.update_of_ne hr]
      · rfl
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp)
  | b :: x, pre, σ, hst, hsh, hd, hc => by
    have hb : wbit σ src = true := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e1 := emitC_spec (cap := cap) dst OP true σ hd (by simp at hc; omega)
    set σ1 := ((σ.sets dst (σ.st dst ++ [true])).seth dst (σ.sh dst + 1)).setv OP (σ.val OP + 1) with hσ1
    have e2 := WExec.fwd (cap := cap) src σ1
    set σ2 := σ1.seth src (σ1.sh src + 1) with hσ2
    have hdata : wbit σ2 src = b := by
      unfold wbit readTapeBit
      simp only [hσ2, hσ1, WState.seth_st, WState.setv_st, WState.sets_st, WState.seth_sh, WState.setv_sh,
        WState.sets_sh, Function.update_self]
      rw [Function.update_of_ne hsd, Function.update_of_ne hsd, hst, hsh]
      simp [RepairOrdinary.frame, List.getD_append_right]
    have hd2 : σ2.sh dst = (σ2.st dst).length := by simp [hσ2, hσ1, Function.update_apply, hsd.symm, hd]
    have hc2 : σ2.val OP < cap := by simp [hσ2, hσ1]; simp at hc; omega
    have e3 : WExec cap (.ifs src (emitC dst OP true) (emitC dst OP false)) σ2
        (((σ2.sets dst (σ2.st dst ++ [b])).seth dst (σ2.sh dst + 1)).setv OP (σ2.val OP + 1)) 8 := by
      cases b
      · exact WExec.mono (WExec.ifsF hdata (emitC_spec cap dst OP false σ2 hd2 hc2)) (by omega)
      · exact WExec.mono (WExec.ifsT hdata (emitC_spec cap dst OP true σ2 hd2 hc2)) (by omega)
    set σ3 := ((σ2.sets dst (σ2.st dst ++ [b])).seth dst (σ2.sh dst + 1)).setv OP (σ2.val OP + 1) with hσ3
    have e4 := WExec.fwd (cap := cap) src σ3
    set σ4 := σ3.seth src (σ3.sh src + 1) with hσ4
    have ih := copyFrame_loop src dst hsd OP rest x (pre ++ [true, b]) σ4
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hsd, hst, RepairOrdinary.frame])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hsd, hsh])
      (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hsd.symm, hd])
      (by simp [hσ4, hσ3, hσ2, hσ1]; simp at hc; omega)
    have e := WExec.whsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih
    refine WExec.cast cap e ?_ (by simp; omega)
    apply WState.eq
    · funext y; by_cases hy : y = src
      · subst hy; simp [hσ4, hσ3, hσ2, hσ1, appendO, hsd, hsh]; omega
      · by_cases hyd : y = dst
        · subst hyd; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hy, marks_length, marks]; omega
        · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · funext y; by_cases hyd : y = dst
      · subst hyd; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_apply, hsd.symm, marks]
      · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyd]
    · funext r; by_cases hr : r = OP
      · subst hr; simp [hσ4, hσ3, hσ2, hσ1, appendO, marks_length, marks]; omega
      · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hr]
    · simp [hσ4, hσ3, hσ2, hσ1, appendO]

/-- **Copy a framed word.** -/
theorem copyFrameW_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr) (x rest : List Bool)
    (σ : WState ns nr) (hst : σ.st src = RepairOrdinary.frame x ++ rest) (hsh : σ.sh src = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hc : σ.val OP + 2 * x.length + 1 ≤ cap) :
    WExec cap (copyFrameW src dst OP) σ ((appendO σ dst OP (RepairOrdinary.frame x)).seth src (2 * x.length))
      (22 * x.length + 1 + 1 + 7) := by
  have e1 := copyFrame_loop cap src dst hsd OP rest x [] σ (by simpa using hst) (by simpa using hsh) hd (by omega)
  set σ1 := (appendO σ dst OP (marks x)).seth src (([] : List Bool).length + 2 * x.length) with hσ1
  have e2 := emitC_spec (cap := cap) dst OP false σ1
    (by simp [hσ1, appendO, Function.update_apply, hsd.symm, hd, marks_length])
    (by simp [hσ1, appendO, marks_length]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = src
    · subst hy; simp [hσ1, appendO, hsd]
    · by_cases hyd : y = dst
      · subst hyd; simp [hσ1, appendO, Function.update_apply, hy, marks_length, frame_eq_marks]; omega
      · simp [hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y; by_cases hyd : y = dst
    · subst hyd; simp [hσ1, appendO, Function.update_apply, hsd.symm, frame_eq_marks]
    · simp [hσ1, appendO, Function.update_of_ne hyd]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [hσ1, appendO, marks_length, frame_eq_marks]; omega
    · simp [hσ1, appendO, Function.update_of_ne hr]
  · simp [hσ1, appendO]

/-- Copy `frame x` from `src` to an empty `dst` and rewind both (`OP`, `T`, `D` scratch at `0`). -/
def copyRW (src dst : Fin (ns + 1)) (OP T D : Fin nr) : WM ns nr :=
  .seq (copyFrameW src dst OP) (.seq (dupR OP T D) (.seq (WM.rewind dst OP) (WM.rewind src T)))

theorem copyRW_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP T D : Fin nr) (hOT : OP ≠ T) (hOD : OP ≠ D)
    (hTD : T ≠ D) (x rest : List Bool) (σ : WState ns nr) (hst : σ.st src = RepairOrdinary.frame x ++ rest)
    (hsh : σ.sh src = 0) (hd : σ.st dst = []) (hdh : σ.sh dst = 0) (hO : σ.val OP = 0) (hT : σ.val T = 0)
    (hD : σ.val D = 0) (hc : 4 * x.length + 4 ≤ cap) :
    WExec cap (copyRW src dst OP T D) σ (σ.sets dst (RepairOrdinary.frame x))
      (22 * x.length + 1 + 1 + 7 + 1 + (18 * (2 * x.length + 1) + 3 + 1 + (5 * (2 * x.length + 1) + 1 + 1 +
        (5 * (2 * x.length + 1) + 1)))) := by
  have hfl : (RepairOrdinary.frame x).length = 2 * x.length + 1 := by rw [frame_eq_marks]; simp [marks_length]
  have e1 := copyFrameW_spec cap src dst hsd OP x rest σ hst hsh (by rw [hd, hdh]; rfl) (by omega)
  set σ1 := (appendO σ dst OP (RepairOrdinary.frame x)).seth src (2 * x.length) with hσ1
  have hO1 : σ1.val OP = 2 * x.length + 1 := by simp [hσ1, appendO, hO, hfl]
  have e2 := dupR_spec cap OP T D hOT hOD hTD σ1 (by simp [hσ1, appendO, Function.update_of_ne hOD.symm, hD])
    (by rw [hO1]; simp [hσ1, appendO, Function.update_of_ne hOT.symm, hT]; omega)
  have hT1 : σ1.val T = 0 := by simp [hσ1, appendO, Function.update_of_ne hOT.symm, hT]
  rw [hO1, hT1, Nat.zero_add] at e2
  set σ2 := σ1.setv T (2 * x.length + 1) with hσ2
  have e3 := wrewind_spec cap dst OP (2 * x.length + 1) σ2 (by simp [hσ2, Function.update_of_ne hOT, hO1])
    (by simp [hσ2, Function.update_of_ne hOT, hO1]; omega)
  set σ3 := (σ2.setv OP 0).seth dst (σ2.sh dst - (2 * x.length + 1)) with hσ3
  have e4 := wrewind_spec cap src T (2 * x.length + 1) σ3 (by simp [hσ3, hσ2, Function.update_of_ne hOT.symm])
    (by simp [hσ3, hσ2, Function.update_of_ne hOT.symm]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = src
    · subst hy; simp [hσ3, hσ2, hσ1, appendO, hsd, hsh]
    · by_cases hyd : y = dst
      · subst hyd; simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hy, hdh, hd, hfl]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y; by_cases hyd : y = dst
    · subst hyd; simp [hσ3, hσ2, hσ1, appendO, hd]
    · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyd]
  · funext r
    by_cases hrT : r = T
    · subst hrT; simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hOT.symm, hT]
    · by_cases hrO : r = OP
      · subst hrO; simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hOT, hO]
      · simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne hrT, Function.update_of_ne hrO]
  · simp [hσ3, hσ2, hσ1, appendO]

/-- Frame the oracle field onto an empty `dst` and rewind `dst` (the reading head of `W` stays after the field). -/
def fieldRW (W dst : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr := .seq (fieldFrameW W dst OP K) (WM.rewind dst OP)

theorem fieldRW_spec (W dst : Fin (ns + 1)) (hWd : W ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP)
    (pre bits rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ (Worker.Format.countWord bits.length ++ bits) ++ rest) (hsh : σ.sh W = pre.length)
    (hd : σ.st dst = []) (hdh : σ.sh dst = 0) (hK : σ.val K = 0) (hO : σ.val OP = 0)
    (hc : 2 * bits.length + 2 ≤ cap) :
    WExec cap (fieldRW W dst OP K) σ
      ((σ.seth W (pre.length + bits.length + 1 + bits.length)).sets dst (RepairOrdinary.frame bits))
      (7 * bits.length + 3 + 1 + (22 * bits.length + 1 + 1 + 7) + 1 + (5 * (2 * bits.length + 1) + 1)) := by
  have hfl : (RepairOrdinary.frame bits).length = 2 * bits.length + 1 := by rw [frame_eq_marks]; simp [marks_length]
  have e1 := fieldFrameW_spec cap W dst hWd OP K hKO pre bits rest σ hst hsh (by rw [hd, hdh]; rfl) hK
    (by omega) (by omega)
  set σ1 := appendO (σ.seth W (pre.length + bits.length + 1 + bits.length)) dst OP (RepairOrdinary.frame bits) with hσ1
  have e2 := wrewind_spec cap dst OP (2 * bits.length + 1) σ1 (by simp [hσ1, appendO, hO, hfl])
    (by simp [hσ1, appendO, hO, hfl]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = dst
    · subst hy; simp [hσ1, appendO, Function.update_apply, hWd.symm, hdh, hd, hfl]
    · by_cases hyW : y = W
      · subst hyW; simp [hσ1, appendO, Function.update_apply, hWd]
      · simp [hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyW]
  · funext y; by_cases hy : y = dst
    · subst hy; simp [hσ1, appendO, hd]
    · simp [hσ1, appendO, Function.update_of_ne hy]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [hσ1, appendO, hO]
    · simp [hσ1, appendO, Function.update_of_ne hr]
  · simp [hσ1, appendO]

theorem readCount_replicate (q : ℕ) : Worker.Format.readCount (List.replicate q true) = (q, []) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [List.replicate_succ]
    show ((Worker.Format.readCount (List.replicate q true)).1 + 1,
      (Worker.Format.readCount (List.replicate q true)).2) = (q + 1, [])
    rw [ih]

/-- Read a unary count from the start of `S` into `Q` and rewind `S` (`T`, `D` scratch). -/
def unaryQ (S : Fin (ns + 1)) (Q T D : Fin nr) : WM ns nr :=
  .seq (countW S Q) (.seq (dupR Q T D) (.seq (.inc T) (WM.rewind S T)))

theorem unaryQ_spec (S : Fin (ns + 1)) (Q T D : Fin nr) (hQT : Q ≠ T) (hQD : Q ≠ D) (hTD : T ≠ D) (q : ℕ)
    (σ : WState ns nr) (hs : σ.st S = List.replicate q true) (hsh : σ.sh S = 0) (hQ : σ.val Q = 0)
    (hT : σ.val T = 0) (hD : σ.val D = 0) (hc : 2 * q + 2 ≤ cap) :
    WExec cap (unaryQ S Q T D) σ (σ.setv Q q)
      (7 * q + 3 + 1 + (18 * q + 3 + 1 + (3 + 1 + (5 * (q + 1) + 1)))) := by
  have hrc : Worker.Format.readCount ((σ.st S).drop (σ.sh S)) = (q, []) := by
    rw [hs, hsh, List.drop_zero]; exact readCount_replicate q
  have e1 := countW_spec cap S Q σ (by rw [hrc, hQ]; omega)
  rw [hrc, hQ, hsh] at e1
  simp only [Nat.zero_add] at e1
  set σ1 := (σ.seth S (q + 1)).setv Q q with hσ1
  have e2 := dupR_spec cap Q T D hQT hQD hTD σ1 (by simp [hσ1, Function.update_of_ne hQD.symm, hD])
    (by simp [hσ1, Function.update_of_ne hQT.symm, hT]; omega)
  have hT1 : σ1.val T = 0 := by simp [hσ1, Function.update_of_ne hQT.symm, hT]
  have hQ1 : σ1.val Q = q := by simp [hσ1]
  rw [hT1, hQ1, Nat.zero_add] at e2
  set σ2 := σ1.setv T q with hσ2
  have e3 := WExec.inc (cap := cap) T σ2 (by simp [hσ2]; omega)
  set σ3 := σ2.setv T (σ2.val T + 1) with hσ3
  have e4 := wrewind_spec cap S T (q + 1) σ3 (by simp [hσ3, hσ2]) (by simp [hσ3, hσ2]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = S
    · subst hy; simp [hσ3, hσ2, hσ1, hsh]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hy]
  · rfl
  · funext r; by_cases hr : r = T
    · subst hr; simp [hσ3, hσ2, hσ1, Function.update_of_ne hQT.symm, hT]
    · by_cases hrQ : r = Q
      · subst hrQ; simp [hσ3, hσ2, hσ1, Function.update_of_ne hr]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hr, Function.update_of_ne hrQ]
  · rfl

end NearCubicGates.Close.Codec
