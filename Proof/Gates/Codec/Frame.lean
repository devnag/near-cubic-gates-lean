import Proof.Gates.Codec.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming

variable {ns nr : ℕ} (cap : ℕ)

/-- One cell: append `[true, b]` for the scanned bit `b` of `src`, then step `src`. -/
def frameCell (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.ifs src (emitPair dst OP true) (emitPair dst OP false)) (.fwd src)

theorem frameCell_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr) (σ : WState ns nr)
    (hd : σ.sh dst = (σ.st dst).length) (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (frameCell src dst OP) σ
      ((appendO σ dst OP [true, readTapeBit (σ.st src) (σ.sh src)]).seth src (σ.sh src + 1)) 18 := by
  have hfw : ∀ τ : WState ns nr, τ.st src = σ.st src → τ.sh src = σ.sh src →
      WExec cap (.fwd src) τ (τ.seth src (σ.sh src + 1)) 1 := by
    intro τ _ hsh; have := WExec.fwd (cap := cap) src τ; rwa [hsh] at this
  cases hb : readTapeBit (σ.st src) (σ.sh src) with
  | false =>
    have hw : wbit σ src = false := by unfold wbit; exact hb
    have h1 := emitPair_spec cap dst OP false σ hd hc
    have h2 := hfw (appendO σ dst OP [true, false]) (by simp [appendO, Function.update_of_ne hsd])
      (by simp [appendO, Function.update_of_ne hsd])
    exact WExec.mono (WExec.seq (WExec.ifsF hw h1) h2) (by omega)
  | true =>
    have hw : wbit σ src = true := by unfold wbit; exact hb
    have h1 := emitPair_spec cap dst OP true σ hd hc
    have h2 := hfw (appendO σ dst OP [true, true]) (by simp [appendO, Function.update_of_ne hsd])
      (by simp [appendO, Function.update_of_ne hsd])
    exact WExec.mono (WExec.seq (WExec.ifsT hw h1) h2) (by omega)

/-- `K` times `frameCell`. -/
def frameStream (src dst : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (frameCell src dst OP))

theorem frameStream_spec (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP) :
    ∀ (Y : List Bool) (pre rest : List Bool) (σ : WState ns nr), σ.st src = pre ++ Y ++ rest →
      σ.sh src = pre.length → σ.sh dst = (σ.st dst).length → σ.val K = Y.length → Y.length ≤ cap →
      σ.val OP + 2 * Y.length ≤ cap →
      WExec cap (frameStream src dst OP K) σ
        (((appendO σ dst OP (marks Y)).setv K 0).seth src (pre.length + Y.length)) (22 * Y.length + 1)
  | [], pre, rest, σ, _, hsh, hd, hK, _, _ => by
    have e : ((appendO σ dst OP (marks ([] : List Bool))).setv K 0).seth src (pre.length + ([] : List Bool).length) = σ := by
      rw [show marks ([] : List Bool) = [] by simp [marks], appendO_nil σ dst OP hd]
      refine WState.eq ?_ rfl ?_ rfl
      · funext j; by_cases hj : j = src
        · subst hj; simp [hsh]
        · simp [Function.update_of_ne hj]
      · funext r; by_cases hr : r = K
        · subst hr; simp [hK]
        · simp [Function.update_of_ne hr]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hK)) (by simp)
  | b :: Y, pre, rest, σ, hst, hsh, hd, hK, hlen, hc => by
    have h1 := WExec.dec (cap := cap) K σ (by rw [hK]; simpa using hlen)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have hb : readTapeBit (σ1.st src) (σ1.sh src) = b := by
      simp only [hσ1, WState.setv_st, WState.setv_sh]; rw [hst, hsh]; unfold readTapeBit; simp
    have h2 := frameCell_spec cap src dst hsd OP σ1 (by simp [hσ1, hd])
      (by simp only [hσ1, WState.setv_val]; rw [Function.update_of_ne (Ne.symm hKO)]; simp at hc; omega)
    rw [hb] at h2
    set σ2 := (appendO σ1 dst OP [true, b]).seth src (σ1.sh src + 1) with hσ2
    have h3 := frameStream_spec src dst hsd OP K hKO Y (pre ++ [b]) rest σ2
      (by simp only [hσ2, WState.seth_st, appendO_st]; rw [Function.update_of_ne hsd]; simp [hσ1, hst])
      (by simp [hσ2, hσ1, hsh])
      (by simp [hσ2, appendO, Function.update_of_ne (Ne.symm hsd), hσ1, hd])
      (by simp [hσ2, appendO, Function.update_of_ne hKO, hσ1, hK])
      (by simp at hlen; omega)
      (by simp only [hσ2, WState.seth_val, appendO_val, Function.update_self]; simp only [hσ1, WState.setv_val];
          rw [Function.update_of_ne (Ne.symm hKO)]; simp at hc ⊢; omega)
    have hne : σ.val K ≠ 0 := by rw [hK]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq h1 h2) h3) ?_ (by simp; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = src
      · subst hj; simp [hσ2, hσ1, hsh]; ring
      · by_cases hjd : j = dst
        · subst hjd; simp [hσ2, hσ1, appendO, Function.update_of_ne hj, hd, marks]; ring
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjd]
    · funext j; by_cases hjd : j = dst
      · subst hjd; simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hsd), marks]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hjd]
    · funext r; by_cases hr : r = K
      · subst hr; simp [hσ2, hσ1, appendO, Function.update_of_ne hKO]
      · by_cases hrO : r = OP
        · subst hrO; simp [hσ2, hσ1, appendO, Function.update_of_ne hr, marks]; ring
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hr, Function.update_of_ne hrO]

end NearCubicGates.Close.Codec
