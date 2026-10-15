import Proof.Gates.Succinct.FieldW
import Proof.Gates.Succinct.Eval
import Proof.Gates.WordPrograms.Hoare
import Proof.Wire_3_5.PrimTReadEq
import Proof.Wire_3_5.FinalPassThrPtPad

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-! ## The value stream -/

/-- The value stream after the gate values `vals`, on a stream of `m` blank cells (paper lem:succinct-verifier,
stage (3): "keeping the gate values on a tape"). -/
def vtape (m : ℕ) (vals : List Bool) : List Bool := vals ++ List.replicate (m - vals.length) false

theorem read_vtape (m : ℕ) (vals : List Bool) (a : ℕ) : readTapeBit (vtape m vals) a = vals.getD a false := by
  unfold vtape readTapeBit
  by_cases h : a < vals.length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp [List.getElem?_eq_none (by omega : vals.length ≤ a)]

theorem vtape_length (m : ℕ) (vals : List Bool) : (vtape m vals).length = max m vals.length := by
  unfold vtape; simp; try omega

theorem vtape_write (m : ℕ) (vals : List Bool) (b : Bool) :
    writeTapeBit (vtape m vals) vals.length b = vtape m (vals ++ [b]) := by
  apply List.ext_getElem
  · rw [FinalPass.ThrPt.writeTapeBit_length, vtape_length, vtape_length]; simp <;> omega
  · intro n h1 h2
    have r := readTapeBit_write (vtape m vals) vals.length b n
    have r2 := read_vtape m (vals ++ [b]) n
    unfold readTapeBit at r r2
    rw [List.getD_eq_getElem _ _ h1] at r
    rw [List.getD_eq_getElem _ _ h2] at r2
    rw [r, r2]
    by_cases hn : n = vals.length
    · subst hn; simp
    · rw [if_neg hn]
      have hv := read_vtape m vals n
      unfold readTapeBit at hv
      rw [hv]
      by_cases hn' : n < vals.length
      · rw [List.getD_append _ _ _ _ hn']
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-! ## Moving a head by a register -/

/-- `out += [cell (head + A)]`, `A := 0`, the head returns (`Y` is scratch, `0` before and after). -/
def seekRead (i : Fin (ns + 1)) (A Y out : Fin nr) : WM ns nr :=
  .seq (.whr A (.seq (.dec A) (.seq (.fwd i) (.inc Y)))) (.seq (.ifs i (.inc out) .skip) (WM.rewind i Y))

/-- Forward by `A`, counting in `Y`. -/
theorem fwdBy_spec (cap : ℕ) (i : Fin (ns + 1)) (A Y : Fin nr) (hAY : A ≠ Y) (σ : WState ns nr) (a : ℕ)
    (hA : σ.val A = a) (hY : σ.val Y = 0) (hcap : a + 1 ≤ cap) :
    WExec cap (.whr A (.seq (.dec A) (.seq (.fwd i) (.inc Y)))) σ
      (((σ.setv A 0).setv Y a).seth i (σ.sh i + a)) (a * 9 + 1) := by
  let S : ℕ → WState ns nr := fun k => ((σ.setv A (a - k)).setv Y k).seth i (σ.sh i + k)
  have h0 : S 0 = σ := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext j; by_cases hj : j = i
      · subst hj; simp [S]
      · simp [S, Function.update_of_ne hj]
    · funext j; simp only [S, WState.seth_val, WState.setv_val, Function.update_apply]
      by_cases hjY : j = Y
      · subst hjY; simp [hY]
      · by_cases hjA : j = A
        · subst hjA; simp [hjY, hA]
        · simp [hjY, hjA]
  have e := UnionMachine.Round.wloop cap A (.seq (.fwd i) (.inc Y)) 5 a S
    (fun k _ => by simp [S, Function.update_apply, hAY]) (by omega)
    (fun k hk => by
      have e1 := WExec.fwd (cap := cap) i ((S k).setv A (a - k - 1))
      have e2 := WExec.inc (cap := cap) Y (((S k).setv A (a - k - 1)).seth i (((S k).setv A (a - k - 1)).sh i + 1))
        (by simp [S, Function.update_apply, Ne.symm hAY]; omega)
      refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
      refine WState.eq ?_ rfl ?_ rfl
      · funext j; by_cases hj : j = i
        · subst hj; simp [S]; omega
        · simp [S, Function.update_of_ne hj]
      · funext j; simp only [S, WState.seth_val, WState.setv_val, Function.update_apply]
        by_cases hjY : j = Y
        · subst hjY; simp [Ne.symm hAY]
        · by_cases hjA : j = A
          · subst hjA; simp [hjY]; omega
          · simp [hjY, hjA])
  rw [h0] at e
  refine WExec.cast cap e ?_ (by ring_nf; omega)
  simp only [S, Nat.sub_self]

/-- **Reading a cell by an offset register** (paper lem:succinct-verifier, stage (3): fetching an argument). -/
theorem seekRead_spec (cap : ℕ) (i : Fin (ns + 1)) (A Y out : Fin nr) (hAY : A ≠ Y) (hAo : A ≠ out) (hYo : Y ≠ out)
    (σ : WState ns nr) (hY : σ.val Y = 0) (hcap : σ.val A + σ.val out + 2 ≤ cap) :
    WExec cap (seekRead i A Y out) σ
      ((σ.setv A 0).setv out (σ.val out + (readTapeBit (σ.st i) (σ.sh i + σ.val A)).toNat)) (σ.val A * 14 + 10) := by
  have e1 := fwdBy_spec cap i A Y hAY σ (σ.val A) rfl hY (by omega)
  set τ := ((σ.setv A 0).setv Y (σ.val A)).seth i (σ.sh i + σ.val A) with hτ
  set bit := readTapeBit (σ.st i) (σ.sh i + σ.val A) with hbit
  have hτb : wbit τ i = bit := by simp [wbit, τ]; exact hbit.symm
  have e2 : WExec cap (.ifs i (.inc out) .skip) τ (τ.setv out (τ.val out + bit.toNat)) 4 := by
    cases hb : bit with
    | true =>
      have := WExec.inc (cap := cap) out τ (by simp [τ, Function.update_apply, Ne.symm hAo, Ne.symm hYo]; omega)
      exact WExec.mono (WExec.ifsT (by rw [hτb, hb]) this) (by omega)
    | false =>
      have e : τ.setv out (τ.val out + (false).toNat) = τ := by simp [wsetv_same]
      rw [e]; exact WExec.mono (WExec.ifsF (by rw [hτb, hb]) (WExec.skip τ)) (by omega)
  have e3 := wrewind_spec cap i Y (σ.val A) (τ.setv out (τ.val out + bit.toNat))
    (by simp [τ, Function.update_apply, hYo]) (by simp [τ, Function.update_apply, hYo]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j; by_cases hj : j = i
    · subst hj; simp [τ]
    · simp [τ, Function.update_of_ne hj]
  · funext j; simp only [τ, WState.seth_val, WState.setv_val, Function.update_apply]
    by_cases hjY : j = Y
    · subst hjY; simp [hYo, hY, Ne.symm hAY]
    · by_cases hjo : j = out
      · subst hjo; simp [hjY, hAo, Ne.symm hAo]
      · simp [hjY, hjo]

/-- The cell `head + J` := `[RV ≠ 0]`; `J` is kept (`Z`, `Y`, `T` scratch, `0` before and after). -/
def writeAt (i : Fin (ns + 1)) (J Z Y T RV : Fin nr) : WM ns nr :=
  .seq (addTo J Z T) (.seq (.whr Z (.seq (.dec Z) (.seq (.fwd i) (.inc Y))))
    (.seq (.ifr RV (.wr i true) (.wr i false)) (WM.rewind i Y)))

/-- **Writing a cell by an offset register** (paper lem:succinct-verifier, stage (3): the gate values on a tape). -/
theorem writeAt_spec (cap : ℕ) (i : Fin (ns + 1)) (J Z Y T RV : Fin nr) (hR : [J, Z, Y, T, RV].Nodup)
    (σ : WState ns nr) (hZ : σ.val Z = 0) (hY : σ.val Y = 0) (hT : σ.val T = 0) (hcap : σ.val J + 2 ≤ cap) :
    WExec cap (writeAt i J Z Y T RV) σ
      (σ.sets i (writeTapeBit (σ.st i) (σ.sh i + σ.val J) (decide (σ.val RV ≠ 0)))) (σ.val J * 40 + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hR
  obtain ⟨⟨hJZ, hJY, hJT, hJR⟩, ⟨hZY, hZT, hZR⟩, ⟨hYT, hYR⟩, hTR⟩ := hR
  set j := σ.val J with hj
  have e1 := addTo_spec cap J Z T hJZ hJT hZT σ hT (by omega) (by omega)
  set σ1 := σ.setv Z (σ.val Z + σ.val J) with hσ1
  have e2 := fwdBy_spec cap i Z Y hZY σ1 j (by simp [σ1, hZ, hj]) (by simp [σ1, Function.update_apply, Ne.symm hZY, hY])
    (by omega)
  set σ2 := ((σ1.setv Z 0).setv Y j).seth i (σ1.sh i + j) with hσ2
  have hRV : σ2.val RV = σ.val RV := by simp [σ2, σ1, Function.update_apply, Ne.symm hYR, Ne.symm hZR]
  have e3 : WExec cap (.ifr RV (.wr i true) (.wr i false)) σ2
      (σ2.sets i (writeTapeBit (σ2.st i) (σ2.sh i) (decide (σ.val RV ≠ 0)))) 2 := by
    by_cases hr : σ.val RV = 0
    · have := WExec.wr (cap := cap) i false σ2
      rw [show decide (σ.val RV ≠ 0) = false by simp [hr]]
      exact WExec.ifrF (by rw [hRV, hr]) this
    · have := WExec.wr (cap := cap) i true σ2
      rw [show decide (σ.val RV ≠ 0) = true by simp [hr]]
      exact WExec.ifrT (by rw [hRV]; exact hr) this
  have e4 := wrewind_spec cap i Y j (σ2.sets i (writeTapeBit (σ2.st i) (σ2.sh i) (decide (σ.val RV ≠ 0))))
    (by simp [σ2]) (by simp [σ2]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x; by_cases hx : x = i
    · subst hx; simp [σ2, σ1]
    · simp [σ2, σ1, Function.update_of_ne hx]
  · funext x; by_cases hx : x = i
    · subst hx; simp [σ2, σ1]
    · simp [σ2, σ1, Function.update_of_ne hx]
  · funext x; simp only [σ2, σ1, WState.seth_val, WState.setv_val, WState.sets_val, Function.update_apply]
    by_cases hxY : x = Y
    · subst hxY; simp [hY]
    · by_cases hxZ : x = Z
      · subst hxZ; simp [hxY, hZ]
      · simp [hxY, hxZ]

/-! ## Fields into registers -/

/-- One guarded field into `tgt` (guard flag cleared). -/
def fieldTo (i : Fin (ns + 1)) (R : FReg → Fin nr) (b tgt : Fin nr) : WM ns nr :=
  .seq (fieldW i R b) (.seq (WM.move (R .val) tgt) (WM.clear (R .zg)))

/-- One guarded field into `tgt`, the guard flag into `g`. -/
def fieldToG (i : Fin (ns + 1)) (R : FReg → Fin nr) (b tgt g : Fin nr) : WM ns nr :=
  .seq (fieldW i R b) (.seq (WM.move (R .val) tgt) (WM.move (R .zg) g))

/-- **A guarded field into a register, guard flag kept** (paper lem:succinct-verifier, stage (2)), on every stream
content: the head moves to `fieldEnd`, `CD = R .cd` grows by `2L + 1`, `tgt := fieldVal`, `g := [b < L]`. -/
theorem fieldToG_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (hR : Function.Injective R) (b tgt g : Fin nr)
    (hb : ∀ k, R k ≠ b) (ht : ∀ k, R k ≠ tgt) (hg : ∀ k, R k ≠ g) (htg : tgt ≠ g)
    (σ : WState ns nr) (h0 : ∀ k : FReg, k ≠ .cd → σ.val (R k) = 0) (htz : σ.val tgt = 0) (hgz : σ.val g = 0)
    (hcap : σ.val (R .cd) + 2 * ones (σ.st i) (σ.sh i) + 2 * σ.val b + 2 ^ (σ.val b + 1) + 4 ≤ cap) :
    WExec cap (fieldToG i R b tgt g) σ
      ((((σ.seth i (fieldEnd (σ.st i) (σ.sh i))).setv (R .cd) (σ.val (R .cd) + 2 * ones (σ.st i) (σ.sh i) + 1)).setv tgt
        (fieldVal (σ.st i) (σ.sh i) (σ.val b))).setv g (if σ.val b < ones (σ.st i) (σ.sh i) then 1 else 0))
      (fieldCost (ones (σ.st i) (σ.sh i)) (σ.val b) + 7 * 2 ^ σ.val b + 20) := by
  have e1 := fieldW_spec cap i R hR b hb σ (h0 .flag (by decide)) (h0 .cnt (by decide)) (h0 .pw (by decide))
    (h0 .tmp (by decide)) (h0 .gc (by decide)) (h0 .hc (by decide)) (h0 .zg (by decide))
    (by rw [h0 .val (by decide)]; omega)
  have h2z := h0 .val (by decide)
  have h7z := h0 .zg (by decide)
  have n27 : R .val ≠ R .zg := hR.ne (by decide)
  have n28 : R .val ≠ R .cd := hR.ne (by decide)
  have n78 : R .zg ≠ R .cd := hR.ne (by decide)
  set L := ones (σ.st i) (σ.sh i) with hL
  set fv := fieldVal (σ.st i) (σ.sh i) (σ.val b) with hfv
  set gv : ℕ := if σ.val b < L then 1 else 0 with hgv
  have hgv1 : gv ≤ 1 := by rw [hgv]; split_ifs <;> omega
  set σ1 := (((σ.seth i (fieldEnd (σ.st i) (σ.sh i))).setv (R .val) (σ.val (R .val) + fv)).setv (R .cd)
    (σ.val (R .cd) + 2 * L + 1)).setv (R .zg) gv with hσ1
  have hfvlt : fv < 2 ^ σ.val b := fieldVal_lt _ _ _
  have h2 : σ1.val (R .val) = fv := by simp [σ1, Function.update_apply, n27, n28, h2z]
  have htz1 : σ1.val tgt = 0 := by
    simp [σ1, Function.update_apply, Ne.symm (ht .val), Ne.symm (ht .cd), Ne.symm (ht .zg)]; exact htz
  have e2 := wmove_spec cap (R .val) tgt (ht .val) fv σ1 h2 (by omega) (by rw [htz1, h2]; omega)
  set σ2 := (σ1.setv (R .val) 0).setv tgt (σ1.val tgt + σ1.val (R .val)) with hσ2
  have h7 : σ2.val (R .zg) = gv := by simp [σ2, σ1, Function.update_apply, n27.symm, ht .zg]
  have hg2 : σ2.val g = 0 := by
    simp [σ2, σ1, Function.update_apply, Ne.symm (hg .val), Ne.symm (hg .cd), Ne.symm (hg .zg), htg.symm]; exact hgz
  have e3 := wmove_spec cap (R .zg) g (hg .zg) gv σ2 h7 (by omega) (by rw [hg2, h7]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · simp [σ2, σ1]
    · funext j
      simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hjg : j = g
      · subst hjg; simp [Ne.symm (hg .zg), Ne.symm (hg .val), Ne.symm (hg .cd), htg.symm, hgz, ht .zg, hR.eq_iff]
      · by_cases hj7 : j = R .zg
        · subst hj7; simp [hjg, n27.symm, n78, ht .zg, h7z]
        · by_cases hjt : j = tgt
          · subst hjt; simp [hjg, hj7, Ne.symm (ht .val), Ne.symm (ht .cd), htz, n27, n28, n78, h2z]
          · by_cases hj2 : j = R .val
            · subst hj2; simp [hjg, hj7, hjt, n28, n27, h2z]
            · by_cases hj8 : j = R .cd
              · subst hj8; simp [hjg, hj7, hjt, hj2]
              · simp [hjg, hj7, hjt, hj2, hj8]
  · omega

/-- **A guarded field into a register** (paper lem:succinct-verifier, stage (2)): as `fieldToG_spec`, the guard flag
cleared. -/
theorem fieldTo_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (hR : Function.Injective R) (b tgt : Fin nr)
    (hb : ∀ k, R k ≠ b) (ht : ∀ k, R k ≠ tgt)
    (σ : WState ns nr) (h0 : ∀ k : FReg, k ≠ .cd → σ.val (R k) = 0) (htz : σ.val tgt = 0)
    (hcap : σ.val (R .cd) + 2 * ones (σ.st i) (σ.sh i) + 2 * σ.val b + 2 ^ (σ.val b + 1) + 4 ≤ cap) :
    WExec cap (fieldTo i R b tgt) σ
      (((σ.seth i (fieldEnd (σ.st i) (σ.sh i))).setv (R .cd) (σ.val (R .cd) + 2 * ones (σ.st i) (σ.sh i) + 1)).setv tgt
        (fieldVal (σ.st i) (σ.sh i) (σ.val b)))
      (fieldCost (ones (σ.st i) (σ.sh i)) (σ.val b) + 7 * 2 ^ σ.val b + 20) := by
  have e1 := fieldW_spec cap i R hR b hb σ (h0 .flag (by decide)) (h0 .cnt (by decide)) (h0 .pw (by decide))
    (h0 .tmp (by decide)) (h0 .gc (by decide)) (h0 .hc (by decide)) (h0 .zg (by decide))
    (by rw [h0 .val (by decide)]; omega)
  have h2z := h0 .val (by decide)
  have h7z := h0 .zg (by decide)
  have n27 : R .val ≠ R .zg := hR.ne (by decide)
  have n28 : R .val ≠ R .cd := hR.ne (by decide)
  have n78 : R .zg ≠ R .cd := hR.ne (by decide)
  set L := ones (σ.st i) (σ.sh i) with hL
  set fv := fieldVal (σ.st i) (σ.sh i) (σ.val b) with hfv
  set gv : ℕ := if σ.val b < L then 1 else 0 with hgv
  have hgv1 : gv ≤ 1 := by rw [hgv]; split_ifs <;> omega
  set σ1 := (((σ.seth i (fieldEnd (σ.st i) (σ.sh i))).setv (R .val) (σ.val (R .val) + fv)).setv (R .cd)
    (σ.val (R .cd) + 2 * L + 1)).setv (R .zg) gv with hσ1
  have hfvlt : fv < 2 ^ σ.val b := fieldVal_lt _ _ _
  have h2 : σ1.val (R .val) = fv := by simp [σ1, Function.update_apply, n27, n28, h2z]
  have htz1 : σ1.val tgt = 0 := by
    simp [σ1, Function.update_apply, Ne.symm (ht .val), Ne.symm (ht .cd), Ne.symm (ht .zg)]; exact htz
  have e2 := wmove_spec cap (R .val) tgt (ht .val) fv σ1 h2 (by omega) (by rw [htz1, h2]; omega)
  set σ2 := (σ1.setv (R .val) 0).setv tgt (σ1.val tgt + σ1.val (R .val)) with hσ2
  have h7 : σ2.val (R .zg) = gv := by simp [σ2, σ1, Function.update_apply, n27.symm, ht .zg]
  have e3 := wclear_spec cap (R .zg) gv σ2 h7 (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · simp [σ2, σ1]
    · funext j
      simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hj7 : j = R .zg
      · subst hj7; simp [n27.symm, n78, ht .zg, h7z]
      · by_cases hjt : j = tgt
        · subst hjt; simp [hj7, Ne.symm (ht .val), Ne.symm (ht .cd), htz, n27, n28, n78, h2z]
        · by_cases hj2 : j = R .val
          · subst hj2; simp [hj7, hjt, n28, n27, h2z]
          · by_cases hj8 : j = R .cd
            · subst hj8; simp [hj7, hjt, hj2]
            · simp [hj7, hjt, hj2, hj8]
  · omega

end NearCubicGates.Close.Succinct
