import Proof.Gates.CounterMachine.TabCallSplit
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

/-- One pair of a frame: two cells forward, counted. -/
def skipPair (S : Fin (ns + 1)) (D : Fin nr) : WM ns nr := .seq (.fwd S) (.seq (.fwd S) (.seq (.inc D) (.inc D)))

/-- Skip one frame (head at its start), counting the cells passed in `D`. -/
def skipFr (S : Fin (ns + 1)) (D : Fin nr) : WM ns nr := .seq (.whs S (skipPair S D)) (.seq (.fwd S) (.inc D))

theorem skipPairs_spec (S : Fin (ns + 1)) (D : Fin nr) (rest : List Bool) :
    ∀ (x pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ RepairOrdinary.frame x ++ rest →
      σ.sh S = pre.length → σ.val D + 2 * x.length < cap →
      WExec cap (.whs S (skipPair S D)) σ ((σ.seth S (pre.length + 2 * x.length)).setv D (σ.val D + 2 * x.length))
        (13 * x.length + 1)
  | [], pre, σ, hst, hsh, _ => by
    have hb : wbit σ S = false := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e : (σ.seth S (pre.length + 2 * ([] : List Bool).length)).setv D (σ.val D + 2 * ([] : List Bool).length) =
        σ := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, ← hsh, wseth_same, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp)
  | b :: x, pre, σ, hst, hsh, hc => by
    have hb : wbit σ S = true := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [RepairOrdinary.frame, List.getD_append_right]
    have e1 := WExec.fwd (cap := cap) S σ
    set σ1 := σ.seth S (σ.sh S + 1) with hσ1
    have e2 := WExec.fwd (cap := cap) S σ1
    set σ2 := σ1.seth S (σ1.sh S + 1) with hσ2
    have e3 := WExec.inc (cap := cap) D σ2 (by simp [hσ2, hσ1]; simp at hc; omega)
    set σ3 := σ2.setv D (σ2.val D + 1) with hσ3
    have e4 := WExec.inc (cap := cap) D σ3 (by simp [hσ3, hσ2, hσ1]; simp at hc; omega)
    set σ4 := σ3.setv D (σ3.val D + 1) with hσ4
    have ih := skipPairs_spec S D rest x (pre ++ [true, b]) σ4
      (by simp [hσ4, hσ3, hσ2, hσ1, hst, RepairOrdinary.frame])
      (by simp [hσ4, hσ3, hσ2, hσ1, hsh])
      (by simp [hσ4, hσ3, hσ2, hσ1]; simp at hc; omega)
    have e := WExec.whsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih
    refine WExec.cast cap e ?_ (by simp; omega)
    apply WState.eq
    · funext y; by_cases hy : y = S
      · subst hy; simp [hσ4, hσ3, hσ2, hσ1]; omega
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy]
    · rfl
    · funext r; by_cases hr : r = D
      · subst hr; simp [hσ4, hσ3, hσ2, hσ1]; omega
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr]
    · rfl

theorem skipFr_spec (S : Fin (ns + 1)) (D : Fin nr) (x pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st S = pre ++ RepairOrdinary.frame x ++ rest) (hsh : σ.sh S = pre.length)
    (hc : σ.val D + (RepairOrdinary.frame x).length < cap) :
    WExec cap (skipFr S D) σ ((σ.seth S (pre.length + (RepairOrdinary.frame x).length)).setv D
      (σ.val D + (RepairOrdinary.frame x).length)) (13 * x.length + 7) := by
  have hfl : (RepairOrdinary.frame x).length = 2 * x.length + 1 := by rw [frame_eq_marks]; simp [Codec.marks_length]
  rw [hfl] at hc ⊢
  have e1 := skipPairs_spec cap S D rest x pre σ hst hsh (by omega)
  set σ1 := (σ.seth S (pre.length + 2 * x.length)).setv D (σ.val D + 2 * x.length) with hσ1
  have e2 := WExec.fwd (cap := cap) S σ1
  have e3 := WExec.inc (cap := cap) D (σ1.seth S (σ1.sh S + 1)) (by simp [hσ1]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext y; by_cases hy : y = S
    · subst hy; simp [hσ1]; omega
    · simp [hσ1, Function.update_of_ne hy]
  · rfl
  · funext r; by_cases hr : r = D
    · subst hr; simp [hσ1]; omega
    · simp [hσ1, Function.update_of_ne hr]
  · rfl

/-- Skip `I` frames (`I` the loop counter). -/
def skipFrs (S : Fin (ns + 1)) (I D : Fin nr) : WM ns nr := .whr I (.seq (.dec I) (skipFr S D))

theorem skipFrs_spec (S : Fin (ns + 1)) (I D : Fin nr) (hID : I ≠ D) (rest : List Bool) :
    ∀ (ws : List (List Bool)) (pre : List Bool) (σ : WState ns nr),
      σ.st S = pre ++ ws.flatMap RepairOrdinary.frame ++ rest → σ.sh S = pre.length → σ.val I = ws.length →
      σ.val D + (ws.flatMap RepairOrdinary.frame).length < cap → ws.length ≤ cap →
      WExec cap (skipFrs S I D) σ (((σ.seth S (pre.length + (ws.flatMap RepairOrdinary.frame).length)).setv D
        (σ.val D + (ws.flatMap RepairOrdinary.frame).length)).setv I 0)
        (11 * (ws.flatMap RepairOrdinary.frame).length + 1)
  | [], pre, σ, _, hsh, hI, _, _ => by
    have e : ((σ.seth S (pre.length + (([] : List (List Bool)).flatMap RepairOrdinary.frame).length)).setv D
        (σ.val D + (([] : List (List Bool)).flatMap RepairOrdinary.frame).length)).setv I 0 = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hsh, wseth_same, wsetv_same]
      rw [show (0 : ℕ) = σ.val I by simpa using hI.symm, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hI)) (by simp)
  | w :: ws, pre, σ, hst, hsh, hI, hc, hlen => by
    have hfl : (RepairOrdinary.frame w).length = 2 * w.length + 1 := by rw [frame_eq_marks]; simp [Codec.marks_length]
    have hL : ((w :: ws).flatMap RepairOrdinary.frame).length =
        (RepairOrdinary.frame w).length + (ws.flatMap RepairOrdinary.frame).length := by simp
    have e1 := WExec.dec (cap := cap) I σ (by rw [hI]; exact hlen)
    set σ1 := σ.setv I (σ.val I - 1) with hσ1
    have e2 := skipFr_spec cap S D w pre (ws.flatMap RepairOrdinary.frame ++ rest) σ1
      (by simp [hσ1, hst, List.append_assoc]) (by simp [hσ1, hsh])
      (by simp [hσ1, Function.update_of_ne hID.symm]; rw [hL] at hc; omega)
    set σ2 := (σ1.seth S (pre.length + (RepairOrdinary.frame w).length)).setv D
      (σ1.val D + (RepairOrdinary.frame w).length) with hσ2
    have hv2 : σ2.val D = σ.val D + (RepairOrdinary.frame w).length := by
      simp only [hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_self]
      rw [Function.update_of_ne hID.symm]
    have ih := skipFrs_spec S I D hID rest ws (pre ++ RepairOrdinary.frame w) σ2
      (by simp [hσ2, hσ1, hst, List.append_assoc]) (by simp [hσ2])
      (by simp [hσ2, hσ1, Function.update_of_ne hID, hI])
      (by rw [hv2]; rw [hL] at hc; omega)
      (by simp at hlen; omega)
    have e := WExec.whrT (by rw [hI]; simp) (WExec.seq e1 e2) ih
    refine WExec.cast cap e ?_ (by rw [hL, hfl] at *; omega)
    apply WState.eq
    · funext y; by_cases hy : y = S
      · subst hy; simp [hσ2, hσ1, hL]; omega
      · simp [hσ2, hσ1, Function.update_of_ne hy]
    · rfl
    · funext r
      by_cases hr : r = I
      · subst hr; simp [hσ2, hσ1, Function.update_of_ne hID]
      · by_cases hr2 : r = D
        · subst hr2; simp [hσ2, hσ1, Function.update_of_ne hr, Function.update_of_ne hID.symm, hL]; omega
        · simp [hσ2, hσ1, Function.update_of_ne hr, Function.update_of_ne hr2]
    · rfl

def selPfx {ns nr : ℕ} (POUT PFX : Fin (ns + 1)) (I : Fin nr) (U : Fin 4 ↪ Fin nr) : WM ns nr :=
  .seq (skipFrs POUT I (U 0)) (.seq (.whs POUT (copyPairW POUT PFX (U 1))) (.seq (emitC PFX (U 1) false)
    (.seq (.fwd POUT) (.seq (copyR (U 1) (U 0) (U 2)) (.seq (WM.rewind PFX (U 1)) (WM.rewind POUT (U 0)))))))

theorem flatMap_split (ws : List (List Bool)) (idx : ℕ) (h : idx < ws.length) :
    ws.flatMap RepairOrdinary.frame = (ws.take idx).flatMap RepairOrdinary.frame ++ RepairOrdinary.frame ws[idx] ++
      (ws.drop (idx + 1)).flatMap RepairOrdinary.frame := by
  have e := List.take_append_drop idx ws
  rw [List.drop_eq_getElem_cons h] at e
  calc ws.flatMap RepairOrdinary.frame =
        (List.take idx ws ++ ws[idx] :: List.drop (idx + 1) ws).flatMap RepairOrdinary.frame := by rw [e]
    _ = _ := by rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem selPfx_spec : SelSpec selPfx := by
  intro ns nr cap POUT PFX I U σ ws rest idx hPP hUI hst hsh h hP hPh hI hU hcap
  have hU01 : U 0 ≠ U 1 := U.injective.ne (by decide)
  have hU02 : U 0 ≠ U 2 := U.injective.ne (by decide)
  have hU12 : U 1 ≠ U 2 := U.injective.ne (by decide)
  set A := ((ws.take idx).flatMap RepairOrdinary.frame).length with hA
  have hsplit := flatMap_split ws idx h
  generalize hx : ws[idx] = x at hsplit ⊢
  have hfl : (RepairOrdinary.frame x).length = 2 * x.length + 1 := by rw [frame_eq_marks]; simp [Codec.marks_length]
  have hLen : (ws.flatMap RepairOrdinary.frame).length = A + (RepairOrdinary.frame x).length +
      ((ws.drop (idx + 1)).flatMap RepairOrdinary.frame).length := by
    rw [hsplit]; simp [hA]; omega
  have htl : (ws.take idx).length = idx := by simp; omega
  have hidxL : idx ≤ A := by
    have : ∀ l : List (List Bool), l.length ≤ (l.flatMap RepairOrdinary.frame).length := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, frame_length]; omega
    have := this (ws.take idx); omega
  -- 1. skip `idx` frames
  have e1 := skipFrs_spec cap POUT I (U 0) (hUI 0).symm
    (RepairOrdinary.frame x ++ (ws.drop (idx + 1)).flatMap RepairOrdinary.frame ++ rest) (ws.take idx) [] σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) (by simpa using hsh) (by rw [hI, htl])
    (by rw [hU 0]; omega) (by omega)
  set σ1 := ((σ.seth POUT (([] : List Bool).length + A)).setv (U 0) (σ.val (U 0) + A)).setv I 0 with hσ1
  -- 2. copy the frame's pairs
  have e2 := copyFrame_loop cap POUT PFX hPP (U 1) ((ws.drop (idx + 1)).flatMap RepairOrdinary.frame ++ rest) x
    ((ws.take idx).flatMap RepairOrdinary.frame) σ1
    (by simp [hσ1, hst, hsplit, List.append_assoc]) (by simp [hσ1, hA])
    (by simp [hσ1, Function.update_of_ne hPP.symm, hP, hPh])
    (by simp [hσ1, Function.update_of_ne (hUI 1), Function.update_of_ne hU01.symm, hU 1]; omega)
  set σ2 := (appendO σ1 PFX (U 1) (marks x)).seth POUT (((ws.take idx).flatMap RepairOrdinary.frame).length +
    2 * x.length) with hσ2
  have hU0I : U 0 ≠ I := hUI 0
  have hU1I : U 1 ≠ I := hUI 1
  have hU2I : U 2 ≠ I := hUI 2
  have v2U1 : σ2.val (U 1) = 2 * x.length := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hU1I, Function.update_of_ne hU01.symm, hU 1, Codec.marks_length]
  have v2U0 : σ2.val (U 0) = A := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hU01, Function.update_of_ne hU0I, hU 0]
  have v2U2 : σ2.val (U 2) = 0 := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hU12.symm, Function.update_of_ne hU02.symm,
      Function.update_of_ne hU2I, hU 2]
  have s2P : σ2.st PFX = marks x := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hPP.symm, hP]
  have h2P : σ2.sh PFX = 2 * x.length := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hPP.symm, hPh, Codec.marks_length]
  have h2O : σ2.sh POUT = A + 2 * x.length := by
    rw [hσ2]; simp only [WState.seth_sh, Function.update_self]; rw [hA]
  -- 3. the closing `false`
  have e3 := emitC_spec (cap := cap) PFX (U 1) false σ2 (by rw [s2P, h2P, Codec.marks_length])
    (by rw [v2U1]; omega)
  set σ3 := ((σ2.sets PFX (σ2.st PFX ++ [false])).seth PFX (σ2.sh PFX + 1)).setv (U 1) (σ2.val (U 1) + 1) with hσ3
  -- 4. past it on the source
  have e4 := WExec.fwd (cap := cap) POUT σ3
  set σ4 := σ3.seth POUT (σ3.sh POUT + 1) with hσ4
  have v4U1 : σ4.val (U 1) = 2 * x.length + 1 := by simp [hσ4, hσ3, v2U1]
  have v4U0 : σ4.val (U 0) = A := by simp [hσ4, hσ3, Function.update_of_ne hU01, v2U0]
  have v4U2 : σ4.val (U 2) = 0 := by simp [hσ4, hσ3, Function.update_of_ne hU12.symm, v2U2]
  -- 5. `U 0 += U 1`
  have e5 := copyR_spec (cap := cap) (v := U 1) (d := U 0) (t := U 2) hU01.symm hU12 hU02 σ4 v4U2
    (by rw [v4U0, v4U1]; omega)
  rw [v4U1, v4U0] at e5
  set σ5 := σ4.setv (U 0) (A + (2 * x.length + 1)) with hσ5
  -- 6. rewind `PFX`
  have e6 := wrewind_spec (cap := cap) PFX (U 1) (2 * x.length + 1) σ5
    (by simp [hσ5, Function.update_of_ne hU01.symm, v4U1]) (by simp [hσ5, Function.update_of_ne hU01.symm, v4U1]; omega)
  set σ6 := (σ5.setv (U 1) 0).seth PFX (σ5.sh PFX - (2 * x.length + 1)) with hσ6
  -- 7. rewind the source
  have e7 := wrewind_spec (cap := cap) POUT (U 0) (A + (2 * x.length + 1)) σ6
    (by simp [hσ6, hσ5, Function.update_of_ne hU01]) (by simp [hσ6, hσ5, Function.update_of_ne hU01]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ (by rw [hLen, hfl]; omega)
  apply WState.eq
  · funext y
    by_cases hyO : y = POUT
    · subst hyO; simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne hPP, h2O, hsh]
    · by_cases hyP : y = PFX
      · subst hyP; simp [hσ6, hσ5, hσ4, hσ3, Function.update_of_ne hPP.symm, h2P, hPh]
      · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyO, Function.update_of_ne hyP]
  · funext y
    by_cases hyP : y = PFX
    · subst hyP; simp [hσ6, hσ5, hσ4, hσ3, s2P, frame_eq_marks]
    · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hyP]
  · funext r
    by_cases r0 : r = U 0
    · subst r0; simp [Function.update_of_ne hU0I, hU 0]
    · by_cases r1 : r = U 1
      · subst r1; simp [hσ6, Function.update_of_ne hU01.symm, Function.update_of_ne hU1I, hU 1]
      · by_cases rI : r = I
        · subst rI; simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hU0I.symm,
            Function.update_of_ne hU1I.symm]
        · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne r0, Function.update_of_ne r1,
            Function.update_of_ne rI]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, appendO]

end NearCubicGates.Close.CounterMachine
