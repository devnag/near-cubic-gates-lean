import Proof.Gates.CheckedPCPP.FrameIn

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.Glue

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp readNatM readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.SourceInterfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.NodeEmit NearCubicGates.Close.CheckedPCPP.DescW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Duplicating a framed word -/

/-- `o := frame w` from `s` holding `frame w ++ rest` at its head (`o` empty), `o` rewound (`P` counts, back to `0`). -/
def copyFrameW (s o : Fin (ns + 1)) (P : Fin nr) : WM ns nr :=
  .seq (copyMarks s o P) (.seq (emitC o P false) (WM.rewind o P))

theorem copyFrameW_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (P : Fin nr) (w pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ RepairOrdinary.frame w ++ rest) (hsh : σ.sh s = pre.length) (ho : σ.st o = [])
    (hoh : σ.sh o = 0) (hP : σ.val P = 0) (hcap : 2 * w.length + 2 ≤ cap) :
    WExec cap (copyFrameW s o P) σ ((σ.sets o (RepairOrdinary.frame w)).seth s (pre.length + 2 * w.length))
      (22 * w.length + 1 + 1 + 7 + 1 + (5 * (2 * w.length + 1) + 1)) := by
  have hos : o ≠ s := Ne.symm hso
  have e1 := copyMarks_spec cap s o hso P w pre (false :: rest) σ
    (by rw [hst, frame_eq_marks']; simp) (by rfl) hsh (by rw [ho, hoh]; rfl) (by rw [hP]; omega)
  set σ1 := (appendO σ o P (marks w)).seth s (pre.length + 2 * w.length) with hσ1
  have e2 := Codec.emitBit_spec cap o P false σ1 (by simp [hσ1, Function.update_of_ne hos, ho, hoh, marks_len'])
    (by simp [hσ1, hP, marks_len']; omega)
  have h7 : (appendO σ1 o P [false]).val P = 2 * w.length + 1 := by simp [hσ1, hP, marks_len']
  have e3 := wrewind_spec (cap := cap) o P (2 * w.length + 1) (appendO σ1 o P [false]) h7 (by rw [h7]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext x; by_cases hx : x = o
    · subst hx; simp [hσ1, Function.update_of_ne hos, hoh, marks_len']
    · by_cases hxs : x = s
      · subst hxs; simp [hσ1, Function.update_of_ne hx]
      · simp [hσ1, Function.update_of_ne hx, Function.update_of_ne hxs]
  · funext x; by_cases hx : x = o
    · subst hx; simp [hσ1, ho, frame_eq_marks']
    · simp [hσ1, Function.update_of_ne hx]
  · funext r; by_cases hr : r = P
    · subst hr; simp [hP]
    · simp [hσ1, Function.update_of_ne hr]
  · simp [hσ1]

/-! ## Reading the first natural number of a framed word -/

def readQW (DD QS : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (P2 T Rq f c p t : Fin nr) : WM ns nr :=
  .seq (Codec.copyNat true DD QS R) (.seq (addW (R 7) P2 T) (.seq (WM.rewind DD (R 7)) (.seq (WM.rewind QS P2)
    (readNatM true QS f c Rq p t))))

/-- The cost bound of `readQW` for a value at most `X`. -/
def readQCost (X : ℕ) : ℕ := 60 * (2 * X + 3) + 60 + 1 + (18 * (2 * (2 * X + 3)) + 3) + 1 +
  (5 * (2 * (2 * X + 3)) + 1) + 1 + (5 * (2 * (2 * X + 3)) + 1) + 1 + DescW.readCost X

theorem readQW_spec (DD QS : Fin (ns + 1)) (hDQ : DD ≠ QS) (R : Fin 8 ↪ Fin nr) {P2 T Rq f c p t : Fin nr}
    (hregs : [R 1, R 2, R 7, P2, T, Rq, f, c, p, t].Nodup) (x : ℕ) (w' : List Bool) (σ : WState ns nr)
    (hst : σ.st DD = RepairOrdinary.frame (natWord x ++ w')) (hsh : σ.sh DD = 0) (hQ : σ.st QS = [])
    (hQh : σ.sh QS = 0) (hz : ∀ r ∈ [R 1, R 2, R 7, P2, T, Rq, f, c, p, t], σ.val r = 0) (X : ℕ) (hX : x ≤ X)
    (hcap : 8 * X + 20 ≤ cap) :
    ∃ τ, WExec cap (readQW DD QS R P2 T Rq f c p t) σ τ (readQCost X) ∧ τ.st DD = σ.st DD ∧ τ.sh DD = 0 ∧
      τ.val Rq = x ∧ SameExcept σ τ [QS] [Rq] := by
  have hr := hregs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hr
  obtain ⟨⟨r12, r17, r1P, r1T, r1q, r1f, r1c, r1p, r1t⟩, ⟨r27, r2P, r2T, r2q, r2f, r2c, r2p, r2t⟩,
    ⟨r7P, r7T, r7q, r7f, r7c, r7p, r7t⟩, ⟨rPT, rPq, rPf, rPc, rPp, rPt⟩, ⟨rTq, rTf, rTc, rTp, rTt⟩,
    ⟨rqf, rqc, rqp, rqt⟩, ⟨rfc, rfp, rft⟩, ⟨rcp, rct⟩, rpt⟩ := hr
  have z : ∀ r ∈ [R 1, R 2, R 7, P2, T, Rq, f, c, p, t], σ.val r = 0 := hz
  have hQD : QS ≠ DD := Ne.symm hDQ
  have hlx := ChecksW.natWord_len x
  have hbx := natBitLength_le x
  -- copy natWord x to QS
  have e1 := Codec.copyNat_spec cap true DD QS hDQ R x [] (marks w' ++ [false]) σ
    (by rw [hst, frame_eq_marks', NodeEmit.marks_append]; simp [enc_true]) (by rw [hsh]; rfl)
    (by rw [hQ, hQh]; rfl) (z _ (by simp)) (z _ (by simp)) (by rw [z _ (by simp)]; omega)
  simp only [stp, if_true, List.length_nil, Nat.zero_add] at e1
  set σ1 := (appendO σ QS (R 7) (marks (natWord x))).seth DD (2 * (natWord x).length) with hσ1
  have h17 : σ1.val (R 7) = 2 * (natWord x).length := by simp [hσ1, z (R 7) (by simp), marks_len']
  have e2 := addW_spec cap (A := R 7) (W := P2) (T := T) r7P r7T rPT σ1
    (by simp [hσ1, Function.update_of_ne rTq, z T (by simp), Function.update_of_ne (Ne.symm r7T)])
    (by simp [hσ1, Function.update_of_ne (Ne.symm r7P), z P2 (by simp), z (R 7) (by simp), marks_len']; omega)
  have hP2 : σ1.val P2 + σ1.val (R 7) = 2 * (natWord x).length := by
    simp [hσ1, Function.update_of_ne (Ne.symm r7P), z P2 (by simp), z (R 7) (by simp), marks_len']
  rw [hP2] at e2
  set σ2 := σ1.setv P2 (2 * (natWord x).length) with hσ2
  have e3 := wrewind_spec (cap := cap) DD (R 7) (2 * (natWord x).length) σ2
    (by simp [hσ2, Function.update_of_ne r7P, h17]) (by simp [hσ2, Function.update_of_ne r7P, h17]; omega)
  set σ3 := (σ2.setv (R 7) 0).seth DD (σ2.sh DD - 2 * (natWord x).length) with hσ3
  have e4 := wrewind_spec (cap := cap) QS P2 (2 * (natWord x).length) σ3
    (by simp [hσ3, hσ2, Function.update_of_ne (Ne.symm r7P)]) (by simp [hσ3, hσ2, Function.update_of_ne (Ne.symm r7P)]; omega)
  set σ4 := (σ3.setv P2 0).seth QS (σ3.sh QS - 2 * (natWord x).length) with hσ4
  have e5 := readNatM_spec cap true QS f c Rq p t rfc (Ne.symm rqf) rfp rft (Ne.symm rqc) rcp rct (Ne.symm rqp) rpt
    rqt x [] [] σ4 (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hQD, hQ, enc_true])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hQD, hQh, marks_len'])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPf), Function.update_of_ne (Ne.symm r7f),
      z f (by simp)])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPc), Function.update_of_ne (Ne.symm r7c),
      z c (by simp)])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPp), Function.update_of_ne (Ne.symm r7p),
      z p (by simp)])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPt), Function.update_of_ne (Ne.symm r7t),
      z t (by simp)])
    (by
      simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPq), Function.update_of_ne (Ne.symm r7q),
        z Rq (by simp)]
      have := DescW.pow_bitlen_le x; rw [pow_succ]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, ?_, ?_, ?_, ?_⟩
  · unfold readQCost
    have : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ DescW.readCost X := by
      unfold DescW.readCost
      have := DescW.pow_bitlen_le x
      exact Nat.mul_le_mul (by omega) (by omega)
    omega
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hDQ]
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hDQ, hsh]
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm rPq), Function.update_of_ne (Ne.symm r7q),
      z Rq (by simp)]
  · refine ⟨fun y hy => ?_, fun r hr => ?_, by simp [hσ4, hσ3, hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      by_cases hyD : y = DD
      · subst hyD; simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hDQ, hsh]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy, Function.update_of_ne hyD]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      by_cases h7 : r = R 7
      · rw [h7]; simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne r7P, Function.update_of_ne r7q, z (R 7) (by simp)]
      · by_cases hP : r = P2
        · rw [hP]; simp [hσ4, hσ3, Function.update_of_ne rPq, z P2 (by simp)]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr, Function.update_of_ne h7, Function.update_of_ne hP]

/-- Copy the first two frames of `WO` to `PO` and `RO`. -/
def headerW (WO PO RO : Fin (ns + 1)) (P : Fin nr) : WM ns nr :=
  .seq (copyMarks WO PO P) (.seq (emitC PO P false) (.seq (.fwd WO) (.seq (copyMarks WO RO P) (emitC RO P false))))

theorem headerW_spec (WO PO RO : Fin (ns + 1)) (hS : [WO, PO, RO].Nodup) (P : Fin nr) (a b rest : List Bool)
    (σ : WState ns nr) (hst : σ.st WO = RepairOrdinary.frame a ++ RepairOrdinary.frame b ++ rest) (hsh : σ.sh WO = 0)
    (hP : σ.st PO = []) (hPh : σ.sh PO = 0) (hR : σ.st RO = []) (hRh : σ.sh RO = 0)
    (hcap : σ.val P + 2 * a.length + 2 * b.length + 2 ≤ cap) :
    ∃ τ, WExec cap (headerW WO PO RO P) σ τ (22 * a.length + 22 * b.length + 30) ∧
      τ.st PO = RepairOrdinary.frame a ∧ τ.st RO = RepairOrdinary.frame b ∧ τ.st WO = σ.st WO ∧
      SameExcept σ τ [WO, PO, RO] [P] := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
  obtain ⟨⟨hWP, hWR⟩, hPR, -⟩ := hS
  have hPW : PO ≠ WO := Ne.symm hWP
  have hRW : RO ≠ WO := Ne.symm hWR
  have hRP : RO ≠ PO := Ne.symm hPR
  have e1 := copyMarks_spec cap WO PO hWP P a [] (false :: (RepairOrdinary.frame b ++ rest)) σ
    (by rw [hst, frame_eq_marks' a]; simp) rfl (by rw [hsh]; rfl) (by rw [hP, hPh]; rfl) (by omega)
  set σ1 := (appendO σ PO P (marks a)).seth WO (0 + 2 * a.length) with hσ1
  have e2 := Codec.emitBit_spec cap PO P false σ1 (by simp [hσ1, Function.update_of_ne hPW, hP, hPh, marks_len'])
    (by simp [hσ1, marks_len']; omega)
  set σ2 := appendO σ1 PO P [false] with hσ2
  have e3 := WExec.fwd (cap := cap) WO σ2
  set σ3 := σ2.seth WO (σ2.sh WO + 1) with hσ3
  have h3 : σ3.sh WO = (RepairOrdinary.frame a).length := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hWP, FrameIn.frame_len]
  have e4 := copyMarks_spec cap WO RO hWR P b (RepairOrdinary.frame a) (false :: rest) σ3
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hWP, hst, frame_eq_marks' b])
    rfl h3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hRW, Function.update_of_ne hRP, hR, hRh])
    (by simp [hσ3, hσ2, hσ1, marks_len']; omega)
  set σ4 := (appendO σ3 RO P (marks b)).seth WO ((RepairOrdinary.frame a).length + 2 * b.length) with hσ4
  have e5 := Codec.emitBit_spec cap RO P false σ4
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRW, Function.update_of_ne hRP, hR, hRh, marks_len'])
    (by simp [hσ4, hσ3, hσ2, hσ1, marks_len']; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega), ?_, ?_, ?_,
    ⟨fun y hy => ?_, fun r hr => ?_, by simp [hσ4, hσ3, hσ2, hσ1]⟩⟩
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hPR, Function.update_of_ne hPW, hP, frame_eq_marks']
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRW, Function.update_of_ne hRP, hR, frame_eq_marks']
  · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hWR, Function.update_of_ne hWP]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr]

end NearCubicGates.Close.CheckedPCPP.Glue
