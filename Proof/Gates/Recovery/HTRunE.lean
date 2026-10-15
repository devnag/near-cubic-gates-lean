import Proof.Gates.Recovery.HTRunK

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

theorem marks_append' (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by simp [marks]

theorem marks_marks (u : List Bool) : marks (marks u) = u.flatMap fun b => marks [true, b] := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [show marks (a :: u) = true :: a :: marks u from rfl,
      show marks (true :: a :: marks u) = true :: true :: true :: a :: marks (marks u) from rfl, ih]
    rfl

theorem msg_eq (r : ℕ) (u : List Bool) :
    (r.bits.flatMap fun b => marks [true, b]) ++ marks [false] ++ ((marks u).flatMap fun c => [true, c]) ++
      marks [false] ++ [false] = frame (frame r.bits ++ frame u) := by
  rw [frame_marks (frame r.bits ++ frame u), marks_append', frame_marks, frame_marks, marks_append', marks_append',
    marks_marks, marks_marks]
  have : ((marks u).flatMap fun c => [true, c]) = u.flatMap fun b => marks [true, b] := by
    rw [← marks_marks]; rfl
  rw [this]; simp [List.append_assoc]

theorem marks_len (u : List Bool) : (marks u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [marks] at ih ⊢; omega

/-- The encoder input as written. -/
def eiWord (r : ℕ) (u : List Bool) : List Bool := frame (frame r.bits ++ frame u)

theorem eiWord_len (r : ℕ) (u : List Bool) : (eiWord r u).length = 4 * r.bits.length + 4 * u.length + 5 := by
  simp [eiWord, LitDecode.frame_length']; ring

/-- **The encoder input.** -/
theorem ei_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) (Rv : ℕ) (u v : List Bool) (hu : u.length = Rv)
    (hR : σ.val rR = Rv) (hP2 : σ.st (P2 tK tE tH) = frame (u ++ v)) (hP2h : σ.sh (P2 tK tE tH) = 0)
    (hEI : σ.st (EI tK tE tH) = []) (hEIh : σ.sh (EI tK tE tH) = 0)
    (hz : ∀ r ∈ [rRc, rH, rB, rK, rT, opEI, scP2], σ.val r = 0) (hcap : 8 * Rv + 8 ≤ cap) :
    WXExec cap (eiW tK tE tH) σ (σ.sets (EI tK tE tH) (eiWord Rv u)) (100 * (Rv + 1) * (Rv + 1)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zRc, zH, zB, zK, zT, zOP, zSC⟩ := hz
  have hbl := LitDecode.bits_len_le Rv
  have dEP : P2 tK tE tH ≠ EI tK tE tH := by hdst
  have dPE := Ne.symm dEP
  -- 1. rRc := R
  have x1 := addR_spec cap (A := rR) (B := rRc) (T := rT) (by decide) (by decide) (by decide) σ zT (by omega)
  obtain ⟨s1, hs1, e1⟩ := named x1
  -- 2. the bits of R
  have x2 := bitsQ_exec (cap := cap) (X := rRc) (H := rH) (B := rB) (OP := opEI) (dst := EI tK tE tH) (by decide)
    Rv (by omega) Rv s1 le_rfl (by simp (config := { decide := true }) [hs1, zRc, hR])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zH])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zB])
    (by rw [hs1]; simp [hEI, hEIh]) (by simp (config := { decide := true }) [hs1, Function.update_apply, zOP]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  set U1 := Rv.bits.flatMap fun b => marks [true, b] with hU1
  have hU1l : U1.length = 4 * Rv.bits.length := by
    rw [hU1]; clear hU1; induction Rv.bits with
    | nil => rfl
    | cons a l ih => simp [marks] at ih ⊢; omega
  -- 3. the inner end marker
  have x3 := Codec.emitMarks_spec cap (EI tK tE tH) opEI [false] s2 (by simp [hs2, hs1, appendO, hEI, hEIh])
    (by simp (config := { decide := true }) [hs2, hs1, appendO, Function.update_apply, zOP]; omega)
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.wm x3)
  -- 4–5. rK := 2R
  have x4 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) s3
    (by simp (config := { decide := true }) [hs3, hs2, hs1, appendO, Function.update_apply, zT])
    (by simp (config := { decide := true }) [hs3, hs2, hs1, appendO, Function.update_apply, zK, hR]; omega)
  obtain ⟨s4, hs4, e4⟩ := named x4
  have x5 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) s4
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, appendO, Function.update_apply, zT])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, appendO, Function.update_apply, zK, hR]; omega)
  obtain ⟨s5, hs5, e5⟩ := named x5
  have hK5 : s5.val rK = (marks u).length := by
    simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, appendO, Function.update_apply, zK, hR, marks_len,
      hu]; omega
  have hP25 : s5.st (P2 tK tE tH) = [] ++ marks u ++ (marks v ++ [false]) := by
    simp [hs5, hs4, hs3, hs2, hs1, appendO, Function.update_apply, dPE, dEP, hP2, frame_marks, marks_append']
  -- 6. the marked cells of x, re-marked
  set W1 := U1 ++ marks [false] with hW1
  have hEI5 : s5.st (EI tK tE tH) = W1 := by simp [hs5, hs4, hs3, hs2, hs1, appendO, hEI, hW1]
  have hEIh5 : s5.sh (EI tK tE tH) = W1.length := by simp [hs5, hs4, hs3, hs2, hs1, appendO, hEIh, hW1]
  have hOP5 : s5.val opEI = W1.length := by
    simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, appendO, Function.update_apply, zOP, hW1]
  have hP2h5 : s5.sh (P2 tK tE tH) = ([] : List Bool).length := by
    simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, appendO, Function.update_apply, dPE, dEP, hP2h]
  have hOc5 : s5.val opEI + ((marks u).flatMap fun b => [true, b]).length ≤ cap := by
    rw [hOP5, hW1]; simp [hU1l, marks_len, marks]; omega
  have hSC5 : s5.val scP2 + (marks u).length < cap + 1 := by
    simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, appendO, Function.update_apply, zSC, marks_len]
    omega
  have x6 := cntLoop_spec (cap := cap) (src := P2 tK tE tH) (dst := EI tK tE tH) (OP := opEI) (SC := scP2)
    (K := rK) dEP (by decide) (by decide) (by decide) (emits_pair cap) (marks v ++ [false]) (marks u) [] s5 hP25
    hP2h5 (by rw [hEI5, hEIh5]) hK5 (by rw [marks_len]; omega) hOc5 hSC5
  obtain ⟨s6, hs6, e6⟩ := named (WXExec.wm x6)
  set Wx := (marks u).flatMap fun b => [true, b] with hWx
  have hWxl : Wx.length = 4 * u.length := by
    rw [hWx]; clear hWx; rw [show ((marks u).flatMap fun b => [true, b]) = marks (marks u) from rfl, marks_len,
      marks_len]; ring
  have hEI6 : s6.st (EI tK tE tH) = W1 ++ Wx := by
    rw [hs6]; simp only [WState.setv_st]; rw [adv_st_dst, hEI5]
  have hEIh6 : s6.sh (EI tK tE tH) = W1.length + Wx.length := by
    rw [hs6]; simp only [WState.setv_sh]; rw [adv_sh_dst dEP, hEIh5]
  have hOP6 : s6.val opEI = W1.length + Wx.length := by
    rw [hs6]; simp only [WState.setv_val]
    rw [Function.update_of_ne (show opEI ≠ rK by decide), adv_val_OP (show opEI ≠ scP2 by decide), hOP5]
  -- 7–8. the outer end markers
  have x7 := Codec.emitMarks_spec cap (EI tK tE tH) opEI [false] s6 (by rw [hEI6, hEIh6]; simp)
    (by rw [hOP6]; simp [hU1l, hWxl, hW1, marks] <;> omega)
  obtain ⟨s7, hs7, e7⟩ := named (WXExec.wm x7)
  have x8 := Codec.emitBit_spec cap (EI tK tE tH) opEI false s7 (by rw [hs7]; simp [appendO, hEI6, hEIh6] <;> omega)
    (by rw [hs7]; simp [appendO, hOP6, hU1l, hWxl, hW1, marks] <;> omega)
  obtain ⟨s8, hs8, e8⟩ := named (WXExec.wm x8)
  have hOP8 : s8.val opEI = W1.length + Wx.length + 3 := by
    rw [hs8, hs7]; simp [appendO, hOP6, marks] <;> omega
  have hEI8 : s8.st (EI tK tE tH) = eiWord Rv u := by
    rw [hs8, hs7]; simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [hEI6, eiWord, ← msg_eq]
  have hEIh8 : s8.sh (EI tK tE tH) = W1.length + Wx.length + 3 := by
    rw [hs8, hs7]; simp [appendO, hEIh6, marks] <;> omega
  -- 9–10. rewind
  have x9 := wrewind_spec (cap := cap) (EI tK tE tH) opEI (W1.length + Wx.length + 3) s8 hOP8
    (by rw [hOP8]; simp [hU1l, hWxl, hW1, marks] <;> omega)
  obtain ⟨s9, hs9, e9⟩ := named (WXExec.wm x9)
  have hSC9 : s9.val scP2 = (marks u).length := by
    simp (config := { decide := true }) [hs9, hs8, hs7, hs6, adv, appendO, Function.update_apply, hs5, hs4, hs3, hs2,
      hs1, zSC]
  have x10 := wrewind_spec (cap := cap) (P2 tK tE tH) scP2 (marks u).length s9 hSC9 (by rw [hSC9, marks_len]; omega)
  obtain ⟨s10, hs10, e10⟩ := named (WXExec.wm x10)
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 e10))))))))
  have dEO : ∀ j, j ≠ EI tK tE tH → j ≠ P2 tK tE tH → s8.sh j = σ.sh j := by
    intro j h1 h2
    simp [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1, Function.update_apply, h1, h2]
  have sEO : ∀ j, j ≠ EI tK tE tH → s8.st j = σ.st j := by
    intro j h1
    simp [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1, Function.update_apply, h1]
  have hP28 : s8.sh (P2 tK tE tH) = (marks u).length := by
    simp [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1, Function.update_apply, dPE, dEP, hP2h]
  have hv8 : ∀ q, q ≠ opEI → q ≠ scP2 → s8.val q = σ.val q := by
    intro q h1 h2
    by_cases q1 : q = rRc
    · subst q1; simp (config := { decide := true }) [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1,
        Function.update_apply, zRc]
    · by_cases q2 : q = rK
      · subst q2; simp (config := { decide := true }) [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1,
          Function.update_apply, zK]
      · simp (config := { decide := true }) [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1,
          Function.update_apply, h1, h2, q1, q2]
  refine WXExec.mono (WXExec.cast cap whole ?_ le_rfl) ?_
  · rw [hs10, hs9]
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases j1 : j = P2 tK tE tH
      · subst j1; simp [Function.update_apply, dPE, dEP, hP28, hP2h]
      · by_cases j2 : j = EI tK tE tH
        · subst j2; simp [Function.update_apply, dEP, dPE, hEIh8, hEIh]
        · simp [Function.update_apply, j1, j2, dEO j j2 j1]
    · funext j
      by_cases j2 : j = EI tK tE tH
      · subst j2; simp [hEI8]
      · simp [Function.update_apply, j2, sEO j j2]
    · funext q
      by_cases q1 : q = scP2
      · subst q1; simp (config := { decide := true }) [zSC]
      · by_cases q2 : q = opEI
        · subst q2; simp (config := { decide := true }) [zOP]
        · simp [Function.update_apply, q1, q2, hv8 q q2 q1]
    · simp [hs8, hs7, hs6, adv, appendO, hs5, hs4, hs3, hs2, hs1]
  · have h3 : s3.val rR = Rv := by
      simp (config := { decide := true }) [hs3, hs2, hs1, appendO, Function.update_apply, hR]
    have h4 : s4.val rR = Rv := by
      simp (config := { decide := true }) [hs4, hs3, hs2, hs1, appendO, Function.update_apply, hR]
    have hW1l : W1.length = 4 * Rv.bits.length + 2 := by rw [hW1]; simp [hU1l, marks]
    have hm := Nat.mul_le_mul_right (12 * Rv + 60) hbl
    rw [hR, h3, h4, hW1l, hWxl, marks_len, hu]
    simp only [List.length_singleton]
    have hsq := Nat.le_mul_self Rv
    nlinarith [hm, hbl, hsq]

end NearCubicGates.Close.Recovery.HT
