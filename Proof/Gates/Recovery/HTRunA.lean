import Proof.Gates.Recovery.HTRunH

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

/-- **The address split.** -/
theorem addr_exec (tK tE tH pl cap : ℕ) (σ : WState (NS tK tE tH) 64) (u wa wj r : List Bool) (Rv cl : ℕ)
    (hu : u.length = Rv) (ha : wa.length = cl) (hj : wj.length = pl)
    (hP2 : σ.st (P2 tK tE tH) = frame (u ++ wa ++ wj ++ r)) (hP2h : σ.sh (P2 tK tE tH) = 0)
    (hR : σ.val rR = Rv) (hCL : σ.val rCL = cl)
    (hz : ∀ q ∈ [rK, rT, scP2, R 0, R 10, R 11, R 12, rJ], σ.val q = 0)
    (hcap : 2 * 2 ^ cl + 2 * 2 ^ pl + 4 * (Rv + cl + pl) + 4 ≤ cap) :
    WXExec cap (addrW tK tE tH pl) σ
      (((((σ.seth (P2 tK tE tH) (2 * (Rv + cl + pl))).setv (R 0) (value wa)).setv rJ (value wj)).setv scP2
        (2 * (Rv + cl + pl)))) (200 * (Rv + 1) + 2 * LitDecode.binKCost cl + 2 * LitDecode.binKCost pl + 4 * pl + 100)
      := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zK, zT, zSC, z0, z10, z11, z12, zJ⟩ := hz
  have hfr : frame (u ++ wa ++ wj ++ r) = marks u ++ marks wa ++ (marks wj ++ (marks r ++ [false])) := by
    rw [frame_marks]; simp [marks_append', List.append_assoc]
  -- 1–2. rK := 2R
  have x1 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) σ zT (by omega)
  obtain ⟨s1, hs1, e1⟩ := named x1
  have x2 := addR_spec cap (A := rR) (B := rK) (T := rT) (by decide) (by decide) (by decide) s1
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zT])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zK, hR]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  have hK2 : s2.val rK = (marks u).length := by
    simp (config := { decide := true }) [hs2, hs1, Function.update_apply, zK, hR, marks_len, hu]; omega
  -- 3. skip marks x
  have x3 := skipN_exec (cap := cap) (P2 tK tE tH) (SC := scP2) (K := rK) (by decide) _ s2 hK2
    (by rw [marks_len]; omega)
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, zSC, marks_len]; omega)
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.wm x3)
  -- 4. rK := cl
  have x4 := addR_spec cap (A := rCL) (B := rK) (T := rT) (by decide) (by decide) (by decide) s3
    (by simp (config := { decide := true }) [hs3, hs2, hs1, Function.update_apply, zT])
    (by simp (config := { decide := true }) [hs3, hs2, hs1, Function.update_apply, hCL]; omega)
  obtain ⟨s4, hs4, e4⟩ := named x4
  -- 5. a
  have x5 := LitDecode.binK_exec (cap := cap) (P2 tK tE tH) (K := rK) (X := R 0) (P := R 10) (Q := R 11) (T := R 12)
    (SC := scP2) (by decide) wa (marks u) (marks wj ++ (marks r ++ [false])) s4
    (by rw [hs4, hs3, hs2, hs1]; simp only [WState.setv_st, WState.seth_st]; rw [hP2, hfr]; exact RdEq.refl _)
    (by simp [hs4, hs3, hs2, hs1, hP2h, marks_len, hu] <;> omega)
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, hCL, ha])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, z10])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, z11])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, z12])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, z0, ha]; omega)
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, zSC, ha, marks_len, hu]
        omega)
  obtain ⟨s5, hs5, e5⟩ := named x5
  -- 6. rK := pl
  have x6 := incN_exec (cap := cap) rK pl s5 (by simp [hs5]; omega)
  obtain ⟨s6, hs6, e6⟩ := named x6
  -- 7. j
  have x7 := LitDecode.binK_exec (cap := cap) (P2 tK tE tH) (K := rK) (X := rJ) (P := R 10) (Q := R 11) (T := R 12)
    (SC := scP2) (by decide) wj (marks u ++ marks wa) (marks r ++ [false]) s6
    (by rw [hs6, hs5, hs4, hs3, hs2, hs1]; simp only [WState.setv_st, WState.seth_st]; rw [hP2, hfr]
        simp only [List.append_assoc]; exact RdEq.refl _)
    (by simp [hs6, hs5, hs4, hs3, hs2, hs1, hP2h, marks_len, hu, ha] <;> omega)
    (by simp [hs6, hs5, hj])
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, z10])
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, z11])
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, z12])
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, zJ, hj]; omega)
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, zSC, hj, ha,
        marks_len, hu]; omega)
  obtain ⟨s7, hs7, e7⟩ := named x7
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4
    (WXExec.seq e5 (WXExec.seq e6 e7)))))) ?_ le_rfl) ?_
  · rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
    refine WState.eq ?_ rfl ?_ rfl
    · funext j
      by_cases j1 : j = P2 tK tE tH
      · subst j1; simp [hP2h, marks_len, hu, ha, hj]; ring
      · simp [Function.update_apply, j1]
    · funext q
      by_cases q1 : q = rK
      · subst q1; simp (config := { decide := true }) [Function.update_apply, zK]
      · by_cases q2 : q = scP2
        · subst q2; simp (config := { decide := true }) [Function.update_apply, zSC, marks_len, hu, ha, hj]; ring
        · by_cases q3 : q = rJ
          · subst q3; simp (config := { decide := true }) [Function.update_apply, zJ]
          · by_cases q4 : q = R 0
            · subst q4; simp (config := { decide := true }) [Function.update_apply, z0]
            · by_cases q5 : q = rT
              · subst q5; simp (config := { decide := true }) [Function.update_apply, zT]
              · simp (config := { decide := true }) [Function.update_apply, q1, q2, q3, q4, q5]
  · simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, hR, hCL, zK, ha, hj,
      marks_len, hu]
    have hmu : (marks u).length = 2 * Rv := by rw [marks_len, hu]
    have h1 : 1 ≤ 2 ^ cl := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ pl := Nat.one_le_two_pow
    have h3 : 18 * cl ≤ LitDecode.binKCost cl := by
      unfold LitDecode.binKCost; nlinarith
    omega

end NearCubicGates.Close.Recovery.HT
