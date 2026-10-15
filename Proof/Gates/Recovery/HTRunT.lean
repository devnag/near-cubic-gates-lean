import Proof.Gates.Recovery.HTRunA

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
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

theorem twoPlus_exec (tK tE tH cap : ℕ) (V : Fin 64) (hV1 : V ≠ rKr) (hV2 : V ≠ rT) (σ : WState (NS tK tE tH) 64)
    (v : ℕ) (hv : σ.val V = v) (hK : σ.val rKr = 0) (hT : σ.val rT = 0) (hc : 2 * v + 2 ≤ cap) :
    WXExec cap (twoPlus tK tE tH V) σ (σ.setv rKr (2 * v + 1)) (40 * v + 12) := by
  have x1 := addR_spec cap (A := V) (B := rKr) (T := rT) hV1 hV2 (by decide) σ hT (by omega)
  obtain ⟨s1, hs1, e1⟩ := named x1
  have x2 := addR_spec cap (A := V) (B := rKr) (T := rT) hV1 hV2 (by decide) s1
    (by simp (config := { decide := true }) [hs1, Function.update_apply, hT])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, hK, hv, Ne.symm hV1]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  have x3 := WXExec.inc (cap := cap) rKr s2
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hK, hv, Ne.symm hV1]; omega)
  obtain ⟨s3, hs3, e3⟩ := named x3
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ le_rfl) ?_
  · rw [hs3, hs2, hs1]
    simp only [WState.setv_val, Function.update_self, LitDecode.setv_setv]
    congr 1; simp [Function.update_apply, Ne.symm hV1, hK, hv]; omega
  · rw [hs1]; simp [Function.update_apply, Ne.symm hV1, hV1, hv]; omega

/-- The coordinate `asg[v]` as a register value. -/
def bitAt (asg : List Bool) (v : ℕ) : ℕ := (asg.getD v false).toNat

/-- **The three coordinates.** -/
theorem rd_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) (asg : List Bool) (v0 v1 v2 : ℕ)
    (hAS : RdEq (σ.st (AS tK tE tH)) (marks asg)) (hASh : σ.sh (AS tK tE tH) = (marks asg).length)
    (hOP : σ.val opAS = (marks asg).length)
    (h1 : σ.val (R 1) = v0) (h2 : σ.val (R 2) = v1) (h3 : σ.val (R 3) = v2)
    (hz : ∀ q ∈ [rT1, rT, rKr, rT3, b0, b1, b2], σ.val q = 0)
    (hcap : 4 * (asg.length + v0 + v1 + v2) + 4 ≤ cap) :
    WXExec cap (rdW tK tE tH) σ ((((σ.seth (AS tK tE tH) 0).setv b0 (bitAt asg v0)).setv b1 (bitAt asg v1)).setv b2
      (bitAt asg v2)) (100 * (asg.length + v0 + v1 + v2 + 2)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zT1, zT, zKr, zT3, z0, z1, z2⟩ := hz
  have hml := marks_len asg
  have x1 := addR_spec cap (A := opAS) (B := rT1) (T := rT) (by decide) (by decide) (by decide) σ zT (by omega)
  obtain ⟨s1, hs1, e1⟩ := named x1
  have x2 := wrewind_spec (cap := cap) (AS tK tE tH) rT1 (marks asg).length s1
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zT1, hOP])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zT1, hOP]; omega)
  obtain ⟨s2, hs2, e2⟩ := named (WXExec.wm x2)
  have x3 := twoPlus_exec tK tE tH cap (R 1) (by decide) (by decide) s2 v0
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, h1])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, zKr])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, zT]) (by omega)
  obtain ⟨s3, hs3, e3⟩ := named x3
  have x4 := readAt_exec (cap := cap) (AS tK tE tH) (SC := rT3) (K := rKr) (Bt := b0) (by decide) asg v0 s3
    (by simpa [hs3, hs2, hs1] using hAS) (by simp [hs3, hs2, hs1, hASh])
    (by simp (config := { decide := true }) [hs3, hs2, hs1, Function.update_apply, zT3])
    (by simp (config := { decide := true }) [hs3])
    (by simp (config := { decide := true }) [hs3, hs2, hs1, Function.update_apply, z0]) (by omega)
  obtain ⟨s4, hs4, e4⟩ := named x4
  have x5 := twoPlus_exec tK tE tH cap (R 2) (by decide) (by decide) s4 v1
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, h2])
    (by simp (config := { decide := true }) [hs4, hs3, Function.update_apply])
    (by simp (config := { decide := true }) [hs4, hs3, hs2, hs1, Function.update_apply, zT]) (by omega)
  obtain ⟨s5, hs5, e5⟩ := named x5
  have x6 := readAt_exec (cap := cap) (AS tK tE tH) (SC := rT3) (K := rKr) (Bt := b1) (by decide) asg v1 s5
    (by simpa [hs5, hs4, hs3, hs2, hs1] using hAS) (by simp [hs5, hs4, hs3, hs2, hs1, hASh])
    (by simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, Function.update_apply, zT3])
    (by simp (config := { decide := true }) [hs5])
    (by simp (config := { decide := true }) [hs5, hs4, hs3, hs2, hs1, Function.update_apply, z1]) (by omega)
  obtain ⟨s6, hs6, e6⟩ := named x6
  have x7 := twoPlus_exec tK tE tH cap (R 3) (by decide) (by decide) s6 v2
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, h3])
    (by simp (config := { decide := true }) [hs6, hs5, Function.update_apply])
    (by simp (config := { decide := true }) [hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, zT]) (by omega)
  obtain ⟨s7, hs7, e7⟩ := named x7
  have x8 := readAt_exec (cap := cap) (AS tK tE tH) (SC := rT3) (K := rKr) (Bt := b2) (by decide) asg v2 s7
    (by simpa [hs7, hs6, hs5, hs4, hs3, hs2, hs1] using hAS) (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hASh])
    (by simp (config := { decide := true }) [hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, zT3])
    (by simp (config := { decide := true }) [hs7])
    (by simp (config := { decide := true }) [hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, z2]) (by omega)
  obtain ⟨s8, hs8, e8⟩ := named x8
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 (WXExec.seq e7 e8))))))) ?_ le_rfl) ?_
  · rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
    refine WState.eq ?_ rfl ?_ rfl
    · funext j; by_cases j1 : j = AS tK tE tH
      · subst j1; simp [hASh]
      · simp [Function.update_apply, j1]
    · funext q
      by_cases q1 : q = rKr
      · subst q1; simp (config := { decide := true }) [Function.update_apply, zKr]
      · by_cases q2 : q = rT1
        · subst q2; simp (config := { decide := true }) [Function.update_apply, zT1]
        · simp (config := { decide := true }) [Function.update_apply, q1, q2, bitAt]
  · simp (config := { decide := true }) [hs1, Function.update_apply, hOP]
    omega

/-- **The output bit.** -/
theorem out_exec (tK tE tH cap : ℕ) (σ : WState (NS tK tE tH) 64) (j : ℕ) (hJ : σ.val rJ = j)
    (hb0 : σ.val b0 ≤ 1) (hb1 : σ.val b1 ≤ 1) (hb2 : σ.val b2 ≤ 1)
    (hn0 : σ.val (R 4) ≤ 1) (hn1 : σ.val (R 5) ≤ 1) (hn2 : σ.val (R 6) ≤ 1)
    (hO : σ.st (OUT tK tE tH) = []) (hOh : σ.sh (OUT tK tE tH) = 0)
    (hz : ∀ q ∈ [rM5, rJ5, rD5, rK5, rT, opOUT], σ.val q = 0) (hcap : j + 20 ≤ cap) :
    ∃ τ, WXExec cap (outPhase tK tE tH) σ τ (300 * (j + 1)) ∧
      τ.st (OUT tK tE tH) = outWord (outBit (j % 5) (σ.val b0) (σ.val b1) (σ.val b2) (σ.val (R 4)) (σ.val (R 5))
        (σ.val (R 6))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zM, zJ5, zD, zK, zT, zO⟩ := hz
  have x1 := incN_exec (cap := cap) rM5 5 σ (by rw [zM]; omega)
  obtain ⟨s1, hs1, e1⟩ := named x1
  have x2 := ClauseFront.modW_exec (cap := cap) (A := rJ) (M := rM5) (C := rJ5) (D := rD5) (K := rK5) (T := rT)
    (by decide) j 5 (by decide) (by omega) (by omega) s1
    (by simp (config := { decide := true }) [hs1, Function.update_apply, hJ])
    (by simp (config := { decide := true }) [hs1, zM])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zJ5])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zD])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zK])
    (by simp (config := { decide := true }) [hs1, Function.update_apply, zT])
  obtain ⟨s2, hs2, e2⟩ := named x2
  have hj5 : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have x3 := outW_exec (cap := cap) (OUT tK tE tH) opOUT rJ5 b0 b1 b2 (R 4) (R 5) (R 6) (by decide) (by decide) s2
    (j % 5) (by simp (config := { decide := true }) [hs2]) (by omega)
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hb0])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hb1])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hb2])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hn0])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hn1])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, hn2])
    (by simp [hs2, hs1, hO, hOh])
    (by simp (config := { decide := true }) [hs2, hs1, Function.update_apply, zO]; omega)
  obtain ⟨s3, hs3, e3⟩ := named x3
  refine ⟨s3, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) ?_, ?_⟩
  · nlinarith
  · rw [hs3]; simp [appendO, hs2, hs1, hO]
    simp (config := { decide := true }) [Function.update_apply]

/-- The output program's value is the table bit. -/
theorem outBit_eq (j : ℕ) (x0 x1 x2 : Bool) (n0 n1 n2 : ℕ) :
    outBit (j % 5) x0.toNat x1.toNat x2.toNat n0 n1 n2 =
      if h : j % 5 < 3 then ![x0, x1, x2] ⟨j % 5, h⟩ else
        (xor x0 (decide (n0 = 1)) && xor x1 (decide (n1 = 1))) && xor x2 (decide (n2 = 1)) := by
  have hl : j % 5 < 5 := Nat.mod_lt _ (by decide)
  have hb : ∀ x : Bool, decide (x.toNat = 1) = x := by intro x; cases x <;> rfl
  unfold outBit
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4) with h | h | h | h | h <;>
    simp [h, hb]

end NearCubicGates.Close.Recovery.HT
