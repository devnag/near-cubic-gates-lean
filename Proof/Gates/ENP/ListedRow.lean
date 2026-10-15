import Proof.Gates.ENP.ListedStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} {cap : ℕ}

/-- The registers of the row loop are pairwise distinct. -/
structure RRegs (K J X Y B CO : Fin nr) : Prop where
  e : ERegs X Y B CO
  kj : K ≠ J
  kx : K ≠ X
  ky : K ≠ Y
  kb : K ≠ B
  kc : K ≠ CO
  jx : J ≠ X
  jy : J ≠ Y
  jb : J ≠ B
  jc : J ≠ CO

/-- Write the row `qRow R i` (`R` the value of `K`, `i` the value of `X`). -/
def rowLoop (K J X Y B CO : Fin nr) (O : Fin (ns + 1)) : WMX ns nr := repK K J (qStep X Y B CO O)

theorem qRow_succ (R i : ℕ) : qRow (R + 1) i = qRow R i ++ qField (i.testBit R) := by
  simp [qRow, List.range_succ, List.flatMap_append]

theorem qRow_length (R i : ℕ) : (qRow R i).length = 7 * R := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [qRow_succ, List.length_append, ih]
    cases i.testBit R <;> rfl

/-- Cost of one row. -/
def rowCost (R i : ℕ) : ℕ := R * (13 * i + 98) + 7 * R + 3

theorem rowLoop_exec (K J X Y B CO : Fin nr) (O : Fin (ns + 1)) (hr : RRegs K J X Y B CO) (R i : ℕ)
    (σ : WState ns nr) (out L0 : List Bool) (hK : σ.val K = R) (hJ : σ.val J = 0) (hX : σ.val X = i)
    (hY : σ.val Y = 0) (hB : σ.val B = 0) (hO : OutOn σ O CO out L0) (hi : i ≤ cap) (hR : 2 * R ≤ cap)
    (hc : out.length + 7 * R + 8 < cap) :
    WXExec cap (rowLoop K J X Y B CO O) σ (outSt (σ.setv X (i / 2 ^ R)) O CO (out ++ qRow R i) L0)
      (rowCost R i) := by
  have he := hr.e
  obtain ⟨_, hkj, hkx, hky, hkb, hkc, hjx, hjy, hjb, hjc⟩ := hr
  obtain ⟨hxy, hxb, hyb, hxc, hyc, hbc⟩ := he
  let st : ℕ → WState ns nr := fun k => outSt (σ.setv X (i / 2 ^ k)) O CO (out ++ qRow k i) L0
  have hst0 : st 0 = σ := by
    apply WState.eq
    · funext j; simp only [st, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp [qRow, hO.2.1]
    · funext j; simp only [st, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp [qRow, hO.1]
    · funext j; simp only [st, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [qRow, hO.2.2]
    · rfl
  have h := Runs.repE (cap := cap) (K := K) (K2 := J) (body := qStep X Y B CO O) hkj (13 * i + 90) R st hR
    (by intro k; simp [st, outSt, Function.update_of_ne hkc, Function.update_of_ne hkx])
    (by intro k; simp [st, outSt, Function.update_of_ne hjc, Function.update_of_ne hjx])
    (by
      intro k hk v1 v2
      have hq := qStep_exec (cap := cap) X Y B CO O ⟨hxy, hxb, hyb, hxc, hyc, hbc⟩ (i / 2 ^ k) (((st k).setv K v1).setv J v2)
        (out ++ qRow k i) L0
        (by simp [st, outSt, Function.update_of_ne hjx.symm, Function.update_of_ne hkx.symm,
          Function.update_of_ne hxc])
        (by simp [st, outSt, Function.update_of_ne hjy.symm, Function.update_of_ne hky.symm,
          Function.update_of_ne hyc, Function.update_of_ne hxy.symm, hY])
        (by simp [st, outSt, Function.update_of_ne hjb.symm, Function.update_of_ne hkb.symm,
          Function.update_of_ne hbc, Function.update_of_ne hxb.symm, hB])
        (outOn_setv (outOn_setv (outOn_outSt _ _ _ _ _) K hkc v1) J hjc v2)
        ((Nat.div_le_self _ _).trans hi)
        (by rw [List.length_append, qRow_length]; nlinarith)
      have hdiv : i / 2 ^ k / 2 = i / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
      have hbit : decide (i / 2 ^ k % 2 = 1) = i.testBit k := (Nat.testBit_eq_decide_div_mod_eq).symm
      refine WXExec.mono (WXExec.cast cap hq ?_ le_rfl) (by
        have : i / 2 ^ k ≤ i := Nat.div_le_self _ _
        nlinarith)
      rw [hdiv, hbit, List.append_assoc, ← qRow_succ]
      apply WState.eq
      · funext j; simp only [st, outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        try (split_ifs <;> simp_all)
      · funext j; simp only [st, outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        try (split_ifs <;> simp_all)
      · funext j; simp only [st, outSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · rfl)
    (by rw [hst0]; exact hK) (by rw [hst0]; exact hJ)
  rw [hst0] at h
  refine WXExec.mono h ?_
  unfold rowCost
  nlinarith

end NearCubicGates.Close.ENP
