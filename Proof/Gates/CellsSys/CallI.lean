import Proof.Gates.CellsSys.CallH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN bitN)

variable {C : Ctx}

theorem drop_lt {l A B : List ℕ} {k : ℕ} (h : l.drop k = A ++ B) (hA : 0 < A.length) : k < l.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append] at hl
  omega

theorem mdAB_le (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)
    (part : Option Bool) (a b : ℕ) : mdAB c p wt y κ part a b ≤ 2 ^ c.n := by
  have h := trueDist_le c p wt y part κ (ptAB c p wt y κ a b)
  rw [trueDist_tdN] at h
  unfold mdAB; exact_mod_cast h

theorem callN_of {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    {a0 a : DS VV MM} {κ : Role c × Fin p.J → ℤ} {part : Option Bool} (G : Glob S C c p wt y Big)
    (h0 : SysPre S C c p wt y a0) (hK : Keep a0 a) (hB : BoxV c p wt y κ a)
    (hpI : a.env pI = if part = some true then 1 else 0)
    (hcnt : a.env vCnt + (ptsOf c p wt y κ).length * 2 ^ c.n < 2 ^ C.Wd) :
    CallN a (kindTag c.kind) (if outerParity c wt y then 1 else 0) (if part = some true then 1 else 0)
      (loR c p wt y κ 0).toNat (-loR c p wt y κ 0).toNat (loR c p wt y κ 1).toNat (-loR c p wt y κ 1).toNat
      (lenR c p wt y κ 0) (lenR c p wt y κ 1) (a.env vTS0) (circ c 0).topWeight (a.env vTS1) (circ c 1).topWeight
      (2 ^ c.n) (BwP c) (mdAB c p wt y κ part) C := by
  obtain ⟨cT, hs⟩ := G.spec
  obtain ⟨w, hw⟩ := G.dec
  obtain ⟨B1, B2, hadm⟩ := G.adm
  have hram : a.ram sN = cellN c p wt := by rw [hK.ram]; exact h0.cellN
  have hT0e : a.env vTS0 = a0.env vTS0 := hK.ev (x := vTS0) (by decide) (by decide)
  have hT1e : a.env vTS1 = a0.env vTS1 := hK.ev (x := vTS1) (by decide) (by decide)
  have hT0 : (cellN c p wt).drop (a.env vTS0) = (circ c 0).table.map bitN ++
      (cellN c p wt).drop (a.env vTS0 + (circ c 0).table.length) := by rw [hT0e]; exact h0.TS0
  have hT1 : (cellN c p wt).drop (a.env vTS1) = (circ c 1).table.map bitN ++
      (cellN c p wt).drop (a.env vTS1 + (circ c 1).table.length) := by rw [hT1e]; exact h0.TS1
  have hwf0 : (circ c 0).table.length = 2 * (circ c 0).topWeight + 1 := (circ_wf c hadm 0).2.2.1
  have hwf1 : (circ c 1).table.length = 2 * (circ c 1).topWeight + 1 := (circ_wf c hadm 1).2.2.1
  have hlenN := cellN_len c p wt w hadm hs hw
  have hT0lt : a.env vTS0 < (cellN c p wt).length := drop_lt hT0 (by simp [hwf0])
  have hT1lt : a.env vTS1 < (cellN c p wt).length := drop_lt hT1 (by simp [hwf1])
  have hW := W_le c p wt y G
  have htw0 := topWeight_le_W c 0
  have htw1 := topWeight_le_W c 1
  have hN0 := lenR_le c p wt y κ 0
  have hN1 := lenR_le c p wt y κ 1
  have h5 := n5p c.n
  have hn4 : c.n ^ 4 ≤ (c.n + 1) ^ 5 :=
    (Nat.pow_le_pow_left (by omega) 4).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hp := wd_n G (5 * c.n + 12) (by omega)
  have hp' : 2 ^ (5 * c.n + 12) = 128 * 2 ^ (5 * c.n + 5) := by
    rw [show 5 * c.n + 12 = 5 * c.n + 5 + 7 by omega, pow_add]; ring
  have hbw : BwP c + 2 ≤ C.Wd := by have := G.wd; unfold BwP; nlinarith
  have hpl := pts_len c p wt y κ
  rw [List.length_map] at hpl
  have hrc := rc12 c
  refine ⟨(hK.ev (x := vKd) (by decide) (by decide)).trans h0.kind,
    (hK.ev (x := vOP) (by decide) (by decide)).trans h0.op, hpI, hB.l0p, hB.l0n, hB.l1p, hB.l1n, hB.n0e, hB.n1e, rfl,
    (hK.ev (x := vTW0) (by decide) (by decide)).trans h0.TW0, rfl,
    (hK.ev (x := vTW1) (by decide) (by decide)).trans h0.TW1, ⟨by split_ifs <;> omega, by split_ifs <;> omega⟩,
    fun a' ha' => ?_, fun hK1 b hb => ?_, fun hn => ?_, fun hK1 hn => ?_, by omega, by omega,
    fun a' _ b _ => mdAB_le c p wt y κ part a' b, fun a' _ b _ => ?_, by unfold BwP; omega, hbw, ?_, ?_⟩
  · obtain ⟨_, g2, g3, g4⟩ := bit_eq c p wt y κ 0 (by omega) hT0 hwf0 a' ha'
    rw [hram]
    exact ⟨g2, g3, by rw [g4]; exact bitN_le _⟩
  · have h2 : 1 < roleCount c.kind := by
      rcases hk : c.kind with _ | _ | _
      · rw [hk] at hK1; simp [kindTag] at hK1
      · decide
      · rw [hk] at hK1; simp [kindTag] at hK1
    obtain ⟨_, g2, g3, g4⟩ := bit_eq c p wt y κ 1 h2 hT1 hwf1 b hb
    rw [hram]
    exact ⟨g2, g3, by rw [g4]; exact bitN_le _⟩
  · have := loR_pos c p wt y κ 0 hn; omega
  · have := loR_pos c p wt y κ 1 hn; omega
  · exact (nbl_lt (k := c.n + 1) (lt_of_le_of_lt (mdAB_le c p wt y κ part a' b)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))) (by omega)).trans (by unfold BwP; omega)
  · rw [← hpl]; exact hcnt
  · rw [hram]; omega

end NearCubicGates.Close.Cells.SystemsPhase
