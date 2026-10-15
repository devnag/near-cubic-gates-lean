import Proof.Gates.CellsSys.CallI

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN bitN)

variable {C : Ctx}

def callP : St VV MM := .seq (.op .kcall) (.seq rdNatK (.seq rdNatK cptsP))

/-- The cost of the solver step. -/
def callCost (_S : SolveMachine) (C : Ctx) (c : Call) (_p : Params) (_Big : ℕ) : ℕ :=
  (1 + C.Lk + C.Bk) + ((30 * BwP c + 30) + ((30 * BwP c + 30) + ((4 * c.n ^ 4 + 1) *
    (((4 * c.n ^ 4 + 1) * (cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4) + 4) + 4) + 4) + 1) + 1) + 1

theorem preS_cast (f : ℕ → ℕ → ℕ) (N0 N1 : ℕ) : ((preS f N1 N0 : ℕ) : ℚ) =
    ((List.range N0).map fun a => ((List.range N1).map fun b => (f a b : ℚ)).sum).sum := by
  unfold preS rowS
  push_cast
  simp [List.map_map, Function.comp_def]

theorem callP_spec : CallGoal callP callCost := by
  intro S C c p wt y Big a0 a part κ G h0 hK hκ hpart hBV hpI hkin hcnt
  obtain ⟨cT, hs⟩ := G.spec
  obtain ⟨w, hw⟩ := G.dec
  obtain ⟨B1, B2, hadm⟩ := G.adm
  have hN := callN_of G h0 hK hBV hpI hcnt
  have hsw := solve_word c p wt y κ part S hs G.tests hκ
  have hbw := hN.BW
  have hB1 := hN.B1
  refine Hx.hs (Hs.then (o_kcall S h0.callee (sysOf c p wt y κ part) a hkin (G.call part κ hκ).2)
    (fun b1 hb1 k1 hk1 => ?_))
  subst hb1
  have C1 : CS a (natWord 1 ++ (natWord (lenR c p wt y κ 0 * lenR c p wt y κ 1) ++
      ((List.range (lenR c p wt y κ 0)).flatMap (fun a => (List.range (lenR c p wt y κ 1)).flatMap
        (rdW (mdAB c p wt y κ part) a)) ++ [])))
      (a.called (solveWord (S.solve (sysOf c p wt y κ part)))) :=
    ⟨rfl, rfl, rfl, rfl, hK.rc, rfl, by simp only [DS.called, List.drop_zero]; exact hsw,
      (by have hc := Keep.cst h0 hK; exact ⟨hc.z, hc.one, hc.two⟩), fun _ _ _ => rfl⟩
  refine Hs.then (cs_rd 1 (BwP c) C1 (nbl01 1 _ le_rfl hB1) hbw) (fun b2 ⟨p1, p2, p3⟩ k2 hk2 => ?_)
  -- the point count
  have hW := W_le c p wt y G
  have hN0 := lenR_le c p wt y κ 0
  have hN1 := lenR_le c p wt y κ 1
  have h4 := n4p c.n
  have hNN : lenR c p wt y κ 0 * lenR c p wt y κ 1 ≤ 2 ^ (4 * c.n + 3) * 2 ^ (4 * c.n + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [← pow_add] at hNN
  have hlt7 : 2 ^ (4 * c.n + 3 + (4 * c.n + 3)) < 2 ^ (8 * c.n + 7) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Hs.then (cs_rd _ (BwP c) p2 ((nbl_lt (k := 8 * c.n + 7) (by omega) (by omega)).trans (by unfold BwP; omega))
    hbw) (fun b3 ⟨q1, q2, q3⟩ k3 hk3 => ?_)
  have hV3 : b3.env vCnt = a.env vCnt := by
    rw [q3 vCnt (by decide), p3 vCnt (by decide)]; rfl
  refine Hs.last (cptsP_spec hN q2 hV3) (fun b4 ⟨r1, r2, r3⟩ k4 hk4 => ⟨⟨?_, r1.kin, r1.ram, r1.ip, r1.out,
    r1.rcA, r1.rc, fun x hx hc => r1.fr x hx hc⟩, ?_⟩)
  · rw [r2, Nat.cast_add, preS_cast, sum_pts]
    congr 1
    refine congrArg List.sum (List.map_congr_left (fun a' ha' => ?_))
    refine congrArg List.sum (List.map_congr_left (fun b hb => ?_))
    rw [List.mem_range] at ha' hb
    obtain ⟨cT', hs'⟩ := G.spec
    have hwf0 : (circ c 0).table.length = 2 * (circ c 0).topWeight + 1 := (circ_wf c hadm 0).2.2.1
    have hwf1 : (circ c 1).table.length = 2 * (circ c 1).topWeight + 1 := (circ_wf c hadm 1).2.2.1
    have hT0e : a.env vTS0 = a0.env vTS0 := hK.ev (x := vTS0) (by decide) (by decide)
    have hT1e : a.env vTS1 = a0.env vTS1 := hK.ev (x := vTS1) (by decide) (by decide)
    have hram : a.ram sN = cellN c p wt := by rw [hK.ram]; exact h0.cellN
    rw [predW_eq c p wt y κ part hpart a' b ha' hb (T0 := a.env vTS0) (T1 := a.env vTS1)
      (by rw [hT0e]; exact h0.TS0) (by rw [hT1e]; exact h0.TS1) hwf0 hwf1, trueDist_tdN, hram]
    unfold cfn
    split_ifs <;> simp [mdAB]
  · -- the cost
    have hLN : (a.ram sN).length ≤ 100 * (c.n + 1) ^ 5 := by
      rw [hK.ram, h0.cellN]; exact cellN_len c p wt w hadm hs hw
    have hc : cptCost (BwP c) (a.ram sN).length ≤ cptCost (BwP c) (100 * (c.n + 1) ^ 5) := by
      unfold cptCost bitsCost; omega
    have m1 : lenR c p wt y κ 0 * ((lenR c p wt y κ 1 * (cptCost (BwP c) (a.ram sN).length + 4) + 4) + 4) + 4 ≤
        (4 * c.n ^ 4 + 1) * (((4 * c.n ^ 4 + 1) * (cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4) + 4) + 4) + 4 := by
      have := Nat.mul_le_mul (show lenR c p wt y κ 0 ≤ 4 * c.n ^ 4 + 1 by omega)
        (show (lenR c p wt y κ 1 * (cptCost (BwP c) (a.ram sN).length + 4) + 4) + 4 ≤
          ((4 * c.n ^ 4 + 1) * (cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4) + 4) + 4 by
          have := Nat.mul_le_mul (show lenR c p wt y κ 1 ≤ 4 * c.n ^ 4 + 1 by omega)
            (show cptCost (BwP c) (a.ram sN).length + 4 ≤ cptCost (BwP c) (100 * (c.n + 1) ^ 5) + 4 by omega)
          omega)
      omega
    unfold callCost
    omega

end NearCubicGates.Close.Cells.SystemsPhase
