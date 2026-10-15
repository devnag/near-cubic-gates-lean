import Proof.Gates.CellsSys.PrG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def prP : St VV MM :=
  .seq (.op (.mul n0 n1 t3)) (.seq emitNatK (.seq ptsP (.seq cntP (.seq (.op (.copy t3 cnt)) (.seq emitNatK rowsQ)))))

/-- The cost of the printer (a function of `n` only). -/
def prCost (_S : SolveMachine) (_C : Ctx) (c : Call) (_p : Params) (_Big : ℕ) : ℕ :=
  1 + (40 * BwP c + 40) + ((4 * c.n ^ 4 + 1) * (((4 * c.n ^ 4 + 1) * (ptCost (BwP c) + 4) + 4) + 4) + 4) +
    (1 + (c.n * (fqCost (100 * (c.n + 1) ^ 5) + 4 + 4) + 4) + 1) + 1 + (40 * BwP c + 40) +
    (c.n * (fqCost (100 * (c.n + 1) ^ 5) + s0Cost c.n (BwP c) + 1 + 4) + 4) + 6

theorem sysWord_eq (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)
    (part : Option Bool) :
    sysWord (sysOf c p wt y κ part) = natWord (lenR c p wt y κ 0 * lenR c p wt y κ 1) ++
      ((List.range (lenR c p wt y κ 0)).flatMap (rowPts (roleCount c.kind) (loR c p wt y κ 0).toNat
        (-loR c p wt y κ 0).toNat (loR c p wt y κ 1).toNat (-loR c p wt y κ 1).toNat (lenR c p wt y κ 1)) ++
      (natWord ((p.primes.sort (· ≤ ·)).map fun q => q * qBn q (roleCount c.kind)).sum ++
      ((p.primes.sort (· ≤ ·)).flatMap (rowsS0W (roleCount c.kind) (Jf c p wt y κ part)) ++ []))) := by
  have e : sysWord (sysOf c p wt y κ part) = listWord (listWord Interfaces.intWord)
      ((ptsOf c p wt y κ).map fun u => List.ofFn u) ++ listWord (fun row : ℕ × List ℕ × ℕ =>
        natWord row.1 ++ listWord natWord row.2.1 ++ natWord row.2.2) (rowsOf c p wt y κ part) := rfl
  rw [e, listWord, listWord, pts_len, pts_word, rows_len, rows_word]
  simp [List.append_assoc]

theorem prP_spec : PrGoal prP prCost := by
  intro S C c p wt y Big a0 a part κ rest G h0 hK hκ hpart hBV hkin hA
  obtain ⟨cT, hs⟩ := G.spec
  obtain ⟨w, hw⟩ := G.dec
  obtain ⟨B1, B2, hadm⟩ := G.adm
  have hBN := boxN_of G h0 hK hBV
  have hRN := rowN_of κ part G h0 hK
  have hL := (G.call part κ hκ).1
  have hW2 := hBN.W2
  have hbw := hBN.BW
  have hP0 : PS a (sysWord (sysOf c p wt y κ part)) _ _ a :=
    ⟨rfl, rfl, rfl, hK.rc, by rw [hkin]; exact (List.nil_append _).trans (sysWord_eq c p wt y κ part).symm,
      by rw [hA, rows_vals], Keep.cst h0 hK, fun _ _ => rfl⟩
  -- bounds
  have hWn := W_le c p wt y G
  have hN0 := lenR_le c p wt y κ 0
  have hN1 := lenR_le c p wt y κ 1
  have hPB : 2 * c.W + 1 ≤ 4 * c.n ^ 4 + 1 := by omega
  have h4 := n4p c.n
  have hNN : lenR c p wt y κ 0 * lenR c p wt y κ 1 ≤ 2 ^ (4 * c.n + 3) * 2 ^ (4 * c.n + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [← pow_add] at hNN
  have hp7 := wd_n G (8 * c.n + 7) (by omega)
  have hlt7 : 2 ^ (4 * c.n + 3 + (4 * c.n + 3)) < 2 ^ (8 * c.n + 7) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Hx.hs (Hs.then (o_mul n0 n1 t3 a (by decide) (by decide) (by decide) (by
    rw [hBV.n0e, hBV.n1e]; omega)) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  rw [hBV.n0e, hBV.n1e] at p1
  refine Hs.then (ps_emit _ (BwP c) (hP0.step p3 p2 (by decide)) p1
    ((nbl_lt (k := 8 * c.n + 7) (by omega) (by omega)).trans (by unfold BwP; omega)) hbw hW2 hL)
    (fun s2 ⟨q1, q2⟩ k2 hk2 => ?_)
  refine Hs.then (ptsP_spec hBN hL q1) (fun s3 ⟨r1, r2⟩ k3 hk3 => ?_)
  refine Hs.then (cntP_spec hRN r1) (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_)
  refine Hs.then (o_copy t3 cnt s4 (by decide)) (fun s5 ⟨v1, v2, v3⟩ k5 hk5 => ?_)
  rw [u1] at v1
  refine Hs.then (ps_emit _ (BwP c) (u2.step v3 v2 (by decide)) v1 hRN.bc hbw hW2 hL)
    (fun s6 ⟨x1, x2⟩ k6 hk6 => ?_)
  refine Hs.last (rowsQ_spec hRN hL x1) (fun s7 ⟨y1, y2⟩ k7 hk7 => ⟨⟨by have := y1.kin; simpa using this,
    y1.sA, y1.ram, y1.ip, y1.out, y1.rc, y1.fr⟩, ?_⟩)
  -- the cost
  have hPs : (p.primes.sort (· ≤ ·)).length ≤ c.n := by
    rw [Finset.length_sort]; exact (primes_card_le c p hs).trans (P_le_n c p hs)
  have hLN : (a.ram sN).length ≤ 100 * (c.n + 1) ^ 5 := by
    rw [hK.ram, h0.cellN]; exact cellN_len c p wt w hadm hs hw
  have hfq : fqCost (a.ram sN).length ≤ fqCost (100 * (c.n + 1) ^ 5) := by unfold fqCost; omega
  have m1 : lenR c p wt y κ 0 * ((lenR c p wt y κ 1 * (ptCost (BwP c) + 4) + 4) + 4) + 4 ≤
      (4 * c.n ^ 4 + 1) * (((4 * c.n ^ 4 + 1) * (ptCost (BwP c) + 4) + 4) + 4) + 4 := by
    have := Nat.mul_le_mul (show lenR c p wt y κ 0 ≤ 4 * c.n ^ 4 + 1 by omega)
      (show (lenR c p wt y κ 1 * (ptCost (BwP c) + 4) + 4) + 4 ≤ ((4 * c.n ^ 4 + 1) * (ptCost (BwP c) + 4) + 4) + 4 by
        have := Nat.mul_le_mul_right (ptCost (BwP c) + 4) (show lenR c p wt y κ 1 ≤ 4 * c.n ^ 4 + 1 by omega)
        omega)
    omega
  have m2 : (p.primes.sort (· ≤ ·)).length * (fqCost (a.ram sN).length + 4 + 4) ≤
      c.n * (fqCost (100 * (c.n + 1) ^ 5) + 4 + 4) := Nat.mul_le_mul hPs (by omega)
  have m3 : (p.primes.sort (· ≤ ·)).length * (fqCost (a.ram sN).length + s0Cost c.n (BwP c) + 1 + 4) ≤
      c.n * (fqCost (100 * (c.n + 1) ^ 5) + s0Cost c.n (BwP c) + 1 + 4) := Nat.mul_le_mul hPs (by omega)
  unfold prCost
  omega

end NearCubicGates.Close.Cells.SystemsPhase
