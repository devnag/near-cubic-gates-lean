import Proof.Gates.Cells.Forms2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

namespace Call
variable (c : Call) (p : Params) (wt : Wit c.n)

theorem drop_iG2 : (cellN c p wt).drop (iG2 (cellN c p wt)) = circN c.second ++ ([c.parity.length] ++ c.parity ++
    ratN c.radius ++ (paramsN p ++ witN c p wt)) := by
  set L := cellN c p wt with hL
  have hn := idx_n c p wt
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := circ_fields c.first L _ 2 (idx_circ1 c p wt)
  have e1 : iC1 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) := by
    unfold iC1; rw [hn, a1]
  have e2 : iT1 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 + 2 * c.first.coeffs.length := by
    unfold iT1; rw [e1, a3]
  have e3 : iG2 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 + 2 * c.first.coeffs.length + 1 +
      c.first.table.length := by
    unfold iG2; rw [e2, a5]
  rw [e3, a7]; simp [List.append_assoc]

theorem drop_circ (r : ℕ) (hr : r = 0 ∨ r = 1) :
    ∃ R, (cellN c p wt).drop (if r = 0 then 2 else iG2 (cellN c p wt)) = circN (circ c r) ++ R := by
  rcases hr with h | h <;> subst h
  · exact ⟨_, by simpa [circ] using idx_circ1 c p wt⟩
  · exact ⟨_, by simpa [circ] using drop_iG2 c p wt⟩

theorem wit_fld : fld (cellN c p wt) (iOm (cellN c p wt)) = (coordsOf wt.I).length :=
  fld_of_drop (B := coordsOf wt.I ++ (srList c p).flatMap fun sr =>
    [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN) (by rw [(lay c p wt).wit]; simp [witN])

theorem drop_blocks : (cellN c p wt).drop (iOm (cellN c p wt) + 1 + fld (cellN c p wt) (iOm (cellN c p wt))) =
    blocksAll wt.coef (roleCount c.kind) p.J ++ [] := by
  rw [wit_fld, Nat.add_assoc, ← List.drop_drop, (lay c p wt).wit]
  simp only [witN, List.append_assoc]
  rw [show 1 + (coordsOf wt.I).length = ([(coordsOf wt.I).length] ++ coordsOf wt.I).length by simp; omega]
  rw [← List.append_assoc, List.drop_left]
  simp only [srList, blocksAll, blocksOf, List.flatMap_assoc, List.flatMap_map, List.append_nil]

theorem drop_factors : (cellN c p wt).drop (iPsi (cellN c p wt) + 24 + nPr (cellN c p wt)) =
    [p.factors.length] ++ (p.factors ++ ([p.A, p.Lambda] ++ witN c p wt)) := by
  have h1 := (lay c p wt).params
  have h2 := (lay c p wt).np
  set Pr := p.primes.sort (· ≤ ·)
  have hq : paramsN p ++ witN c p wt = ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]
      ++ [Pr.length] ++ Pr ++ ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1, p.J])) ++
      ([p.factors.length] ++ (p.factors ++ ([p.A, p.Lambda] ++ witN c p wt))) := by
    simp [paramsN, Pr, List.append_assoc]
  rw [hq] at h1
  have h3 := drop_split h1
  rw [h2]
  convert h3 using 2
  simp [ratN_length]; omega

end Call

end NearCubicGates.Close.Cells
