import Proof.Gates.CellsSys.Role

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- The numeric facts of the box program (`V` bounds the store values, `Q` every formed number). -/
structure Nums (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (Big V Q : ℕ) : Prop where
  PV : ∀ x ∈ tailL p, x ≤ V
  EV : ∀ x ∈ ctrL c p wt y, x ≤ V
  XV : ∀ x ∈ kxL c p wt y, x ≤ V
  hE : p.hE ≤ V
  wV : wWin p ≤ V
  w1 : 1 ≤ wWin p
  pw : wWin p ^ nDig c p * (wWin p + 1) < 2 ^ C.Wd
  big : (p.J + 1) * (V * (2 * V + 2)) + 8 * p.J < 2 ^ C.Wd
  cQ : 2 ^ Big * (p.J * (V * (2 * V + 2)) + V) ≤ Q
  VQ : V ≤ Q
  BQ : 2 ^ Big ≤ Q
  q64 : 64 * Q ≤ 2 ^ C.Wd
  q8 : 8 ≤ Q
  TW : ∀ r, (circ c r).topWeight ≤ V
  M1a : 1 ≤ p.M1
  M1b : p.M1 ≤ 2 ^ Big
  Aa : 0 < p.A
  Ab : p.A ≤ 2 ^ Big
  Lb : p.Lambda ≤ 2 ^ Big
  J1 : 1 ≤ p.J

theorem nums {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {Big : ℕ}
    (G : Glob S C c p wt y Big) :
    Nums C c p wt y Big (2 ^ E1 c p Big) (2 ^ (2 * E1 c p Big + p.J + Big + 3)) := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = E1 c p Big := ⟨_, rfl⟩
  rw [← hEdef]
  have hWd : 2 * E + p.J + Big + 10 ≤ C.Wd := hEdef ▸ wd_E1 c p wt y G
  have hBE : Big + 8 ≤ E := by rw [hEdef]; unfold E1; omega
  have hJE : p.J ≤ E := by rw [hEdef]; unfold E1; omega
  have hnE : 4 * c.n + 1 ≤ E := by rw [hEdef]; unfold E1; omega
  have hnV : 2 ^ (4 * c.n + 1) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hnE
  have hJ1 := J_ge c p wt y G
  have hE1 := hE_ge c p wt y G
  have hrc2 := roleCount_le_two c
  have hvv : p.J * (2 ^ E * (2 * 2 ^ E + 2)) ≤ 2 ^ (p.J + 2 * E + 2) := jvv_le p.J E
  have hvv1 : (p.J + 1) * (2 ^ E * (2 * 2 ^ E + 2)) ≤ 2 ^ (p.J + 1 + 2 * E + 2) := jvv_le (p.J + 1) E
  have hJ8 : 8 * p.J ≤ 2 ^ (p.J + 3) := by
    have : 8 * p.J ≤ 8 * 2 ^ p.J := Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
    rw [pow_add]; omega
  have hp1 : 2 ^ (p.J + 1 + 2 * E + 2) + 2 ^ (p.J + 3) ≤ 2 ^ (p.J + 2 * E + 4) := by
    have h1 : 2 ^ (p.J + 3) ≤ 2 ^ (p.J + 1 + 2 * E + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (p.J + 2 * E + 4) = 2 * 2 ^ (p.J + 1 + 2 * E + 2) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hp2 : 2 ^ (p.J + 2 * E + 4) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hVs : 2 ^ E ≤ 2 ^ (p.J + 2 * E + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun x hx => by rw [hEdef]; exact tailL_le c p wt y G x hx,
    fun x hx => by rw [hEdef]; exact ctrL_le c p wt y G x hx,
    fun x hx => (kxL_le c p wt y G x hx).trans hnV,
    (hE_lt G.bits).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega)),
    (wWin_lt c p wt y G).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega)),
    by unfold wWin; omega,
    pw_fit c p wt y G _ (by unfold nDig; exact (Nat.mul_le_mul_right _ hrc2).trans (by omega)),
    by omega, ?_, Nat.pow_le_pow_right (by norm_num) (by omega), Nat.pow_le_pow_right (by norm_num) (by omega),
    ?_, ?_, fun r => ?_, M1_ge c p wt y G, (M1_lt G.bits).le, A_pos' c p wt y G, (A_lt G.bits).le,
    (Lam_lt G.bits).le, hJ1⟩
  · calc 2 ^ Big * (p.J * (2 ^ E * (2 * 2 ^ E + 2)) + 2 ^ E) ≤ 2 ^ Big * 2 ^ (p.J + 2 * E + 3) := by
          apply Nat.mul_le_mul_left; rw [pow_succ]; omega
      _ = 2 ^ (2 * E + p.J + Big + 3) := by rw [← pow_add]; congr 1; omega
  · rw [show 64 = 2 ^ 6 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [show 8 = 2 ^ 3 by norm_num]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have := topWeight_le_W c r; have := W_le_pow c p wt y G; omega

end NearCubicGates.Close.Cells.SystemsPhase
