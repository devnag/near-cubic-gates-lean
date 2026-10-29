import SourceAdapters.Routing.CoordinateMachineInputRun

/-!
# Concrete capacities of the coordinate solver

The construction in `lem:generator`: the polynomial input-width allocation holds
every packed annihilator and coordinate row, and every finite field word.
All bounds follow from the request hypotheses, with no runtime-capacity premise.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL

theorem prepared_solver_bounds (p : CoordReq) (h : CoordOk p) :
    let G := globOf (preparedInput (coordInput p))
    p.m + 1 ≤ G.N ∧ p.f ≤ G.N ∧ p.f * (p.m + 1) ≤ G.K ∧ p.f + 2 ≤ G.K ∧
      2 ^ p.f ≤ G.cap ∧ 2 ≤ G.cap := by
  intro G
  let n := (coordInput p).length
  have hf : p.f ≤ n := coordInput_field_le p h
  have hm : p.m + 1 ≤ p.f := by have := h.2.2.2; omega
  have hk4 : 4 * n + 4 ≤ G.K := prepared_K_lower (coordInput p)
  have hk6 : 2 * (2 * n + 2) ^ 6 ≤ G.K := prepared_K_power_lower (coordInput p)
  have hnK : n + 2 ≤ G.K := by omega
  have hKN : G.N = G.K := rfl
  have hprod : p.f * (p.m + 1) ≤ n * n := Nat.mul_le_mul hf (hm.trans hf)
  have hsq : n * n ≤ (2 * n + 2) ^ 6 := by
    calc n * n = n ^ 2 := by ring
      _ ≤ (2 * n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 * n + 2) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hfield : p.f + 2 ≤ G.K := by omega
  have hpow : 2 ^ p.f < 2 ^ G.K := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcap := cap_add G
  have hsmall := cap_ge G
  exact ⟨by omega, by omega, by omega, hfield, by omega, by omega⟩

theorem prepared_stage_bounds (p : CoordReq) (h : CoordOk p) (n : ℕ) (hn : n < p.m) :
    let G := globOf (preparedInput (coordInput p))
    n + 2 ≤ p.m + 1 ∧ n + 2 ≤ G.N ∧ p.f * (n + 2) ≤ G.K := by
  intro G
  have hb := prepared_solver_bounds p h
  have hn' : n + 2 ≤ p.m + 1 := by omega
  exact ⟨hn', hn'.trans hb.1, (Nat.mul_le_mul_left p.f hn').trans hb.2.2.1⟩

end NearCubicGates.Adapters.Routing.CoordinateMachine
