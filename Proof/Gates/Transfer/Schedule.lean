import Proof.Gates.Interfaces.TransferParts
import Proof.CaseAnalysis.ScheduleBounds

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary NearCubicGates.Close.Gadget

namespace GateParams
variable (s : GateSources) (g : GateParams)

/-- The native width at `N_ν` is at least `ν + 1`. -/
theorem width_lower (ν : ℕ) : ν + 1 ≤ g.width s ν := g.nu_lt_width s ν

/-- The jump bound of the native width: `(k+2)(A_pad+1)`. -/
noncomputable def widthJump : ℕ := (g.k + 2) * (Outer.apad s.mw (g.sv s) + 1)

/-- One doubling of the source length moves the native width by a bounded amount. -/
theorem width_step (ν : ℕ) : g.width s (ν + 1) ≤ g.width s ν + g.widthJump s := by
  unfold width widthJump Outer.width
  exact Outer.widthOf_step _ _ ν

/-- The jump bound of the core arity. -/
noncomputable def coreJump : ℕ :=
  let j := g.widthJump s
  g.ampFactor * (j + g.clauseDegree * natBitLength (j + 1))

theorem coreArity_lower (hamp : 1 ≤ g.ampFactor) (ν : ℕ) : ν + 1 ≤ g.coreArity s ν := by
  have hw := g.width_lower s ν
  have : g.width s ν ≤ g.coreArity s ν := by
    unfold coreArity tableArity
    calc g.width s ν ≤ g.width s ν + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog := by omega
      _ ≤ g.ampFactor * _ := Nat.le_mul_of_pos_left _ hamp
  omega

theorem coreArity_step (ν : ℕ) : g.coreArity s (ν + 1) ≤ g.coreArity s ν + g.coreJump s := by
  have hq := g.width_step s ν
  have hc := clause_step g.clauseDegree (g.width s ν) (g.width s (ν + 1)) (g.widthJump s) hq
  unfold coreArity tableArity coreJump
  simp only
  nlinarith

end GateParams

variable {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ}

/-- **SelectionFacts** hold for every closure. -/
theorem selectionFacts (c : GateClosure s P ε) : SelectionFacts c := by
  classical
  have hamp := c.ready.ampPos
  constructor
  · intro N0
    refine ⟨2 * c.g.coreArity s (N0 + 1) + (N0 + 1), fun n hn => ?_⟩
    have := selected_ge (c.g.coreArity s) (N0 + 1) n (by omega) hn
    unfold GateParams.selected
    omega
  · obtain ⟨n1, hn1⟩ : ∃ n1, ∀ n, n1 ≤ n → c.g.sourceOnset ≤ 2 ^ c.g.selected s n ∧ 1 ≤ c.g.selected s n := by
      refine ⟨2 * c.g.coreArity s (c.g.sourceOnset + 1) + (c.g.sourceOnset + 1), fun n hn => ?_⟩
      have h := selected_ge (c.g.coreArity s) (c.g.sourceOnset + 1) n (by omega) hn
      unfold GateParams.selected
      refine ⟨le_trans (by omega) (Nat.lt_two_pow_self).le, by omega⟩
    refine ⟨n1, fun n hn => ?_⟩
    obtain ⟨hsrc, h1⟩ := hn1 n hn
    refine ⟨h1, hsrc, ?_⟩
    have hfit := selectedIndex_fits (c.g.coreArity s) n (by unfold GateParams.selected at h1; omega)
    unfold GateParams.nativeLength GateParams.selected
    exact min_eq_left (le_trans hfit.2 (Nat.div_le_self n 2))

/-- The length bound `n ≤ 5·q(n)` at large `n`. -/
theorem lengthBound (c : GateClosure s P ε) :
    ∃ onset : ℕ, ∀ n, onset ≤ n → n ≤ 5 * c.g.nativeLength s n := by
  classical
  have hamp := c.ready.ampPos
  obtain ⟨o, ho⟩ := (selectionFacts c).2
  refine ⟨max o (6 * c.g.coreJump s + 6), fun n hn => ?_⟩
  obtain ⟨h1, -, hlen⟩ := ho n (le_trans (le_max_left _ _) hn)
  have hf := selected_fraction (c.g.coreArity s) (c.g.coreJump s) (c.g.coreArity_lower s hamp)
    (c.g.coreArity_step s) n (le_trans (le_max_right _ _) hn) (by unfold GateParams.selected at h1; omega)
  rw [hlen]
  unfold GateParams.selected
  have hpos := c.g.coreArity_lower s hamp (selectedIndex (c.g.coreArity s) n)
  omega

end NearCubicGates.Close.Transfer
