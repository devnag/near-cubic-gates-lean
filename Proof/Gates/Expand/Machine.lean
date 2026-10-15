import Proof.Gates.Expand.Cost7

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem Zq_eq (r : FormulaReq) : Zq r = (r.1 + 2) ^ (2 * r.2.degree + 3) *
    ((formulaWord r).length + r.2.size + r.2.weight + 1) ^ 8 := by
  unfold Zq Mq Vq Pq
  rw [← pow_mul, mul_comm r.2.degree 2, pow_add]

/-- **The cost class.** -/
theorem budget_le (r : FormulaReq) : budget r ≤ 10 ^ 11 * (r.1 + 2) ^ (2 * r.2.degree + 3) *
    ((formulaWord r).length + r.2.size + r.2.weight + 1) ^ 8 := by
  have a := stageA_le r
  have b := stageB_le r
  have c := core_le r
  have d := cleanup_le r
  have hZ : 1 ≤ Zq r := by
    have f := facts r
    unfold Zq; exact Nat.one_le_iff_ne_zero.mpr (by have := f.v2; have := f.p1; have := f.m1; positivity)
  rw [mul_assoc, ← Zq_eq]
  unfold budget
  omega

end NearCubicGates.Close.Expand.Layout

namespace NearCubicGates.Close.Expand

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats Layout

noncomputable def expansionMachine : ExpandMachine where
  expand r := expandM r.2
  ok r := expandM_ok r.2
  budget := budget
  wf := expansionMachineWF
  cls := ⟨10 ^ 11, 8, budget_le⟩

end NearCubicGates.Close.Expand
