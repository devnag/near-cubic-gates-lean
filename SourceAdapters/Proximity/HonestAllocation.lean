import SourceAdapters.Proximity.CompilerGrowth

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": arbitrary prepared-word resource demands receive
a polynomial Cells allocation from the physically computed length prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestAllocation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity Growth
variable {Request : Type} (input : Request → List Bool)

def allocation (A D : ℕ) (r : Request) : ℕ :=
  2 ^ (D * leadOnes (LengthPrefix.wrapped (input r))) * A

theorem covers (A D : ℕ) (r : Request) :
    A * ((input r).length + 1) ^ D ≤ allocation input A D r := by
  have hl := LengthPrefix.allocation_covers_length (input r)
  have hp := Nat.pow_le_pow_left (by omega : (input r).length + 1 ≤
    2 ^ leadOnes (LengthPrefix.wrapped (input r))) D
  unfold allocation
  rw [Nat.mul_comm D, pow_mul]
  simpa only [Nat.mul_comm A] using Nat.mul_le_mul_left A hp

theorem bounded (A D : ℕ) : Bounded (fun r => (input r).length) (allocation input A D) :=
  ⟨A * 2 ^ D, D, fun r => LengthPrefix.allocation_bound A D (input r)⟩

theorem positive (A D : ℕ) (hA : 1 ≤ A) (r : Request) : 1 ≤ allocation input A D r := by
  have hp : 1 ≤ 2 ^ (D * leadOnes (LengthPrefix.wrapped (input r))) := Nat.one_le_pow _ _ (by decide)
  exact Nat.mul_le_mul hp hA

theorem sufficient (demand : Request → ℕ) (h : Bounded (fun r => (input r).length) demand) :
    ∃ A D : ℕ, 1 ≤ A ∧ ∀ r, demand r ≤ allocation input A D r := by
  obtain ⟨A, D, hA⟩ := h
  refine ⟨A + 1, D, by omega, fun r => (hA r).trans ((covers input A D r).trans ?_)⟩
  exact Nat.mul_le_mul_left _ (by omega)

theorem compiler_budget_bounded (K : Callee) (A D : ℕ) (N : Request → ℕ)
    (hN : Bounded (fun r => (input r).length) N) :
    Bounded (fun r => (input r).length) (fun r => langBudget K (SourceCallee.uniformSize A D) VV MM
      (LengthPrefix.wrapped (input r)) (N r)) := by
  have halloc := bounded input A D
  have hlead : Bounded (fun r => (input r).length)
      (fun r => leadOnes (LengthPrefix.wrapped (input r))) := by
    simpa only [LengthPrefix.wrapped_leadOnes] using
      (bounded_size (size := fun r => (input r).length)).bitLength
  have hG : Bounded (fun r => (input r).length) (fun r => NearCubicGates.Close.CellsPack.Gof K
      (SourceCallee.uniformSize A D) (leadOnes (LengthPrefix.wrapped (input r)))) := by
    exact (((((((((((halloc.add halloc).add halloc).add hlead).add (bounded_const A)).add
      (bounded_const A)).add (bounded_const A)).add (bounded_const D)).add (bounded_const D)).add
      (bounded_const D)).add (bounded_const (TSK K))).add (bounded_const 1))
  have hinput : Bounded (fun r => (input r).length) (fun r => (LengthPrefix.wrapped (input r)).length) :=
    ((bounded_const 3).mul (bounded_size.add (bounded_const 1))).mono
      (fun r => LengthPrefix.wrapped_length_bound (input r))
  have hbound := ((bounded_const (10 ^ 6)).mul ((hN.add (bounded_const 1)).mul (hG.pow 2))).add
    ((bounded_const 10).mul hinput)
  exact hbound.mono (fun r => NearCubicGates.Close.CellsPack.lang_le2 K (SourceCallee.uniformSize A D)
    (LengthPrefix.wrapped (input r)) (N r))

theorem polynomial (output : Request → List Bool) (K : Callee) (A D : ℕ) (N : Request → ℕ)
    (hN : Bounded (fun r => (input r).length) N)
    (P : WordFunction Request (fun r => LengthPrefix.wrapped (input r)) output
      (fun r => langBudget K (SourceCallee.uniformSize A D) VV MM (LengthPrefix.wrapped (input r)) (N r))) :
    SourcePolyTime input output := by
  obtain ⟨B, d, hB⟩ := compiler_budget_bounded input K A D N hN
  let F : WordFunction Request input (fun r => frame (LengthPrefix.wrapped (input r)))
      (fun r => 10000 * ((input r).length + 1) ^ 2) := {
    program := LengthPrefix.polynomialWordFunction.program
    realizes := fun r => LengthPrefix.polynomialWordFunction.realizes (input r) }
  obtain ⟨C, e, hC⟩ := Code.composeFramed_budget_poly input _ _
    ⟨10000, 2, fun _ => le_rfl⟩ ⟨B, d, hB⟩
  exact ⟨C, e, ⟨(Code.composeFramed F P).enlargeBudget hC⟩⟩

end NearCubicGates.Adapters.Proximity.HonestAllocation
