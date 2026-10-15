import Proof.PCP.PCPPNativeClauseFullBody

/-! Discharge the original clause reader/printer capacities from the same
measured envelope and physical quadratic driver used by the native query
bank. The inequalities refer to the actual scalar/literal inputs. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseCapacity
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_capacity (bits : List Bool) (index : ℕ) (sign : Bool) (stride p n W C : ℕ)
    (hv : value bits=2*index+sign.toNat) (hi : index≤W) (hs : stride≤W)
    (hp : p≤W) (hn : n≤W) (hl : bits.length≤W) (hC : 16384*(W+1)^2≤C) :
    PCPPNativeClauseField.budget bits index sign stride p n+1≤C := by
  have hsign : sign.toNat≤1 := by cases sign <;> decide
  have href:=PCPPNativeClauseReference.budget_bound index sign stride p n
  have hprod : (index+1)*(stride+p+n+1)≤(W+1)*(3*W+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hunary : (value bits+1)*(bits.length+1)≤(2*W+2)*(W+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold PCPPNativeClauseField.budget PCPPNativeClauseField.readBudget RepairSource.ProjectionNormalization.Unary.budget
  nlinarith

theorem sum_capacity (x y W C : ℕ) (hs : x+y≤W+1) (hC : 16384*(W+1)^2≤C) :
    PCPPNativeSumAppend.budget x y+1≤C := by
  have hb:=PCPPNativeSumAppend.budget_bound x y
  have hp : (x+y+1)^2≤(W+2)^2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

theorem block_capacity (base accumulator W C : ℕ) (refs : Fin 3→ℕ)
    (hb : base≤W) (ha : accumulator≤W) (hr : ∀ j,refs j≤W)
    (hC : 16384*(W+1)^2≤C) :
    PCPPNativeClauseBank.Capacity (PCPPNativeClauseBank.values base accumulator refs) C := by
  have h0:=hr 0; have h1:=hr 1; have h2:=hr 2
  exact ⟨sum_capacity 0 (refs 0) W C (by omega) hC,
    sum_capacity 0 (refs 1) W C (by omega) hC,
    sum_capacity 0 base W C (by omega) hC,
    sum_capacity 0 (refs 2) W C (by omega) hC,
    sum_capacity 0 accumulator W C (by omega) hC,
    sum_capacity 1 base W C (by omega) hC⟩

theorem width_le_capacity (W C : ℕ) (hC : 16384*(W+1)^2≤C) : W≤C := by nlinarith

end NearCubicWires.RepairOrdinary.PCPPNativeClauseCapacity
