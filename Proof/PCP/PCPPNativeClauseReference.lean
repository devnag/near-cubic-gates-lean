import Proof.PCP.PCPPNativeClauseReferenceLayout

/-! A fixed ordinary program computes the literal reference from the actual
code template and stride/offset counters, retaining every original parameter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem product_ready (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    ClockJoin.ReadyRun productMachine (2*(index*(2*stride+3)+2)+2)
      (selectedData index sign stride p n) (productData index sign stride p n) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=WilliamsUnaryProduct.product_ready index stride
  have base : ClockJoin.ReadyRun ClockUnaryProduct.machine _ _ _ := ⟨r,hr,ht,hh,hs.le⟩
  have hf:=base.focus productSlots product_injective (selectedData index sign stride p n)
    (by intro j; fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq productSlots product_injective (selectedData index sign stride p n)
    (productData index sign stride p n) (WilliamsUnaryProduct.output index stride)
    (by intro j; fin_cases j <;> rfl) (by
      intro i hi
      have h9 : i≠9 := fun h=>hi 2 (by rw [h]; rfl)
      have h10 : i≠10 := fun h=>hi 3 (by rw [h]; rfl)
      simp [productData,h9,h10])
  rw [he] at hf
  exact hf

theorem sum_ready (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    ClockJoin.ReadyRun sumMachine (2*(index*stride+offset sign p n)+6)
      (productData index sign stride p n) (output index sign stride p n) := by
  have base:=ClockUnarySum.sum_ready (index*stride) (offset sign p n)
  have hf:=base.focus sumSlots sum_injective (productData index sign stride p n)
    (by intro j; fin_cases j <;> rfl)
  have he:=HierarchyWidth.install_eq sumSlots sum_injective (productData index sign stride p n)
    (output index sign stride p n)
    ![List.replicate (index*stride) true,List.replicate (offset sign p n) true,
      List.replicate (index*stride+offset sign p n) true,List.replicate (index*stride+offset sign p n+2) false]
    (by intro j; fin_cases j <;> rfl) (by
      intro i hi
      have h11 : i≠11 := fun h=>hi 2 (by rw [h]; rfl)
      have h12 : i≠12 := fun h=>hi 3 (by rw [h]; rfl)
      simp [output,h11,h12])
  rw [he] at hf
  exact hf

def budget (index : ℕ) (sign : Bool) (stride p n : ℕ) :=
  6*index*stride+10*index+4*offset sign p n+2*sign.toNat+27

theorem ready_run (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    ClockJoin.ReadyRun machine (budget index sign stride p n)
      (input index sign stride p n) (output index sign stride p n) := by
  have ha:=ClockJoin.join _ _ _ _ _ _ _ (split_ready index sign stride p n) (select_ready index sign stride p n)
  have hb:=ClockJoin.join _ _ _ _ _ _ _ ha (product_ready index sign stride p n)
  have hc:=ClockJoin.join _ _ _ _ _ _ _ hb (sum_ready index sign stride p n)
  have he : ((4*index+2*sign.toNat+6)+1+(2*offset sign p n+6))+1+
      (2*(index*(2*stride+3)+2)+2)+1+(2*(index*stride+offset sign p n)+6)=
      budget index sign stride p n := by unfold budget; ring
  rw [he] at hc
  exact hc

theorem budget_bound (index : ℕ) (sign : Bool) (stride p n : ℕ) :
    budget index sign stride p n ≤ 32*(index+1)*(stride+p+n+1) := by
  have hoff : offset sign p n ≤ p+n := by cases sign <;> simp [offset,PCPPNativeClauseOffset.value]
  have hsign : sign.toNat ≤ 1 := by cases sign <;> decide
  unfold budget
  nlinarith [Nat.zero_le (index*p),Nat.zero_le (index*n),Nat.zero_le (index*stride)]

theorem reference_meaning (index size originalOutput : ℕ) (sign : Bool) :
    output index sign (2*size+1) (2*originalOutput+1) (2*size) 11=
      List.replicate (PCPPSubstitution.queryAddress 0 size originalOutput index sign) true := by
  simp [output,offset,PCPPNativeClauseOffset.value,PCPPSubstitution.queryAddress,PCPPSubstitution.queryOffset]

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReference
