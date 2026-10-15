import Proof.Hierarchy.HierarchyProjectionPrefix

/-! The polynomial hierarchy clock's actual arithmetic prefix. Counting and
width production start from the literal framed input; only short binary
powers are multiplied. The stronger quasilinear budget is retained. -/
namespace NearCubicWires.RepairOrdinary.PolynomialClockPower
open LocalBitMultitape RecoveryRootRound SignedSortKey
open HierarchyFromInput (tapes field input countProgram widthProgram boundSlots bound_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputTape (D : ℕ) (hD : 0<D) := boundSlots D (HierarchyBound.powerTape D hD)
noncomputable def powerProgram (D : ℕ) (hD : 0<D) :=
  RecoveryFocus.machine (boundSlots D) (HierarchyBound.powerProgram D hD)
noncomputable def machine (D : ℕ) (hD : 0<D) := Composition.machine
  (Composition.machine (countProgram D) (widthProgram D 1)) (powerProgram D hD)
def budget (D : ℕ) (bits : List Bool) := HierarchyInputLength.budget bits+1+
  HierarchyWidth.budget D 1 bits.length+1+HierarchyPower.fullBudget D 1 bits.length

theorem from_input_run (D : ℕ) (hD : 0<D) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine D hD) (budget D bits) (input D bits) out ∧
      out (outputTape D hD)=frame (binary (HierarchyBinary.width 1 D bits.length) (bits.length^D)) ∧
      out (field D 11)=List.replicate (HierarchyBinary.width 1 D bits.length) true ∧
      out (field D 2)=frame bits := by
  obtain ⟨a,ha,ha0,ha2,hab⟩ := HierarchyFromInput.count_ready D bits
  obtain ⟨b,hb,hb0,hbw,hb2,hbb⟩ := HierarchyFromInput.width_ready D 1 bits a ha0 ha2 hab
  obtain ⟨p,hp,hpf,hpb⟩ := HierarchyBound.power_ready D 1 bits.length hD
  have hi : ∀ j,b (boundSlots D j)=HierarchyBound.input D 1 bits.length j := by
    intro j
    by_cases hj0 : j.val=0
    · simpa [boundSlots,HierarchyBound.input,hj0] using hb0
    by_cases hj1 : j.val=1
    · simpa [boundSlots,HierarchyBound.input,hj0,hj1] using hbw
    simp only [HierarchyBound.input,if_neg hj0,if_neg hj1]
    apply hbb
    simp [boundSlots,hj0,hj1]
    omega
  have hc := hp.focus (boundSlots D) (bound_injective D) b hi
  have hkeep : install (boundSlots D) b p (field D 2)=frame bits := by
    rw [install_other _ _ _ _ (by
      intro j he; have hv := congrArg Fin.val he
      change (boundSlots D j).val=2 at hv
      rw [HierarchyFromInput.bound_val] at hv
      split_ifs at hv <;> omega)]
    exact hb2
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ ha hb) hc,
    (install_slot _ (bound_injective D) _ _ _).trans hpf.1,?_,hkeep⟩
  exact (install_slot _ (bound_injective D) _ _ (HierarchyBound.widthTape D)).trans hpf.2

def coefficient (D : ℕ) := 44+32*HierarchyReduction.shortCoefficient D 1+
  512*(HierarchyReduction.shortCoefficient D 1)^2

theorem budget_bound (D : ℕ) (bits : List Bool) :
    budget D bits ≤ coefficient D*(bits.length+1)*(PCPResourceLedger.ell bits.length+1)^2 := by
  let X := bits.length+1
  let L := PCPResourceLedger.ell bits.length+1
  have hx : 1≤X := by dsimp [X]; omega
  have hl : 1≤L := by dsimp [L]; omega
  have hll : L≤L^2 := by nlinarith
  have hXL : X*L≤X*L^2 := Nat.mul_le_mul_left X hll
  have hL : L≤X*L^2 := by nlinarith
  have hL2 : L^2≤X*L^2 := by nlinarith
  have h1 : 1≤X*L^2 := by nlinarith
  have hc := HierarchyReduction.count_budget bits
  have hw := HierarchyReduction.width_budget D 1 bits.length
  have hp := HierarchyReduction.bound_budget D 1 bits.length
  have hp' : HierarchyPower.fullBudget D 1 bits.length≤HierarchyBound.budget D 1 bits.length := by
    dsimp [HierarchyBound.budget]; omega
  have hc' : HierarchyInputLength.budget bits≤42*(X*L^2) :=
    (show _ ≤42*(X*L) from by simpa only [X,L,Nat.mul_assoc] using hc).trans
      (Nat.mul_le_mul_left _ hXL)
  have hw' : HierarchyWidth.budget D 1 bits.length≤
      (32*HierarchyReduction.shortCoefficient D 1)*(X*L^2) :=
    hw.trans (Nat.mul_le_mul_left _ hL)
  have hp'' : HierarchyPower.fullBudget D 1 bits.length≤
      (512*(HierarchyReduction.shortCoefficient D 1)^2)*(X*L^2) :=
    hp'.trans (hp.trans (Nat.mul_le_mul_left _ hL2))
  change _ ≤coefficient D*X*L^2
  unfold budget coefficient
  nlinarith

end NearCubicWires.RepairOrdinary.PolynomialClockPower
