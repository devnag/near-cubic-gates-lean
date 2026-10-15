import Proof.Circuits.DecompositionCountDrivers

/-! The actual total integer count is the product of the two native header
counts. Its raw product and counted loop word are physically produced. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCountDrivers
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def total (a m : ℕ) := (a+1)*m
def data4 (a m : ℕ) : Store := fun i =>
  if i.val=8 then List.replicate (total a m) true
  else if i.val=9 then List.replicate (WilliamsUnaryProduct.scratch (a+1) m) false
  else data3 a m i
def data5 (a m : ℕ) : Store := fun i =>
  if i.val=10 then UnaryTemplate.tape (total a m)
  else if i.val=11 then List.replicate (total a m+3) false else data4 a m i
def output (a m : ℕ) : Store := fun i =>
  if i.val=12 then CompareMachine.word (total a m)
  else if i.val=13 then List.replicate (total a m+2) false else data5 a m i
def slots4 : Fin 4 → Fin 14 := ![2,1,8,9]
def slots5 : Fin 3 → Fin 14 := ![8,10,11]
def slots6 : Fin 3 → Fin 14 := ![10,12,13]
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def phase5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine false)
noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine true false)
noncomputable def products := Composition.machine (Composition.machine phase4 phase5) phase6
noncomputable def machine := Composition.machine copies products
def productBudget (a m : ℕ) := WilliamsUnaryProduct.budget (a+1) m+4*total a m+16
def budget (a m : ℕ) := copiesBudget a m+1+productBudget a m

theorem ready4 (a m : ℕ) : ClockJoin.ReadyRun phase4
    (WilliamsUnaryProduct.budget (a+1) m) (data3 a m) (data4 a m) := by
  have hp : ClockJoin.ReadyRun ClockUnaryProduct.machine (WilliamsUnaryProduct.budget (a+1) m)
      (WilliamsUnaryProduct.input (a+1) m) (WilliamsUnaryProduct.output (a+1) m) := by
    obtain ⟨r,hr,ht,hh,hs⟩ := WilliamsUnaryProduct.product_ready (a+1) m
    exact ⟨r,hr,ht,hh,hs.le⟩
  have h := hp.focus slots4 (by decide) (data3 a m) (by intro j; fin_cases j <;> rfl)
  have ho : install slots4 (data3 a m) (WilliamsUnaryProduct.output (a+1) m)=data4 a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h8 : i.val≠8 := fun he => hi 2 (Fin.ext he.symm)
      have h9 : i.val≠9 := fun he => hi 3 (Fin.ext he.symm)
      simp only [data4,h8,h9,ite_false]
  rw [ho] at h
  exact h

theorem ready5 (a m : ℕ) : ClockJoin.ReadyRun phase5
    (2*total a m+8) (data4 a m) (data5 a m) := by
  have h := (DimensionTemplate.ready false (total a m)).focus slots5 (by decide) (data4 a m)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots5 (data4 a m) (DimensionTemplate.output false (total a m))=data5 a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h10 : i.val≠10 := fun he => hi 1 (Fin.ext he.symm)
      have h11 : i.val≠11 := fun he => hi 2 (Fin.ext he.symm)
      simp only [data5,h10,h11,ite_false]
  rw [ho] at h
  exact h

theorem ready6 (a m : ℕ) : ClockJoin.ReadyRun phase6
    (2*total a m+6) (data5 a m) (output a m) := by
  have h := (template_ready true false (total a m)).focus slots6 (by decide) (data5 a m)
    (by intro j; fin_cases j <;> rfl)
  have ho : install slots6 (data5 a m)
      ![UnaryTemplate.tape (total a m),UWalkUnary.output true false (total a m),
        List.replicate (total a m+2) false]=output a m := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      have h12 : i.val≠12 := fun he => hi 1 (Fin.ext he.symm)
      have h13 : i.val≠13 := fun he => hi 2 (Fin.ext he.symm)
      simp only [output,h12,h13,ite_false]
  rw [ho] at h
  exact h

theorem products_ready (a m : ℕ) : ClockJoin.ReadyRun products
    (productBudget a m) (data3 a m) (output a m) := by
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ready4 a m) (ready5 a m)) (ready6 a m)
  have he : productBudget a m=(WilliamsUnaryProduct.budget (a+1) m+1+
      (2*total a m+8))+1+(2*total a m+6) := by
    unfold productBudget
    omega
  rw [he]
  exact h

theorem counts_ready (a m : ℕ) : ClockJoin.ReadyRun machine (budget a m) (input a m) (output a m) :=
  ClockJoin.join _ _ _ _ _ _ _ (copies_ready a m) (products_ready a m)

theorem budget_bound (a m : ℕ) : budget a m ≤ 64*(a+1)*(m+1)+64 := by
  unfold budget copiesBudget productBudget WilliamsUnaryProduct.budget total
  nlinarith

end NearCubicWires.RepairOrdinary.DecompositionCountDrivers
