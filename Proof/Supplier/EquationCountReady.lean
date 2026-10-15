import Proof.Supplier.EquationCountCapacity

/-! The complete count/capacity bank is produced from d,p,G,odd alone.
No output count, scalar width or erase capacity is supplied to this caller. -/
namespace NearCubicWires.RepairOrdinary.EquationCountReady
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (d p g : ℕ) (odd : Bool) : Fin 32 → List Bool :=
  fun i => if i.val=0 then UnaryTemplate.tape d else if i.val=1 then UnaryTemplate.tape p
    else if i.val=2 then UnaryTemplate.tape g else if i.val=3 then [odd] else []
def slots (i : Fin 16) : Fin 32 := i.castAdd 16
noncomputable def first := RecoveryFocus.machine slots EquationCountCopies.machine
noncomputable def machine := Composition.machine first EquationCountCapacity.machine
def budget (d p g : ℕ) := EquationCountCopies.budget d p g+1+EquationCountCapacity.budget d p g

theorem copies_ready (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun first (EquationCountCopies.budget d p g)
      (input d p g odd) (EquationCountCapacity.input d p g odd) := by
  have h := bounded_focus slots (by decide) _ _ _ (EquationCountCopies.copies_ready d p g odd)
    (input d p g odd) (by intro i; fin_cases i <;> rfl)
  have ho : install slots (input d p g odd) (EquationCountCopies.data6 d p g odd)=
      EquationCountCapacity.input d p g odd := by
    apply HierarchyWidth.install_eq _ (by decide)
    · intro i
      change Fin.addCases (m := 16) (n := 16) (motive := fun _ => List Bool)
        (EquationCountCopies.data6 d p g odd) (fun _ => []) (i.castAdd 16)=_
      rw [Fin.addCases_left]
    · intro i hi
      have hv : 16 ≤ i.val := by
        by_contra hh
        exact hi ⟨i.val,by omega⟩ (Fin.ext rfl)
      have he : i=(⟨i.val-16,by omega⟩ : Fin 16).natAdd 16 := by apply Fin.ext; simp; omega
      rw [he]
      simp only [EquationCountCapacity.input,Fin.addCases_right]
      simp [input]
  rw [ho] at h
  exact h

theorem ready (d p g : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun machine (budget d p g) (input d p g odd)
      (EquationCountCapacity.data8 d p g odd) :=
  ClockJoin.join _ _ _ _ _ _ _ (copies_ready d p g odd) (EquationCountCapacity.capacity_ready d p g odd)

theorem capacity_budget (d p g : ℕ) :
    EquationCountCapacity.budget d p g ≤ 4096*(d+p+g+1)^2 := by
  let q := d+p+g+1
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hd : 2*d+1 ≤ 2*q := by dsimp [q]; omega
  have hp : p+1 ≤ q := by dsimp [q]; omega
  have hm := Nat.mul_le_mul hd hp
  have he : EquationCountCapacity.budget d p g=
      8*d+8*g+6*(2*d+1)+522*(2*d+1)*(p+1)+307 := by
    unfold EquationCountCapacity.budget
    ring
  rw [he]
  change _ ≤ 4096*q^2
  have hsum : d+g ≤ q := by dsimp [q]; omega
  nlinarith

theorem budget_polynomial (d p g : ℕ) : budget d p g ≤ 8192*(d+p+g+1)^2 := by
  have h := capacity_budget d p g
  have hq : 1 ≤ d+p+g+1 := by omega
  unfold budget EquationCountCopies.budget
  nlinarith

end NearCubicWires.RepairOrdinary.EquationCountReady
