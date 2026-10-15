import Proof.MachineModel.OrdinaryWilliamsUnaryProduct

/-! Fixed-degree unary powering for the supported Williams dimension.
There are two fresh tapes per multiplication, and every previous power and
the physically produced factor are retained. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPower
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 2+2*D
def previous : ℕ → ℕ | 0 => 1 | j+1 => 2+2*j
theorem previous_bounds (j : ℕ) : 1≤previous j ∧ previous j<2+2*j := by
  cases j <;> simp [previous]; omega
def block (D : ℕ) (j : Fin D) (k : Fin 2) : Fin (tapes D) :=
  ⟨2+2*j.val+k.val,by dsimp [tapes]; omega⟩
def operand (D : ℕ) (j : Fin D) : Fin (tapes D) :=
  ⟨previous j.val,by have := previous_bounds j.val; dsimp [tapes]; omega⟩
def factor (D : ℕ) : Fin (tapes D) := ⟨0,by simp [tapes]⟩
def slot (D : ℕ) (j : Fin D) : Fin 4 → Fin (tapes D) :=
  ![operand D j,factor D,block D j 0,block D j 1]

theorem slot_injective (D : ℕ) (j : Fin D) : Function.Injective (slot D j) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  have hp := previous_bounds j.val
  fin_cases a <;> fin_cases b <;> simp [slot,operand,factor,block] at he ⊢ <;> omega

theorem slot_upper (D : ℕ) (j : Fin D) (i : Fin 4) :
    (slot D j i).val<2+2*(j.val+1) := by
  have hp := previous_bounds j.val
  fin_cases i <;> simp [slot,operand,factor,block] <;> omega

def Input (D c : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool) : Prop :=
  ambient (factor D)=UnaryTemplate.tape c ∧
  ambient (operand D j)=List.replicate (c^j.val) true ∧
  ∀ i,2+2*j.val ≤ i.val → ambient i=[]

noncomputable def program (D : ℕ) (j : Fin D) : Machine (tapes D) 7 :=
  RecoveryFocus.machine (slot D j) ClockUnaryProduct.machine

theorem input_slots (D c : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool)
    (hin : Input D c j ambient) (i : Fin 4) :
    ambient (slot D j i)=WilliamsUnaryProduct.input (c^j.val) c i := by
  fin_cases i
  · exact hin.2.1
  · exact hin.1
  · exact hin.2.2 _ (by simp [slot,block])
  · exact hin.2.2 _ (by simp [slot,block])

def stepBudget (D c : ℕ) := 10*c^D+6

theorem call_budget (D c : ℕ) (j : Fin D) (hc : 1≤c) :
    WilliamsUnaryProduct.budget (c^j.val) c ≤ stepBudget D c := by
  have hp : c^j.val≤c^D := Nat.pow_le_pow_right hc j.isLt.le
  have hn : c^(j.val+1)≤c^D := Nat.pow_le_pow_right hc (by omega)
  have he := pow_succ c j.val
  unfold WilliamsUnaryProduct.budget stepBudget
  nlinarith

theorem step_run (D c : ℕ) (j : Fin D) (hc : 1≤c)
    (ambient : Fin (tapes D) → List Bool) (hin : Input D c j ambient) :
    ∃ r : ExecutionReceipt (tapes D) 7,
      run (program D j) (stepBudget D c) ambient=some r ∧
      r.final.tapes (slot D j 2)=List.replicate (c^(j.val+1)) true ∧
      r.final.tapes (factor D)=UnaryTemplate.tape c ∧
      (∀ i,2+2*(j.val+1) ≤ i.val → r.final.tapes i=[]) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ stepBudget D c := by
  have ready := (WilliamsUnaryProduct.product_ready (c^j.val) c).focus
    (slot D j) (slot_injective D j) ambient (input_slots D c j ambient hin)
  obtain ⟨r,hr,ht,hh,hs⟩ := ready
  have hbound := call_budget D c j hc
  have hm := run_moreFuel (program D j) (WilliamsUnaryProduct.budget (c^j.val) c)
    (stepBudget D c-WilliamsUnaryProduct.budget (c^j.val) c) ambient r hr
  rw [Nat.add_sub_of_le hbound] at hm
  have hslot (i : Fin 4) : r.final.tapes (slot D j i)=WilliamsUnaryProduct.output (c^j.val) c i := by
    rw [ht,install_slot _ (slot_injective D j)]
  refine ⟨r,hm,?_,hslot 1,?_,hh,hs.trans_le hbound⟩
  · rw [hslot]
    simp [WilliamsUnaryProduct.output,pow_succ]
  · intro i hi
    rw [ht,install_other]
    · exact hin.2.2 i (by omega)
    · intro k he
      have hb := slot_upper D j k
      have hv := congrArg Fin.val he
      omega

end NearCubicWires.RepairOrdinary.WilliamsPower
