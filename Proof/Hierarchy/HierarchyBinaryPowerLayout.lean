import Proof.Hierarchy.HierarchyBinaryMultiply

/-! Fixed-degree powering uses a fresh finite block of work tapes per
multiply. Previously produced powers, the original factor and width are
retained. The number of blocks is fixed with the hierarchy program. -/
namespace NearCubicWires.RepairOrdinary.HierarchyPower
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 7+11*D
def previous : ℕ → ℕ | 0 => 2 | j+1 => 9+11*j
theorem previous_bounds (j : ℕ) : 2≤previous j ∧ previous j<7+11*j := by
  cases j <;> simp [previous]; omega
def block (D : ℕ) (j : Fin D) (k : Fin 11) : Fin (tapes D) :=
  ⟨7+11*j.val+k.val,by dsimp [tapes]; omega⟩
def operand (D : ℕ) (j : Fin D) : Fin (tapes D) :=
  ⟨previous j.val,by have := previous_bounds j.val; dsimp [tapes]; omega⟩
def slot (D : ℕ) (j : Fin D) : Fin 14 → Fin (tapes D) :=
  fun i => if h0 : i.val=0 then ⟨0,by simp [tapes]⟩
    else if h8 : i.val=8 then operand D j
    else if h9 : i.val=9 then ⟨1,by dsimp [tapes]; omega⟩
    else if hi : i.val<8 then block D j ⟨i.val-1,by omega⟩
    else block D j ⟨i.val-3,by omega⟩

theorem slot_injective (D : ℕ) (j : Fin D) : Function.Injective (slot D j) := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  have hp := previous_bounds j.val
  fin_cases a <;> fin_cases b <;> simp [slot,block,operand] at he ⊢ <;> omega

theorem slot_upper (D : ℕ) (j : Fin D) (i : Fin 14) :
    (slot D j i).val<7+11*(j.val+1) := by
  have hp := previous_bounds j.val
  fin_cases i <;> simp [slot,block,operand] <;> omega

def Input (D C n : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool) : Prop :=
  ambient ⟨0,by simp [tapes]⟩=frame (ClockBinary.word n) ∧
  ambient ⟨1,by dsimp [tapes]; omega⟩=List.replicate (HierarchyBinary.width C D n) true ∧
  ambient (operand D j)=frame (binary (HierarchyBinary.width C D n) (n^j.val)) ∧
  ∀ i,7+11*j.val ≤ i.val → ambient i=[]

noncomputable def program (D : ℕ) (j : Fin D) :=
  RecoveryFocus.machine (slot D j) HierarchyMultiplyEntry.machine

theorem input_slots (D C n : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool)
    (h : Input D C n j ambient) (i : Fin 14) :
    ambient (slot D j i)=HierarchyMultiplyEntry.input14 (HierarchyBinary.width C D n)
      (n^j.val) (ClockBinary.word n) i := by
  fin_cases i
  · exact h.1
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.1
  · exact h.2.1
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])
  · exact h.2.2.2 _ (by simp [slot,block])

def stepBudget (D C n : ℕ) :=
  128*(HierarchyBinary.width C D n+1)*(PCPResourceLedger.ell n+1)

theorem step_run (D C n : ℕ) (j : Fin D) (ambient : Fin (tapes D) → List Bool)
    (hin : Input D C n j ambient) :
    ∃ r : ExecutionReceipt (tapes D)
        (20+Fintype.card (RecoveryCalls.Control HierarchyMultiply.sizes)+2),
      run (program D j) (stepBudget D C n) ambient=some r ∧
      r.final.tapes (slot D j 3)=frame (binary (HierarchyBinary.width C D n) (n^(j.val+1))) ∧
      r.final.tapes (slot D j 0)=frame (ClockBinary.word n) ∧
      r.final.tapes (slot D j 9)=List.replicate (HierarchyBinary.width C D n) true ∧
      (∀ i,7+11*(j.val+1) ≤ i.val → r.final.tapes i=[]) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ stepBudget D C n := by
  have hfit : n^j.val*2^(ClockBinary.word n).length<2^HierarchyBinary.width C D n := by
    rw [ClockDyadicLedger.bit_width]
    exact HierarchyBinary.power_call_fit C D n j.val j.isLt
  obtain ⟨base,hb,hout,hfactor,_,hwidth,_,hh,hs⟩ :=
    HierarchyMultiplyEntry.multiply_run (HierarchyBinary.width C D n) (n^j.val) (ClockBinary.word n) hfit
  have ht : HierarchyMultiplyEntry.budget (HierarchyBinary.width C D n) (ClockBinary.word n)=stepBudget D C n := by
    simp only [HierarchyMultiplyEntry.budget,stepBudget,ClockDyadicLedger.bit_width]
  rw [ht] at hb hs
  have hi := slot_injective D j
  obtain ⟨r,hr,hf,hrs⟩ := RecoveryFocus.run_config (slot D j) hi HierarchyMultiplyEntry.machine
    (fun _ => 0) ambient (stepBudget D C n) _ base hb
  have hinit : RecoveryFocus.config (slot D j) (fun _ => 0) ambient
      (initialConfiguration HierarchyMultiplyEntry.machine
        (HierarchyMultiplyEntry.input14 (HierarchyBinary.width C D n) (n^j.val) (ClockBinary.word n)))=
      initialConfiguration (program D j) ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick (slot D j) i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing (slot D j) ambient _ (input_slots D C n j ambient hin)
  rw [hinit] at hr
  have hslot (i : Fin 14) : r.final.tapes (slot D j i)=base.final.tapes i := by
    rw [hf]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ hi]
  refine ⟨r,hr,?_,(hslot 0).trans hfactor,(hslot 9).trans hwidth,?_,?_,hrs.trans_le hs⟩
  · rw [hslot,hout,ClockBinary.word_value,pow_succ]
  · intro i hfuture
    have hnone : ∀ l : Fin 14,slot D j l≠i := by
      intro l he
      have hl := slot_upper D j l
      have hv := congrArg Fin.val he
      omega
    rw [hf]
    change install (slot D j) ambient base.final.tapes i=[]
    rw [install_other _ _ _ _ hnone]
    exact hin.2.2.2 i (by omega)
  · intro i
    rw [hf]
    cases hp : RecoveryFocus.pick (slot D j) i <;> simp [RecoveryFocus.config,hp,hh]

end NearCubicWires.RepairOrdinary.HierarchyPower
