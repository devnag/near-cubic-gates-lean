import Proof.Hierarchy.HierarchyBinaryKernel

/-! The actual scalar calls in a shift/add multiplication round. The physical
factor cursor is retained across every add, copy and reset. -/
namespace NearCubicWires.RepairOrdinary.HierarchyMultiply
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  left : ℕ
  duplicate : ℕ
  accumulator : ℕ
  sum : List Bool
  doubled : List Bool

def Store.tapes (s : Store) (w : ℕ) (source : List Bool) : Fin 8 → List Bool :=
  ![source,frame (binary w s.left),frame (binary w s.duplicate),frame (binary w s.accumulator),
    s.sum,s.doubled,List.replicate (2*w+1) false,List.replicate (4*w+3) false]
def heads (pos : ℕ) : Fin 8 → ℕ := ![pos,0,0,0,0,0,0,0]
def added (s : Store) (w : ℕ) : Store := {s with sum := frame (binary w (s.left+s.accumulator))}
def accumulated (s : Store) : Store := {s with accumulator := s.left+s.accumulator}
def doubled (s : Store) (w : ℕ) : Store := {s with doubled := frame (binary w (s.left+s.duplicate))}
def shiftedLeft (s : Store) : Store := {s with left := s.left+s.duplicate}
def shiftedBoth (s : Store) : Store := {s with left := s.left+s.duplicate,duplicate := s.left+s.duplicate}

def addSlots : Fin 4 → Fin 8 := ![1,3,4,7]
def accSlots : Fin 4 → Fin 8 := ![4,3,6,7]
def doubleSlots : Fin 4 → Fin 8 := ![1,2,5,7]
def leftSlots : Fin 4 → Fin 8 := ![5,1,6,7]
def duplicateSlots : Fin 4 → Fin 8 := ![5,2,6,7]
noncomputable def addProgram := RecoveryFocus.machine addSlots BoundaryAdvance.machine
noncomputable def accProgram := RecoveryFocus.machine accSlots copyMachine
noncomputable def doubleProgram := RecoveryFocus.machine doubleSlots BoundaryAdvance.machine
noncomputable def leftProgram := RecoveryFocus.machine leftSlots copyMachine
noncomputable def duplicateProgram := RecoveryFocus.machine duplicateSlots copyMachine

def Run {states : ℕ} (p : Machine 8 states) (time w pos : ℕ) (source : List Bool)
    (before after : Store) : Prop :=
  ∃ r : ExecutionReceipt 8 states,
    runFrom p time (RecoveryCalls.restarted p (heads pos) (before.tapes w source))=some r ∧
    r.final.heads=heads pos ∧ r.final.tapes=after.tapes w source ∧ r.steps=time

theorem add_run (s : Store) (w pos : ℕ) (source : List Bool)
    (hfit : s.left+s.accumulator<2^w) (hb : s.sum.length≤2*w+1) :
    Run addProgram (4*w+4) w pos source s (added s w) := by
  have hr := HierarchyBinary.add_ready w s.left s.accumulator (4*w+3) s.sum hfit hb
  simp only [max_eq_left (by omega : 2*w+1≤4*w+3)] at hr
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run addSlots (by decide) _ _ _ hr
    (heads pos) (s.tapes w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot addSlots (by decide) _ _ 0
    | exact install_slot addSlots (by decide) _ _ 1
    | exact install_slot addSlots (by decide) _ _ 2
    | exact install_slot addSlots (by decide) _ _ 3
    | exact install_other addSlots _ _ _ (by decide)

theorem accumulate_run (s : Store) (w pos : ℕ) (source : List Bool) :
    Run accProgram (8*w+8) w pos source (added s w) (accumulated (added s w)) := by
  have hr := copy_ready (binary w (s.left+s.accumulator)) (frame (binary w s.accumulator))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at hr
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run accSlots (by decide) _ _ _ hr
    (heads pos) ((added s w).tapes w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot accSlots (by decide) _ _ 0
    | exact install_slot accSlots (by decide) _ _ 1
    | exact install_slot accSlots (by decide) _ _ 2
    | exact install_slot accSlots (by decide) _ _ 3
    | exact install_other accSlots _ _ _ (by decide)

theorem double_run (s : Store) (w pos : ℕ) (source : List Bool)
    (hfit : s.left+s.duplicate<2^w) (hb : s.doubled.length≤2*w+1) :
    Run doubleProgram (4*w+4) w pos source s (doubled s w) := by
  have hr := HierarchyBinary.add_ready w s.left s.duplicate (4*w+3) s.doubled hfit hb
  simp only [max_eq_left (by omega : 2*w+1≤4*w+3)] at hr
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run doubleSlots (by decide) _ _ _ hr
    (heads pos) (s.tapes w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot doubleSlots (by decide) _ _ 0
    | exact install_slot doubleSlots (by decide) _ _ 1
    | exact install_slot doubleSlots (by decide) _ _ 2
    | exact install_slot doubleSlots (by decide) _ _ 3
    | exact install_other doubleSlots _ _ _ (by decide)

theorem left_run (s : Store) (w pos : ℕ) (source : List Bool) :
    Run leftProgram (8*w+8) w pos source (doubled s w) (shiftedLeft (doubled s w)) := by
  have hr := copy_ready (binary w (s.left+s.duplicate)) (frame (binary w s.left))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at hr
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run leftSlots (by decide) _ _ _ hr
    (heads pos) ((doubled s w).tapes w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot leftSlots (by decide) _ _ 0
    | exact install_slot leftSlots (by decide) _ _ 1
    | exact install_slot leftSlots (by decide) _ _ 2
    | exact install_slot leftSlots (by decide) _ _ 3
    | exact install_other leftSlots _ _ _ (by decide)

theorem duplicate_run (s : Store) (w pos : ℕ) (source : List Bool) :
    Run duplicateProgram (8*w+8) w pos source (shiftedLeft (doubled s w))
      (shiftedBoth (doubled s w)) := by
  have hr := copy_ready (binary w (s.left+s.duplicate)) (frame (binary w s.duplicate))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at hr
  obtain ⟨r,h,hh,ht,hs⟩ := HierarchyBinary.focused_run duplicateSlots (by decide) _ _ _ hr
    (heads pos) ((shiftedLeft (doubled s w)).tapes w source) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,h,hh,?_,hs⟩
  rw [ht]
  funext i; fin_cases i
  all_goals first
    | exact install_slot duplicateSlots (by decide) _ _ 0
    | exact install_slot duplicateSlots (by decide) _ _ 1
    | exact install_slot duplicateSlots (by decide) _ _ 2
    | exact install_slot duplicateSlots (by decide) _ _ 3
    | exact install_other duplicateSlots _ _ _ (by decide)

end NearCubicWires.RepairOrdinary.HierarchyMultiply
