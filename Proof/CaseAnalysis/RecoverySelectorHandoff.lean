import Proof.CaseAnalysis.RecoverySelectorReuseBank

/-! Paid first-to-second selector scalar handoff. Save the actual first
output, advance the graph count, clear the old value/index, and install the
next shared field index twice using the existing copy and erase machines. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorHandoff
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def saveSlots : Fin 3→Fin 9:=![0,1,6]
def advanceSlots : Fin 2→Fin 9:=![0,6]
def clearSlots : Fin 5→Fin 9:=![3,4,5,7,8]
def firstSlots : Fin 3→Fin 9:=![2,3,6]
def lastSlots : Fin 3→Fin 9:=![2,4,6]
noncomputable def save:=RecoveryFocus.machine saveSlots PCPUnaryCopy.machine
noncomputable def advance:=RecoveryFocus.machine advanceSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def first:=RecoveryFocus.machine firstSlots PCPUnaryCopy.machine
noncomputable def last:=RecoveryFocus.machine lastSlots PCPUnaryCopy.machine
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine save advance) clear) first) last

def data (acc index next value C : ℕ) (stage : Fin 6) : Fin 9→List Bool :=
  ![List.replicate (acc+if 2 ≤ stage.val then 1 else 0) true,
    if 1 ≤ stage.val then ZeroPadding.pad C (List.replicate acc true) else List.replicate C false,
    List.replicate next true,
    if 4 ≤ stage.val then ZeroPadding.pad C (List.replicate next true)
      else if 3 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate index true),
    if 5 ≤ stage.val then ZeroPadding.pad C (List.replicate next true)
      else if 3 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate index true),
    if 3 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate value true),
    List.replicate C false,List.replicate C true,List.replicate (C+1) false]

theorem save_ready (acc index next value C : ℕ) (hC : acc+1 ≤ C) :
    ReadyRun save (2*acc+4) (data acc index next value C 0) (data acc index next value C 1) := by
  have h:=PCPUnaryCopy.copy_ready acc 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus saveSlots (by decide) (data acc index next value C 0)
    (by intro j; fin_cases j <;> rfl)
  have he : install saveSlots (data acc index next value C 0)
      ![List.replicate acc true,ZeroPadding.pad C (List.replicate acc true),List.replicate C false]=
      data acc index next value C 1 := by
    apply HierarchyWidth.install_eq saveSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at run
  exact run

theorem advance_ready (acc index next value C : ℕ) (hC : acc+1 ≤ C) :
    ReadyRun advance (2*acc+4) (data acc index next value C 1) (data acc index next value C 2) := by
  have h:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready acc C hC).focus advanceSlots
    (by decide) (data acc index next value C 1) (by intro j; fin_cases j <;> rfl)
  have he : install advanceSlots (data acc index next value C 1)
      ![List.replicate (acc+1) true,List.replicate C false]=data acc index next value C 2 := by
    apply HierarchyWidth.install_eq advanceSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at h
  exact h

theorem clear_ready (acc index next value C : ℕ) (hi : index ≤ C) (hv : value ≤ C) :
    ReadyRun clear (2*C+4) (data acc index next value C 2) (data acc index next value C 3) := by
  let backing : Fin 3→List Bool:=![ZeroPadding.pad C (List.replicate index true),
    ZeroPadding.pad C (List.replicate index true),ZeroPadding.pad C (List.replicate value true)]
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    fin_cases j
    all_goals change (ZeroPadding.pad C (List.replicate _ true)).length ≤ C
    all_goals rw [ZeroPadding.pad_length,List.length_replicate]; omega
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus clearSlots (by decide)
    (data acc index next value C 2) (by intro j; fin_cases j <;> rfl)
  have he : install clearSlots (data acc index next value C 2)
      (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data acc index next value C 3 := by
    apply HierarchyWidth.install_eq clearSlots (by decide)
    · intro j; fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hkeep
      fin_cases i
      all_goals first | rfl | exact False.elim (hkeep 0 rfl) |
        exact False.elim (hkeep 1 rfl) | exact False.elim (hkeep 2 rfl)
  rw [he] at h
  exact h

theorem first_ready (acc index next value C : ℕ) (hC : next+1 ≤ C) :
    ReadyRun first (2*next+4) (data acc index next value C 3) (data acc index next value C 4) := by
  have h:=PCPUnaryCopy.copy_ready next 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus firstSlots (by decide) (data acc index next value C 3)
    (by intro j; fin_cases j <;> rfl)
  have he : install firstSlots (data acc index next value C 3)
      ![List.replicate next true,ZeroPadding.pad C (List.replicate next true),List.replicate C false]=
      data acc index next value C 4 := by
    apply HierarchyWidth.install_eq firstSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at run
  exact run

theorem last_ready (acc index next value C : ℕ) (hC : next+1 ≤ C) :
    ReadyRun last (2*next+4) (data acc index next value C 4) (data acc index next value C 5) := by
  have h:=PCPUnaryCopy.copy_ready next 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus lastSlots (by decide) (data acc index next value C 4)
    (by intro j; fin_cases j <;> rfl)
  have he : install lastSlots (data acc index next value C 4)
      ![List.replicate next true,ZeroPadding.pad C (List.replicate next true),List.replicate C false]=
      data acc index next value C 5 := by
    apply HierarchyWidth.install_eq lastSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at run
  exact run

theorem handoff_ready (acc index next value C : ℕ)
    (ha : acc+1 ≤ C) (hi : index ≤ C) (hn : next+1 ≤ C) (hv : value ≤ C) :
    ReadyRun machine (2*C+4*acc+4*next+24) (data acc index next value C 0) (data acc index next value C 5) := by
  have h1:=HierarchyMultiplyEntry.join_exact save advance _ _ _ _ _
    (save_ready acc index next value C ha) (advance_ready acc index next value C ha)
  have h2:=HierarchyMultiplyEntry.join_exact (Composition.machine save advance) clear _ _ _ _ _ h1
    (clear_ready acc index next value C hi hv)
  have h3:=HierarchyMultiplyEntry.join_exact (Composition.machine (Composition.machine save advance) clear) first _ _ _ _ _ h2
    (first_ready acc index next value C hn)
  have h4:=HierarchyMultiplyEntry.join_exact (Composition.machine (Composition.machine (Composition.machine save advance) clear) first)
    last _ _ _ _ _ h3 (last_ready acc index next value C hn)
  have he : (((2*acc+4)+1+(2*acc+4))+1+(2*C+4))+1+(2*next+4)+1+(2*next+4)=2*C+4*acc+4*next+24 := by omega
  simpa only [machine,he] using h4

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorHandoff
