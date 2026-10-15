import Proof.Amplification.RecoverySourceClauseBudget

/-! Concrete seven-tape source reader ports and data transitions. Abstract
head/tape functions keep actual control terms outside layout proofs. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseRead
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (k : Fin 3) : Fin 3→Fin 7 := ![0,⟨k.val+1,by have h:=k.isLt; omega⟩,⟨k.val+4,by have h:=k.isLt; omega⟩]
theorem slots_injective (k : Fin 3) : Function.Injective (slots k) := by fin_cases k <;> decide
noncomputable def phase (k : Fin 3) := RecoveryFocus.machine (slots k) PCPFieldMoves.advanceMachine
noncomputable def machine := Composition.machine (Composition.machine (phase 0) (phase 1)) (phase 2)
def prefixes (bits : Fin 3→List Bool) : Fin 4→List Bool :=
  ![[],RepairOrdinary.frame (bits 0),RepairOrdinary.frame (bits 0)++RepairOrdinary.frame (bits 1),
    RepairOrdinary.frame (bits 0)++RepairOrdinary.frame (bits 1)++RepairOrdinary.frame (bits 2)]
def suffixes (bits : Fin 3→List Bool) (suffix : List Bool) : Fin 3→List Bool :=
  ![RepairOrdinary.frame (bits 1)++RepairOrdinary.frame (bits 2)++suffix,RepairOrdinary.frame (bits 2)++suffix,suffix]
def source (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) :=
  pre++RepairOrdinary.frame (bits 0)++RepairOrdinary.frame (bits 1)++RepairOrdinary.frame (bits 2)++suffix

def data (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (done : Fin 4) : Fin 7→List Bool :=
  ![source pre bits suffix,
    if 1≤done.val then RepairOrdinary.frame (bits 0) else [],
    if 2≤done.val then RepairOrdinary.frame (bits 1) else [],
    if 3≤done.val then RepairOrdinary.frame (bits 2) else [],
    if 1≤done.val then List.replicate (2*(bits 0).length+1) false else [],
    if 2≤done.val then List.replicate (2*(bits 1).length+1) false else [],
    if 3≤done.val then List.replicate (2*(bits 2).length+1) false else []]
def cfg {s : Nat} (q : Fin s) (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (done : Fin 4) : Configuration 7 s :=
  ⟨q,![(pre++prefixes bits done).length,0,0,0,0,0,0],data pre bits suffix done⟩

theorem source_split (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (k : Fin 3) :
    source pre bits suffix=(pre++prefixes bits k.castSucc)++RepairOrdinary.frame (bits k)++suffixes bits suffix k := by
  fin_cases k <;> simp [source,prefixes,suffixes,List.append_assoc]

theorem heads_done (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (k : Fin 3)
    (heads : Fin 7→Nat)
    (h0 : heads (slots k 0)=(pre++prefixes bits k.castSucc).length+2*(bits k).length+1)
    (h1 : heads (slots k 1)=0) (h2 : heads (slots k 2)=0)
    (ho : ∀ i,(∀ j,slots k j≠i) → heads i=(cfg (0 : Fin 1) pre bits suffix k.castSucc).heads i) :
    heads=(cfg (0 : Fin 1) pre bits suffix k.succ).heads := by
  funext i
  by_cases hi0 : i=slots k 0
  · subst i; rw [h0]
    fin_cases k <;> simp [cfg,slots,prefixes,frame_length,List.length_append,Nat.add_assoc]
  by_cases hi1 : i=slots k 1
  · subst i; rw [h1]; fin_cases k <;> rfl
  by_cases hi2 : i=slots k 2
  · subst i; rw [h2]; fin_cases k <;> rfl
  rw [ho i (by intro j; fin_cases j; exact Ne.symm hi0; exact Ne.symm hi1; exact Ne.symm hi2)]
  fin_cases k <;> fin_cases i <;> first | rfl | exact (hi0 rfl).elim

theorem data_other (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (k : Fin 3)
    (i : Fin 7) (hi : ∀ j,slots k j≠i) :
    data pre bits suffix k.castSucc i=data pre bits suffix k.succ i := by
  fin_cases i
  · rfl
  · have hn : k.val≠0 := by
      intro hk
      apply hi 1
      apply Fin.ext
      change k.val+1=1
      omega
    change (if 1≤k.val then RepairOrdinary.frame (bits 0) else [])=(if 1≤k.val+1 then RepairOrdinary.frame (bits 0) else [])
    have he : (1≤k.val)=(1≤k.val+1) := propext (by omega)
    simp only [he]
  · have hn : k.val≠1 := by
      intro hk
      apply hi 1
      apply Fin.ext
      change k.val+1=2
      omega
    change (if 2≤k.val then RepairOrdinary.frame (bits 1) else [])=(if 2≤k.val+1 then RepairOrdinary.frame (bits 1) else [])
    have he : (2≤k.val)=(2≤k.val+1) := propext (by omega)
    simp only [he]
  · have hn : k.val≠2 := by
      intro hk
      apply hi 1
      apply Fin.ext
      change k.val+1=3
      omega
    change (if 3≤k.val then RepairOrdinary.frame (bits 2) else [])=(if 3≤k.val+1 then RepairOrdinary.frame (bits 2) else [])
    have he : (3≤k.val)=(3≤k.val+1) := propext (by omega)
    simp only [he]
  · have hn : k.val≠0 := by
      intro hk
      apply hi 2
      apply Fin.ext
      change k.val+4=4
      omega
    change (if 1≤k.val then List.replicate (2*(bits 0).length+1) false else [])=(if 1≤k.val+1 then List.replicate (2*(bits 0).length+1) false else [])
    have he : (1≤k.val)=(1≤k.val+1) := propext (by omega)
    simp only [he]
  · have hn : k.val≠1 := by
      intro hk
      apply hi 2
      apply Fin.ext
      change k.val+4=5
      omega
    change (if 2≤k.val then List.replicate (2*(bits 1).length+1) false else [])=(if 2≤k.val+1 then List.replicate (2*(bits 1).length+1) false else [])
    have he : (2≤k.val)=(2≤k.val+1) := propext (by omega)
    simp only [he]
  · have hn : k.val≠2 := by
      intro hk
      apply hi 2
      apply Fin.ext
      change k.val+4=6
      omega
    change (if 3≤k.val then List.replicate (2*(bits 2).length+1) false else [])=(if 3≤k.val+1 then List.replicate (2*(bits 2).length+1) false else [])
    have he : (3≤k.val)=(3≤k.val+1) := propext (by omega)
    simp only [he]

theorem tapes_done (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (k : Fin 3)
    (tapes : Fin 7→List Bool)
    (h0 : tapes (slots k 0)=source pre bits suffix)
    (h1 : tapes (slots k 1)=RepairOrdinary.frame (bits k))
    (h2 : tapes (slots k 2)=List.replicate (2*(bits k).length+1) false)
    (ho : ∀ i,(∀ j,slots k j≠i) → tapes i=data pre bits suffix k.castSucc i) :
    tapes=data pre bits suffix k.succ := by
  funext i
  by_cases hi0 : i=slots k 0
  · subst i; rw [h0]; rfl
  by_cases hi1 : i=slots k 1
  · subst i; rw [h1]; fin_cases k <;> rfl
  by_cases hi2 : i=slots k 2
  · subst i; rw [h2]; fin_cases k <;> rfl
  rw [ho i (by intro j; fin_cases j; exact Ne.symm hi0; exact Ne.symm hi1; exact Ne.symm hi2)]
  exact data_other pre bits suffix k i (by intro j; fin_cases j; exact Ne.symm hi0; exact Ne.symm hi1; exact Ne.symm hi2)

end NearCubicWires.RepairSource.RecoverySourceClauseRead
