import Proof.Amplification.RecoverySourceClauseReadWhole

/-! The actual three-field reader feeds the exact original-clause machine
in place, retaining its source stream and projected-address stream. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots : Fin 7→Fin 276 := ![272,0,53,106,273,274,275]
def nativeSlots (i : Fin 272) : Fin 276 := i.castAdd 4
theorem read_injective : Function.Injective readSlots := by decide
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 276=>i.val) h)
noncomputable def readMachine := RecoveryFocus.machine readSlots RecoverySourceClauseRead.machine
noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots RecoverySourceClauseCode.machine
noncomputable def machine := Composition.machine readMachine nativeMachine

def input (pre : List Bool) (codes : Fin 3→List Bool) (suffix address : List Bool) (i : Fin 276) :=
  if i.val=159 then address else if i.val=272 then RecoverySourceClauseRead.source pre codes suffix else []
def heads (pre : List Bool) (i : Fin 276) := if i.val=272 then pre.length else 0

theorem entry_heads (pre : List Bool) (codes : Fin 3→List Bool) (suffix : List Bool) (i : Fin 7) :
    heads pre (readSlots i)=(RecoverySourceClauseRead.cfg (0 : Fin 1) pre codes suffix 0).heads i := by
  fin_cases i
  · change pre.length=(pre++[]).length
    simp only [List.append_nil]
  all_goals rfl

theorem entry_tapes (pre : List Bool) (codes : Fin 3→List Bool) (suffix address : List Bool) (i : Fin 7) :
    input pre codes suffix address (readSlots i)=RecoverySourceClauseRead.data pre codes suffix 0 i := by
  fin_cases i <;> rfl

theorem outside (i : Fin 272) (h0 : i.val≠0) (h53 : i.val≠53) (h106 : i.val≠106) :
    ∀ j,readSlots j≠nativeSlots i := by
  intro j he
  have hv:=congrArg Fin.val he; have hi:=i.isLt
  fin_cases j <;> dsimp [readSlots,nativeSlots] at hv <;> omega

theorem native_heads (pre : List Bool) (codes : Fin 3→List Bool) (suffix : List Bool)
    (h : Fin 276→Nat)
    (readHeads : ∀ j,h (readSlots j)=(RecoverySourceClauseRead.cfg (0 : Fin 1) pre codes suffix 3).heads j)
    (unchanged : ∀ i,(∀ j,readSlots j≠i) → h i=heads pre i) :
    ∀ i,h (nativeSlots i)=0 := by
  intro i
  by_cases h0 : i.val=0
  · have he : i=0 := Fin.ext h0
    subst i
    change h (readSlots 1)=0
    exact readHeads 1
  by_cases h53 : i.val=53
  · have he : i=53 := Fin.ext h53
    subst i
    change h (readSlots 2)=0
    exact readHeads 2
  by_cases h106 : i.val=106
  · have he : i=106 := Fin.ext h106
    subst i
    change h (readSlots 3)=0
    exact readHeads 3
  rw [unchanged _ (outside i h0 h53 h106)]
  have hi : (nativeSlots i).val≠272 := by change i.val≠272; exact Nat.ne_of_lt i.isLt
  simp only [heads,hi,ite_false]

theorem native_tapes (pre : List Bool) (codes : Fin 3→List Bool) (suffix address : List Bool)
    (t : Fin 276→List Bool)
    (readTapes : ∀ j,t (readSlots j)=RecoverySourceClauseRead.data pre codes suffix 3 j)
    (unchanged : ∀ i,(∀ j,readSlots j≠i) → t i=input pre codes suffix address i) :
    ∀ i,t (nativeSlots i)=RecoverySourceClauseCode.input codes address i := by
  intro i
  by_cases h0 : i.val=0
  · have he : i=0 := Fin.ext h0
    subst i
    change t (readSlots 1)=RepairOrdinary.frame (codes 0)
    exact readTapes 1
  by_cases h53 : i.val=53
  · have he : i=53 := Fin.ext h53
    subst i
    change t (readSlots 2)=RepairOrdinary.frame (codes 1)
    exact readTapes 2
  by_cases h106 : i.val=106
  · have he : i=106 := Fin.ext h106
    subst i
    change t (readSlots 3)=RepairOrdinary.frame (codes 2)
    exact readTapes 3
  rw [unchanged _ (outside i h0 h53 h106)]
  by_cases h159 : i.val=159
  · have he : i=159 := Fin.ext h159
    subst i; rfl
  have h272 : (nativeSlots i).val≠272 := by change i.val≠272; exact Nat.ne_of_lt i.isLt
  have hn159 : (nativeSlots i).val≠159 := h159
  simp only [input,hn159,h272,ite_false,RecoverySourceClauseCode.input]
  split
  · simp only [RecoverySourceClauseLiterals.input,h159,h0,h53,h106,ite_false]
  · rfl

end NearCubicWires.RepairSource.RecoverySourceClauseLoad
