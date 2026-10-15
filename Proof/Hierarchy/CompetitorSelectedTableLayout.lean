import Proof.Hierarchy.CompetitorSelectedCells

/-! Dock the request-derived selected-total program directly at the actual
natural count-table endpoint. The original Request, raw Q and completed
natural stream are reused at their existing physical tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedTable
open LocalBitMultitape RecoveryRootRound CompetitorCountMask
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := CompetitorCountTable.tapes p+92
def old (p : Program) (i : Fin (CompetitorCountTable.tapes p)) : Fin (tapes p) := i.castAdd 92
def fresh (p : Program) (i : Fin 92) : Fin (tapes p) := i.natAdd (CompetitorCountTable.tapes p)
def source (p : Program) : Fin (CompetitorCountTable.tapes p) :=
  CompetitorCountTable.old p (CompetitorCountBanks.field p 0)
def extra (xs : List (Bool × ℕ)) (i : Fin 92) : List Bool := if i=0 then mask xs else []
def extend (p : Program) (xs : List (Bool × ℕ)) (data : Fin (CompetitorCountTable.tapes p) → List Bool) :=
  Fin.addCases (m := CompetitorCountTable.tapes p) (n := 92) (motive := fun _ => List Bool) data (extra xs)
def heads (p : Program) (pos : ℕ) :=
  Fin.addCases (m := CompetitorCountTable.tapes p) (n := 92) (motive := fun _ => ℕ)
    (CompetitorCountTable.heads p pos) (fun _ => 0)
def slot (p : Program) (i : Fin 91) : Fin (tapes p) :=
  if i.val=0 then old p (source p)
  else if i.val=61 then old p (CompetitorCountTable.slot p 36)
  else if i.val=79 then old p (CompetitorCountTable.slot p 141)
  else if i.val=78 then fresh p 0 else fresh p ⟨i.val+1,by omega⟩

theorem slot_value (p : Program) (i : Fin 91) : (slot p i).val=
    if i.val=0 then 0 else if i.val=61 then CompetitorCountBanks.tapes p+1
    else if i.val=79 then CompetitorCountBanks.tapes p+106
    else if i.val=78 then CompetitorCountTable.tapes p else CompetitorCountTable.tapes p+(i.val+1) := by
  unfold slot
  split_ifs <;> rfl

theorem slot_injective (p : Program) : Function.Injective (slot p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [slot_value,slot_value] at hv
  have ht : 181≤CompetitorCrossScheduler.tapes p := by unfold CompetitorCrossScheduler.tapes;omega
  have hb : CompetitorCountBanks.tapes p=CompetitorCrossScheduler.tapes p+511 := rfl
  have hc : CompetitorCountTable.tapes p=CompetitorCountBanks.tapes p+124 := rfl
  split_ifs at hv <;> omega

theorem slot_heads (p : Program) (pos : ℕ) (i : Fin 91) : heads p pos (slot p i)=0 := by
  unfold slot
  split_ifs
  · rfl
  · simp only [heads,old,Fin.addCases_left,CompetitorCountTable.heads,CompetitorCountTable.slot_value]
    have hb : 181≤CompetitorCountBanks.tapes p := by
      unfold CompetitorCountBanks.tapes CompetitorCrossScheduler.tapes
      omega
    split_ifs <;> omega
  · simp only [heads,old,Fin.addCases_left,CompetitorCountTable.heads,CompetitorCountTable.slot_value]
    have hb : 181≤CompetitorCountBanks.tapes p := by
      unfold CompetitorCountBanks.tapes CompetitorCrossScheduler.tapes
      omega
    split_ifs <;> omega
  · simp only [heads,fresh,Fin.addCases_right]
  · simp only [heads,fresh,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CompetitorSelectedTable
