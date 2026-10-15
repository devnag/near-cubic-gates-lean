import Proof.Hierarchy.CompetitorCountBanksBounds
import Proof.Hierarchy.CompetitorFinalTableNative
import Proof.Hierarchy.CompetitorRowCountMeaning

/-! Reuse the accepted final159 machine beside the actual both-bank program.
Q and parity are explicit retained row metadata; original Request does not
encode them. The only head adjustment moves the produced U driver once. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := CompetitorCountBanks.tapes p+124
def old (p : Program) (i : Fin (CompetitorCountBanks.tapes p)) : Fin (tapes p) := i.castAdd 124
def fresh (p : Program) (i : Fin 124) : Fin (tapes p) := i.natAdd (CompetitorCountBanks.tapes p)
def metadata (q : ℕ) (odd : Bool) (i : Fin 124) : List Bool :=
  if i=1 then List.replicate q true else if i=3 then [odd] else []
def extend (p : Program) (q : ℕ) (odd : Bool) (ambient : Fin (CompetitorCountBanks.tapes p) → List Bool) :=
  Fin.addCases (m := CompetitorCountBanks.tapes p) (n := 124) (motive := fun _ => List Bool)
    ambient (metadata q odd)
def input (p : Program) (r : MatrixScoreBatch.Request) (q : ℕ) (odd : Bool) :=
  extend p q odd (CompetitorCountBanks.input p r)
def slot (p : Program) (i : Fin 159) : Fin (tapes p) :=
  if h : i.val<35 then old p (CompetitorCountBanks.tableNative p ⟨i.val,h⟩)
  else if i.val=35 then old p (CompetitorCountBanks.bank p)
  else if i.val=37 then old p (CompetitorCountBanks.field p 44)
  else fresh p ⟨i.val-35,by omega⟩
def heads (p : Program) (pos : ℕ) (i : Fin (tapes p)) :=
  if i.val=93 then pos else if i.val=44 then 1 else 0

theorem old_injective (p : Program) : Function.Injective (old p) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes p) => k.val) h)
theorem extend_old (p : Program) (q : ℕ) (odd : Bool) (a : Fin (CompetitorCountBanks.tapes p) → List Bool)
    (i : Fin (CompetitorCountBanks.tapes p)) : extend p q odd a (old p i)=a i := by
  simp only [extend,old,Fin.addCases_left]
theorem extend_fresh (p : Program) (q : ℕ) (odd : Bool) (a : Fin (CompetitorCountBanks.tapes p) → List Bool)
    (i : Fin 124) : extend p q odd a (fresh p i)=metadata q odd i := by
  simp only [extend,fresh,Fin.addCases_right]

theorem native_value (p : Program) (i : Fin 35) :
    (CompetitorCountBanks.tableNative p i).val=if i.val=9 then 52 else if i.val=20 then 48 else 61+i.val := by
  fin_cases i <;> rfl
theorem slot_value (p : Program) (i : Fin 159) : (slot p i).val=
    if i.val<35 then (if i.val=9 then 52 else if i.val=20 then 48 else 61+i.val)
    else if i.val=35 then CompetitorCrossScheduler.tapes p+2
    else if i.val=37 then 44 else CompetitorCountBanks.tapes p+(i.val-35) := by
  by_cases h : i.val<35
  · simpa only [slot,h,↓reduceDIte,↓reduceIte,old,Fin.val_castAdd] using native_value p ⟨i.val,h⟩
  · simp only [slot,h,↓reduceDIte,↓reduceIte]
    split_ifs <;> rfl

theorem slot_injective (p : Program) : Function.Injective (slot p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have ht : 181 ≤ CompetitorCrossScheduler.tapes p := by unfold CompetitorCrossScheduler.tapes;omega
  have hc : CompetitorCountBanks.tapes p=CompetitorCrossScheduler.tapes p+511 := rfl
  rw [slot_value,slot_value] at hv
  split_ifs at hv <;> omega

theorem slot_native (p : Program) (i : Fin 35) :
    slot p (i.castAdd 124)=old p (CompetitorCountBanks.tableNative p i) := by
  simp only [slot,Fin.val_castAdd,i.isLt,↓reduceDIte]
theorem slot_heads (p : Program) (pos : ℕ) (i : Fin 159) :
    heads p pos (slot p i)=CompetitorFinalTable.heads pos i := by
  unfold heads
  rw [slot_value]
  have ht : 181 ≤ CompetitorCrossScheduler.tapes p := by unfold CompetitorCrossScheduler.tapes;omega
  have hc : CompetitorCountBanks.tapes p=CompetitorCrossScheduler.tapes p+511 := rfl
  unfold CompetitorFinalTable.heads
  have h32 : i=32 ↔ i.val=32 := Fin.ext_iff
  have h37 : i=37 ↔ i.val=37 := Fin.ext_iff
  simp only [h32,h37]
  split_ifs <;> omega

theorem slot_avoids_zero (p : Program) (i : Fin 159) :
    slot p i≠old p (CompetitorCountBanks.field p 0) := by
  intro h
  have hv := congrArg Fin.val h
  change (slot p i).val=0 at hv
  rw [slot_value] at hv
  have ht : 181 ≤ CompetitorCrossScheduler.tapes p := by unfold CompetitorCrossScheduler.tapes;omega
  have hc : CompetitorCountBanks.tapes p=CompetitorCrossScheduler.tapes p+511 := rfl
  split_ifs at hv <;> omega

def moveMachine {t : ℕ} (target : Fin t) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun _ => none,
    fun i => if i=target then .right else .stay⟩ else none

theorem move_run {t : ℕ} (target : Fin t) (h : Fin t → ℕ) (a : Fin t → List Bool) :
    ∃ r,runFrom (moveMachine target) 1 ⟨0,h,a⟩=some r ∧
      r.final.heads=(fun i => if i=target then h i+1 else h i) ∧
      r.final.tapes=a ∧ r.steps=1 := by
  have hs : step (moveMachine target) ⟨0,h,a⟩=
      some ⟨1,(fun i => if i=target then h i+1 else h i),a⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=target <;> simp [applyAction,hi,HeadMove.apply]
    · rfl
  obtain ⟨r,hr,hf,hsteps⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hsteps⟩

end NearCubicWires.RepairOrdinary.CompetitorCountTable
