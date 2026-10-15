import Proof.MachineModel.UMemoryCloseBranch

/-! Apply the final branch to the actual output-only reset endpoint. A
successful emission supplies exactly the chronological checker's word;
failure writes false without invoking the checker. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def answerBudget (answer : Option MemoryChecker.Request) : ℕ := answer.elim 0 MemoryChecker.rawBudget
def answerValue (answer : Option MemoryChecker.Request) : Bool := answer.elim false MemoryChecker.Request.result

theorem reset_checker_heads {t s : ℕ} (event flag : Fin t) (c : Configuration t s) (steps : ℕ) :
    ∀ j, (resetEndpoint event flag c steps).heads (checkerSlots event j)=0 := by
  intro j
  cases j using Fin.cases with
  | zero => simp only [checkerSlots,Fin.cases_zero,reset_old_heads,↓reduceIte]
  | succ j => simp only [checkerSlots,Fin.cases_succ,reset_scratch_heads]

theorem reset_checker_tapes {t s : ℕ} (event flag : Fin t) (c : Configuration t s) (steps : ℕ)
    (req : MemoryChecker.Request) (hflag : c.scanned flag=true)
    (hstream : c.tapes event++[false]=req.input) (hpos : c.heads event=(c.tapes event).length) :
    ∀ j, (resetEndpoint event flag c steps).tapes (checkerSlots event j)=
      SourceHandoff.sourceTapes req.input j := by
  intro j
  cases j using Fin.cases with
  | zero =>
    rw [checkerSlots,Fin.cases_zero,reset_old_tapes,delimited_event event flag c hflag hpos,hstream]
    rfl
  | succ j =>
    simp only [checkerSlots,Fin.cases_succ,reset_scratch_tapes,SourceHandoff.sourceTapes,
      Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte]

theorem finish_run {t s : ℕ} (event flag : Fin t) (hne : event ≠ flag)
    (c : Configuration t s) (steps : ℕ) (answer : Option MemoryChecker.Request)
    (hflag : c.scanned flag=answer.isSome)
    (hstream : ∀ req, answer=some req → c.tapes event++[false]=req.input ∧
      c.heads event=(c.tapes event).length) :
    ∃ r,runFrom (finishMachine event flag) (answerBudget answer+3)
      (Composition.restart (resetEndpoint event flag c steps) (finishMachine event flag).start)=some r ∧
      r.final.tapes (resultSlot t)=[answerValue answer] ∧ r.final.heads (resultSlot t)=0 ∧
      (∀ i : Fin t, i ≠ event → r.final.heads (oldSlot i)=c.heads i ∧ r.final.tapes (oldSlot i)=c.tapes i) := by
  have hs : (resetEndpoint event flag c steps).scanned (oldSlot flag)=answer.isSome :=
    (reset_flag event flag c steps hne).trans hflag
  cases answer with
  | none =>
    obtain ⟨r,hr,hrt,hrh,hother⟩ := finish_failure event flag (resetEndpoint event flag c steps) hs
      (reset_scratch_tapes event flag 18 c steps) (reset_scratch_heads event flag 18 c steps)
    refine ⟨r,hr,hrt,hrh,?_⟩
    intro i hi
    obtain ⟨hh,ht⟩ := hother i
    rw [reset_old_heads,if_neg hi] at hh
    rw [reset_old_tapes,delimited_other event flag i c hi] at ht
    exact ⟨hh,ht⟩
  | some req =>
    obtain ⟨hword,hpos⟩ := hstream req rfl
    obtain ⟨r,hr,hrt,hrh,hother⟩ := finish_success event flag req (resetEndpoint event flag c steps)
      hs (reset_checker_heads event flag c steps)
      (reset_checker_tapes event flag c steps req hflag hword hpos)
    have hmore := runFrom_moreFuel (finishMachine event flag) (MemoryChecker.rawBudget req+2) 1 _ r hr
    refine ⟨r,hmore,hrt,hrh,?_⟩
    intro i hi
    obtain ⟨hh,ht⟩ := hother i hi
    rw [reset_old_heads,if_neg hi] at hh
    rw [reset_old_tapes,delimited_other event flag i c hi] at ht
    exact ⟨hh,ht⟩

end NearCubicWires.RepairOrdinary.UMemoryClose
