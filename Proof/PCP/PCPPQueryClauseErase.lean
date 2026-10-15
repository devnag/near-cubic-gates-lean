import Proof.PCP.PCPPQueryClauseReset
import Proof.PCP.PCPPRequestNodeErase

/-! Actual reusable scratch erasure for cached clause queries. The source,
two unary drivers and native selected pair survive with their real cursors. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots : Fin 13 → Fin 19 := ![1,2,3,4,5,6,7,8,9,10,11,12,16]
def eraseSlots : Fin 15 → Fin 19 :=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _ => Fin 19)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _ => Fin 19)
      scratchSlots (fun _ : Fin 1 => 17)) (fun _ : Fin 1 => 18)
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 13)
noncomputable def erased (C : ℕ) (ambient : Fin 19 → List Bool) :=
  install eraseSlots ambient (PCPTraversal.clearedLocal 13 C (C+1))

theorem erase_run (C : ℕ) (heads : Fin 19 → ℕ) (ambient : Fin 19 → List Bool)
    (hb : ∀ j,(ambient (scratchSlots j)).length ≤ C)
    (hd : ambient 17=List.replicate C true) (hl : ambient 18=List.replicate (C+1) false)
    (hh : ∀ j,heads (scratchSlots j)=0) (hhd : heads 17=0) (hhl : heads 18=0) :
    ∃ r,runFrom eraseMachine (2*C+4) ⟨eraseMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=erased C ambient ∧ r.steps=2*C+4 := by
  have h := RecoveryScratchErase.erase_ready C (C+1) (fun j => ambient (scratchSlots j)) hb
  apply h.focus_at eraseSlots erase_injective heads ambient
  · intro j
    refine Fin.addCases (m:=14) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=13) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
    · simpa only [eraseSlots,Fin.addCases_right] using hl
  · intro j
    refine Fin.addCases (m:=14) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=13) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simpa only [eraseSlots,Fin.addCases_left] using hh b
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hhd
    · simpa only [eraseSlots,Fin.addCases_right] using hhl

theorem erased_slot (C : ℕ) (ambient : Fin 19 → List Bool) (j : Fin 13) :
    erased C ambient (scratchSlots j)=List.replicate C false := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 13 C (C+1)) ((j.castAdd 1).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left] using h

theorem erased_driver (C : ℕ) (ambient : Fin 19 → List Bool) :
    erased C ambient 17=List.replicate C true := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 13 C (C+1)) (((0 : Fin 1).natAdd 13).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left,Fin.addCases_right] using h

theorem erased_log (C : ℕ) (ambient : Fin 19 → List Bool) :
    erased C ambient 18=List.replicate (C+1) false := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 13 C (C+1)) ((0 : Fin 1).natAdd 14)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_right,max_self] using h

theorem erased_live (C : ℕ) (ambient : Fin 19 → List Bool) (j : Fin 19)
    (hj : j=0 ∨ j=13 ∨ j=14 ∨ j=15) : erased C ambient j=ambient j := by
  apply install_other
  rcases hj with rfl|rfl|rfl|rfl
  all_goals intro i; fin_cases i <;> decide

end NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
