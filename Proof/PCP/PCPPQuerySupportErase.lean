import Proof.PCP.PCPPQuerySupportReset
import Proof.PCP.PCPPRequestNodeErase

/-! Actual reusable scratch erasure for cached support queries. The source,
two unary drivers and raw selected mask survive with their real cursors. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots : Fin 3 → Fin 9 := ![1,2,6]
def eraseSlots : Fin 5 → Fin 9 :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _ => Fin 9)
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _ => Fin 9)
      scratchSlots (fun _ : Fin 1 => 7)) (fun _ : Fin 1 => 8)
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def erased (C : ℕ) (ambient : Fin 9 → List Bool) :=
  install eraseSlots ambient (PCPTraversal.clearedLocal 3 C (C+1))

theorem erase_run (C : ℕ) (heads : Fin 9 → ℕ) (ambient : Fin 9 → List Bool)
    (hb : ∀ j,(ambient (scratchSlots j)).length ≤ C)
    (hd : ambient 7=List.replicate C true) (hl : ambient 8=List.replicate (C+1) false)
    (hh : ∀ j,heads (scratchSlots j)=0) (hhd : heads 7=0) (hhl : heads 8=0) :
    ∃ r,runFrom eraseMachine (2*C+4) ⟨eraseMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=erased C ambient ∧ r.steps=2*C+4 := by
  have h := RecoveryScratchErase.erase_ready C (C+1) (fun j => ambient (scratchSlots j)) hb
  apply h.focus_at eraseSlots erase_injective heads ambient
  · intro j
    refine Fin.addCases (m:=4) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=3) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simp only [eraseSlots,Fin.addCases_left]
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
    · simpa only [eraseSlots,Fin.addCases_right] using hl
  · intro j
    refine Fin.addCases (m:=4) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=3) (n:=1) (fun b => ?_) (fun b => ?_) a
      · simpa only [eraseSlots,Fin.addCases_left] using hh b
      · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hhd
    · simpa only [eraseSlots,Fin.addCases_right] using hhl

theorem erased_slot (C : ℕ) (ambient : Fin 9 → List Bool) (j : Fin 3) :
    erased C ambient (scratchSlots j)=List.replicate C false := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 3 C (C+1)) ((j.castAdd 1).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left] using h

theorem erased_driver (C : ℕ) (ambient : Fin 9 → List Bool) :
    erased C ambient 7=List.replicate C true := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 3 C (C+1)) (((0 : Fin 1).natAdd 3).castAdd 1)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_left,Fin.addCases_right] using h

theorem erased_log (C : ℕ) (ambient : Fin 9 → List Bool) :
    erased C ambient 8=List.replicate (C+1) false := by
  have h := install_slot eraseSlots erase_injective ambient
    (PCPTraversal.clearedLocal 3 C (C+1)) ((0 : Fin 1).natAdd 4)
  simpa only [erased,eraseSlots,PCPTraversal.clearedLocal,Fin.addCases_right,max_self] using h

theorem erased_live (C : ℕ) (ambient : Fin 9 → List Bool) (j : Fin 9)
    (hj : j=0 ∨ j=3 ∨ j=4 ∨ j=5) : erased C ambient j=ambient j := by
  apply install_other
  rcases hj with rfl|rfl|rfl|rfl
  all_goals intro i; fin_cases i <;> decide

end NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
