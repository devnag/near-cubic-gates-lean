import Proof.MachineModel.OrdinaryMatrixBucketRootPower

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootClear
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots : Fin 23 → Fin 27 := ![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,23,24]
def eraseSlots : Fin 25 → Fin 27 := ![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,23,24,25,26]
theorem scratch_injective : Function.Injective scratchSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide
def erasePick : Fin 27 → Option (Fin 25) := ![none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,some 14,some 15,some 16,some 17,some 18,some 19,some 20,none,some 21,some 22,some 23,some 24]
theorem pick_erase (i : Fin 27) : RecoveryFocus.pick eraseSlots i=erasePick i := by
  fin_cases i
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 4
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 5
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 6
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 7
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 8
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 9
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 10
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 11
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 12
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 13
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 14
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 15
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 16
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 17
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 18
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 19
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 20
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 21
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 22
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 23
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 24
def tapes (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) : Fin 27 → List Bool :=
  ![UnaryTemplate.tape c,work 0,work 1,work 2,work 3,work 4,work 5,work 6,work 7,work 8,work 9,work 10,work 11,work 12,work 13,work 14,work 15,work 16,work 17,work 18,work 19,work 20,UnaryTemplate.tape r.U,work 21,work 22,List.replicate (D r) true,List.replicate cap false]
noncomputable def machine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 23)
noncomputable def input (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool) :=
  RecoveryCalls.restarted machine (fun _ => 0) (tapes r c cap work)

theorem clear_run (r : Request) (c cap : ℕ) (work : Fin 23 → List Bool)
    (hb : ∀ i,(work i).length≤D r) :
    ∃ actual,runFrom machine (2*D r+4) (input r c cap work)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧
      actual.final.tapes=tapes r c (max cap (D r+1)) (fun _ => List.replicate (D r) false) ∧
      actual.steps≤2*D r+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready (D r) cap work hb
  let erased := Fin.addCases (m := 24) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 23) (n := 1) (motive := fun _ => List Bool)
      (fun _ => List.replicate (D r) false) (fun _ => List.replicate (D r) true))
    (fun _ => List.replicate (max cap (D r+1)) false)
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 23) (2*D r+4)
      (Fin.addCases (Fin.addCases work (fun _ : Fin 1 => List.replicate (D r) true))
        (fun _ : Fin 1 => List.replicate cap false)) erased := ⟨base,hr,ht,hh,hs.le⟩
  obtain ⟨actual,ha,ah,atapes,asteps⟩ := CompetitorReusableDecision.bounded_focused_run eraseSlots erase_injective
    (RecoveryScratchErase.resetMachine 23) _ _ ready (fun _ => 0) (tapes r c cap work)
    (by intro i; rfl)
    (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,ha,ah,?_,asteps⟩
  rw [atapes]
  funext i
  fin_cases i <;> simp [tapes,install,pick_erase,erasePick,erased,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixBucketRootClear

