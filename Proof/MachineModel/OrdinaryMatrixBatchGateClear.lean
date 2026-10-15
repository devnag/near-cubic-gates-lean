import Proof.MachineModel.OrdinaryMatrixBatchRankedGate
import Proof.Amplification.RecoveryScratchErase

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots : Fin 30 → Fin 48 := ![0,2,3,4,5,7,8,9,10,11,12,13,14,20,21,24,26,29,30,31,32,33,34,35,36,37,38,39,40,47]
def eraseSlots : Fin 32 → Fin 48 := ![0,2,3,4,5,7,8,9,10,11,12,13,14,20,21,24,26,29,30,31,32,33,34,35,36,37,38,39,40,47,44,45]
theorem scratch_injective : Function.Injective scratchSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide
def scratchPick : Fin 48 → Option (Fin 30) :=
  ![some 0,none,some 1,some 2,some 3,some 4,none,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,
    none,none,none,none,none,some 13,some 14,none,none,some 15,none,some 16,none,none,some 17,some 18,some 19,
    some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,none,none,none,none,none,none,
    some 29]
def erasePick : Fin 48 → Option (Fin 32) :=
  ![some 0,none,some 1,some 2,some 3,some 4,none,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,
    none,none,none,none,none,some 13,some 14,none,none,some 15,none,some 16,none,none,some 17,some 18,some 19,
    some 20,some 21,some 22,some 23,some 24,some 25,some 26,some 27,some 28,none,none,none,some 30,some 31,
    none,some 29]
theorem pick_scratch (i : Fin 48) : RecoveryFocus.pick scratchSlots i=scratchPick i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 0
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 1
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 2
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 3
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 4
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 5
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 6
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 7
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 8
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 9
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 10
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 11
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 12
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 13
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 14
  · decide
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 15
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 16
  · decide
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 17
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 18
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 19
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 20
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 21
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 22
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 23
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 24
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 25
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 26
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 27
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 28
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot scratchSlots scratch_injective 29
theorem pick_erase (i : Fin 48) : RecoveryFocus.pick eraseSlots i=erasePick i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 4
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 5
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 6
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 7
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 8
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 9
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 10
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 11
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 12
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 13
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 14
  · decide
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 15
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 16
  · decide
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 17
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 18
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 19
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 20
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 21
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 22
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 23
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 24
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 25
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 26
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 27
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 28
  · decide
  · decide
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 30
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 31
  · decide
  · exact RecoveryFocus.pick_slot eraseSlots erase_injective 29

def stable (r : Request) (assignment id cap : ℕ) (source out : List Bool) : Fin 48 → List Bool :=
  ![[],frame (binary r.width assignment),[],[],[],[],List.replicate (r.S+1) true,
    [],[],[],[],[],[],[],[],List.replicate (C r) true,List.replicate (C r+1) false,UnaryTemplate.tape r.width,
    frame (binary (r.S+1) (2^r.S)),frame (binary (r.S+1) 0),[],[],frame (binary r.M id),
    frame (binary r.M r.U),[],List.replicate (C r) false,[],UnaryTemplate.tape r.U,frame (binary r.width 0),
    [],[],[],[],[],[],[],[],[],[],[],[],out,MatrixScorePhi.columnsWord r.width r.cols,frame (binary r.M 0),
    List.replicate (D r) true,List.replicate cap false,source,[]]
noncomputable def tapes (r : Request) (assignment id cap : ℕ) (source out : List Bool) (backing : Fin 30 → List Bool) :=
  install scratchSlots (stable r assignment id cap source out) backing
def heads (pos outlen : ℕ) (i : Fin 48) :=
  if i=17 ∨ i=27 then 1 else if i=41 then outlen else if i=46 then pos else 0
noncomputable def machine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 30)
noncomputable def input (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) :=
  RecoveryCalls.restarted machine (heads pos out.length) (tapes r assignment id cap source out backing)

theorem clear_run (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ actual,runFrom machine (2*D r+4) (input r assignment id cap pos source out backing)=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r assignment id (max cap (D r+1)) source out (fun _ => List.replicate (D r) false) ∧
      actual.steps≤2*D r+4 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready (D r) cap backing hb
  let before := tapes r assignment id cap source out backing
  let erased := Fin.addCases (m := 31) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 30) (n := 1) (motive := fun _ => List Bool)
      (fun _ => List.replicate (D r) false) (fun _ => List.replicate (D r) true))
    (fun _ => List.replicate (max cap (D r+1)) false)
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 30) (2*D r+4)
      (Fin.addCases (Fin.addCases backing (fun _ : Fin 1 => List.replicate (D r) true))
        (fun _ : Fin 1 => List.replicate cap false)) erased := ⟨base,hr,ht,hh,hs.le⟩
  obtain ⟨actual,ha,ah,atapes,asteps⟩ := CompetitorReusableDecision.bounded_focused_run eraseSlots erase_injective
    (RecoveryScratchErase.resetMachine 30) _ _ ready (heads pos out.length) before
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> simp [before,tapes,install,pick_scratch,scratchPick,stable,eraseSlots,Fin.addCases])
  refine ⟨actual,ha,ah,?_,asteps⟩
  rw [atapes]
  funext i
  fin_cases i <;> simp [before,tapes,install,pick_erase,erasePick,pick_scratch,scratchPick,stable,erased,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixBatchGateClear
