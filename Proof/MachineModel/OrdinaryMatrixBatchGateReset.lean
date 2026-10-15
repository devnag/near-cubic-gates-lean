import Proof.MachineModel.OrdinaryMatrixBatchGateClear
import Proof.MachineModel.OrdinaryMatrixBatchAssignmentZero

namespace NearCubicWires.RepairOrdinary.MatrixBatchGateReset
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The assignment tape and the weight-count sentinel. -/
def zeroSlots : Fin 2 → Fin 48 := ![1,17]
theorem zero_injective : Function.Injective zeroSlots := by decide
def zeroPicked : Fin 48 → Option (Fin 2) :=
  ![none,some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,none,none,
    none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
    none,none,none,none,none,none,none]
theorem pick_zero (i : Fin 48) : RecoveryFocus.pick zeroSlots i=zeroPicked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot zeroSlots zero_injective 0
    | exact RecoveryFocus.pick_slot zeroSlots zero_injective 1
noncomputable def zero := RecoveryFocus.machine zeroSlots MatrixBatchAssignmentZero.machine

/-- The id reset: the retained M-zero word (tape 43) over the id (tape 22). -/
def slots : Fin 4 → Fin 48 := ![43,22,25,16]
theorem slots_injective : Function.Injective slots := by decide
def picked : Fin 48 → Option (Fin 4) :=
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 3,none,none,none,
    none,none,some 1,none,none,some 2,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
    none,none,none,some 0,none,none,none,none]
theorem pick_slots (i : Fin 48) : RecoveryFocus.pick slots i=picked i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot slots slots_injective 0
    | exact RecoveryFocus.pick_slot slots slots_injective 1
    | exact RecoveryFocus.pick_slot slots slots_injective 2
    | exact RecoveryFocus.pick_slot slots slots_injective 3
noncomputable def copy := RecoveryFocus.machine slots copyMachine
def copyOutput (r : Request) : Fin 4 → List Bool :=
  ![frame (binary r.M 0),frame (binary r.M 0),List.replicate (C r) false,List.replicate (C r+1) false]

theorem zero_run (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) :
    ∃ actual,runFrom zero (4*r.width+2)
      (RecoveryCalls.restarted zero (heads pos out.length) (tapes r assignment id cap source out backing))=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r 0 id cap source out backing ∧
      actual.steps≤4*r.width+2 := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixBatchAssignmentZero.assignment_run r.width assignment
  let entry := RecoveryCalls.restarted zero (heads pos out.length) (tapes r assignment id cap source out backing)
  have hi : RecoveryFocus.config zeroSlots entry.heads entry.tapes
      (MatrixBatchAssignmentZero.cfg 0 (frame (binary r.width assignment)) 0 (UnaryTemplate.tape r.width) 1)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [entry,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
        MatrixBatchGateClear.stable,zeroSlots,MatrixBatchAssignmentZero.cfg,RecoveryCalls.restarted]
  obtain ⟨actual,ha,haf,has⟩ := RecoveryFocus.run_config zeroSlots zero_injective MatrixBatchAssignmentZero.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,by omega⟩
  · rw [haf,bf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_zero,zeroPicked,MatrixBatchAssignmentZero.cfg,entry,
      RecoveryCalls.restarted,heads]
  · rw [haf,bf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_zero,zeroPicked,MatrixBatchAssignmentZero.cfg,entry,
      RecoveryCalls.restarted,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
      MatrixBatchGateClear.stable]

theorem install_copy (r : Request) (assignment id cap : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) :
    install slots (tapes r assignment id cap source out backing) (copyOutput r)=
      tapes r assignment 0 cap source out backing := by
  funext i
  fin_cases i <;>
    simp [install,pick_slots,picked,copyOutput,tapes,
      MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable]

theorem copy_run (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) :
    ∃ actual,runFrom copy (8*r.M+8)
      (RecoveryCalls.restarted copy (heads pos out.length) (tapes r assignment id cap source out backing))=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r assignment 0 cap source out backing ∧
      actual.steps≤8*r.M+8 := by
  have hc : 4*r.M+2≤C r := by
    unfold C
    omega
  have ready := MatrixScoreHalvesReset.ready r.M 0 id (C r) hc
  obtain ⟨actual,ha,ah,atapes,as⟩ := CompetitorReusableDecision.bounded_focused_run slots slots_injective
    copyMachine _ _ ready (heads pos out.length) (tapes r assignment id cap source out backing)
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;>
      simp [slots,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable,
        MatrixScoreWeight.zeros])
  exact ⟨actual,ha,ah,atapes.trans (install_copy r assignment id cap source out backing),as⟩

noncomputable def resets := Composition.machine zero copy
noncomputable def machine := Composition.machine MatrixBatchGateClear.machine resets
def budget (r : Request) := (2*D r+4)+1+((4*r.width+2)+1+(8*r.M+8))
noncomputable def input (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) :=
  Composition.leftConfig 11 (MatrixBatchGateClear.input r assignment id cap pos source out backing)

theorem prepare_run (r : Request) (assignment id cap pos : ℕ) (source out : List Bool)
    (backing : Fin 30 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ actual,runFrom machine (budget r) (input r assignment id cap pos source out backing)=some actual ∧
      actual.final.heads=heads pos out.length ∧
      actual.final.tapes=tapes r 0 0 (max cap (D r+1)) source out (fun _ => List.replicate (D r) false) ∧
      actual.steps≤budget r := by
  obtain ⟨cleared,hc,ch,ct,cs⟩ := MatrixBatchGateClear.clear_run r assignment id cap pos source out backing hb
  obtain ⟨left,hl,lh,lt,ls⟩ := zero_run r assignment id (max cap (D r+1)) pos source out (fun _ => List.replicate (D r) false)
  obtain ⟨right,hr,rh,rt,rs⟩ := copy_run r 0 id (max cap (D r+1)) pos source out (fun _ => List.replicate (D r) false)
  have hi : Composition.restart left.final copy.start=
      RecoveryCalls.restarted copy (heads pos out.length)
        (tapes r 0 id (max cap (D r+1)) source out (fun _ => List.replicate (D r) false)) := by
    apply configuration_ext
    · rfl
    · exact lh
    · exact lt
  rw [←hi] at hr
  have htail := Composition.run_join zero copy _ _ _ left right hl hr
  have he : Composition.restart cleared.final resets.start=
      Composition.leftConfig 6 (RecoveryCalls.restarted zero (heads pos out.length)
        (tapes r assignment id (max cap (D r+1)) source out (fun _ => List.replicate (D r) false))) := by
    apply configuration_ext
    · rfl
    · exact ch
    · exact ct
  rw [←he] at htail
  have joined := Composition.run_join MatrixBatchGateClear.machine resets _ _ _ cleared (Composition.joinedReceipt left right) hc htail
  refine ⟨Composition.joinedReceipt cleared (Composition.joinedReceipt left right),joined,rh,rt,?_⟩
  change cleared.steps+1+(left.steps+1+right.steps)≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateReset
