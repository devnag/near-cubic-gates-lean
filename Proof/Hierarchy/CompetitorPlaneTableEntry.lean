import Proof.Hierarchy.CompetitorPlaneTableLoop

/-! Paid entry and exit of the complete serialized-plane table loop. Only
the one physical repeat-driver head moves at the boundary; the global
packet cursor is retained, so no cumulative source-prefix scan occurs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTableEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (ambient : Fin 34 → List Bool) (count : ℕ) : Fin 35 → List Bool :=
  Fin.addCases (m := 34) (n := 1) (motive := fun _ => List Bool) ambient (fun _ => CompareMachine.word count)
def heads (pos driver : ℕ) : Fin 35 → ℕ :=
  Fin.addCases (m := 34) (n := 1) (motive := fun _ => ℕ) (CompetitorPlanePacketDock.heads pos) (fun _ => driver)
def cfg {s : ℕ} (q : Fin s) (pos driver : ℕ) (ambient : Fin 34 → List Bool) (count : ℕ) : Configuration 35 s :=
  ⟨q,heads pos driver,tapes ambient count⟩
def move (direction : HeadMove) : Machine 35 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,Fin.addCases (m := 34) (n := 1) (motive := fun _ => HeadMove)
      (fun _ => .stay) (fun _ => direction)⟩ else none
noncomputable def tail := Composition.machine CompetitorPlaneTable.machine (move .left)
noncomputable def machine := Composition.machine (move .right) tail
def budget (w n count : ℕ) := tableBudget w n count+4

theorem move_run (direction : HeadMove) (pos driver count : ℕ) (ambient : Fin 34 → List Bool) :
    ∃ r,runFrom (move direction) 1 (cfg 0 pos driver ambient count)=some r ∧
      r.final=cfg 1 pos (direction.apply driver) ambient count ∧ r.steps=1 := by
  have hstep : step (move direction) (cfg 0 pos driver ambient count)=
      some (cfg 1 pos (direction.apply driver) ambient count) := by
    simp only [step,move,cfg,Fin.val_zero,ite_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 34) (n := 1) ?_ ?_ i <;> intro j
      · simp [applyAction,heads,HeadMove.apply]
      · simp [applyAction,heads]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem repeat_cfg {s : ℕ} (phase : Fin 5) (q : Fin s) (pos driver count : ℕ) (ambient : Fin 34 → List Bool) :
    RepeatMachine.cfg phase (CompetitorPlanePacketDock.cfg q pos ambient) count driver=
      cfg (RepeatMachine.phaseCode s phase) pos driver ambient count := rfl

theorem table_run {n : ℕ} (b p : ℕ) (planes : List (Plane n)) (state : State n)
    (pre suffix : List Bool) (ambient : Fin 34 → List Bool)
    (hlength : planes.length≤p) (hvalid : ∀ a∈planes,a.Valid b p)
    (hstate : Bounded b p 0 state)
    (hcontext : TableContext b (CompetitorPlaneWidth.width b p) state ambient)
    (hsource : ambient 32=pre++stream b planes++suffix) :
    ∃ r out,runFrom machine (budget (CompetitorPlaneWidth.width b p) n planes.length)
      (cfg machine.start pre.length 0 ambient planes.length)=some r ∧
      r.steps≤budget (CompetitorPlaneWidth.width b p) n planes.length ∧
      r.final.heads=heads (pre.length+(stream b planes).length) 0 ∧
      r.final.tapes=tapes out planes.length ∧
      TableContext b (CompetitorPlaneWidth.width b p) (evaluate planes state) out ∧
      out 32=pre++stream b planes++suffix ∧ Bounded b p (2*planes.length) (evaluate planes state) := by
  obtain ⟨entry,he,hef,hes⟩ := move_run .right pre.length 0 planes.length ambient
  obtain ⟨loop,out,hl,hls,hlf,hc,hsrc,hbound⟩ := table_loop_run b p planes state pre suffix ambient
    hlength hvalid hstate hcontext hsource
  have heLoop : Composition.restart entry.final CompetitorPlaneTable.machine.start=
      RepeatMachine.cfg 0 (CompetitorPlanePacketDock.cfg CompetitorPlanePacketPair.machine.start pre.length ambient)
        planes.length 1 := by
    rw [hef,repeat_cfg]
    rfl
  have hl' : runFrom CompetitorPlaneTable.machine (tableBudget (CompetitorPlaneWidth.width b p) n planes.length)
      (Composition.restart entry.final CompetitorPlaneTable.machine.start)=some loop := by
    rw [heLoop]
    exact hl
  obtain ⟨done,hd,hdf,hds⟩ := move_run .left (pre.length+(stream b planes).length) 1 planes.length out
  have hd' : runFrom (move .left) 1 (Composition.restart loop.final (move .left).start)=some done := by
    rw [hlf,repeat_cfg]
    exact hd
  have htail := Composition.run_join CompetitorPlaneTable.machine (move .left) _ _ _ loop done hl' hd'
  have hall := Composition.run_join (move .right) tail _ _ _ entry
    (Composition.joinedReceipt loop done) he htail
  have hcost : 1+1+(tableBudget (CompetitorPlaneWidth.width b p) n planes.length+1+1)=
      budget (CompetitorPlaneWidth.width b p) n planes.length := by unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt entry (Composition.joinedReceipt loop done),out,?_,?_,?_,?_,hc,hsrc,hbound⟩
  · exact hall
  · change entry.steps+1+(loop.steps+1+done.steps)≤budget (CompetitorPlaneWidth.width b p) n planes.length
    unfold budget
    omega
  · change done.final.heads=_
    rw [hdf]
    rfl
  · change done.final.tapes=_
    rw [hdf]
    rfl

end NearCubicWires.RepairOrdinary.CompetitorPlaneTableEntry
