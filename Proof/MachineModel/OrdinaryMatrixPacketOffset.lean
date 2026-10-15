import Proof.MachineModel.OrdinaryMatrixPacketReuse
import Proof.Circuits.MatrixBucketDimensionsIncrement

/-! Physical initialization and two-mark advancement of the bit-offset
sentinel. The all-plane loop keeps this single tape at head one. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketOffset
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def init : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => some false,fun _ => .right⟩
    else if q.val=1 then some ⟨2,fun _ => some false,fun _ => .stay⟩ else none
def initCfg (q : Fin 3) (pos : ℕ) (bits : List Bool) : Configuration 1 3 := ⟨q,fun _ => pos,fun _ => bits⟩
theorem init_run : ∃ actual,run init 2 (fun _ => [])=some actual ∧
    actual.final.tapes=(fun _ => UnaryTemplate.tape 0) ∧ actual.final.heads=(fun _ => 1) ∧ actual.steps=2 := by
  have h0 : step init (initCfg 0 0 [])=some (initCfg 1 1 [false]) := by rfl
  have h1 : step init (initCfg 1 1 [false])=some (initCfg 2 1 [false,false]) := by rfl
  obtain ⟨actual,ha,hf,hs⟩ := ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)
  exact ⟨actual,ha,by rw [hf]; rfl,by rw [hf]; rfl,hs⟩

def move (direction : HeadMove) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun _ => direction⟩ else none
def moveCfg (q : Fin 2) (bits : List Bool) (pos : ℕ) : Configuration 1 2 := ⟨q,fun _ => pos,fun _ => bits⟩
theorem move_run (direction : HeadMove) (bits : List Bool) (pos : ℕ) : ∃ actual,
    runFrom (move direction) 1 (moveCfg 0 bits pos)=some actual ∧
    actual.final=moveCfg 1 bits (direction.apply pos) ∧ actual.steps=1 := by
  have hs : step (move direction) (moveCfg 0 bits pos)=some (moveCfg 1 bits (direction.apply pos)) := by rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def twice := Composition.machine MatrixBucketDimensions.Increment.machine MatrixBucketDimensions.Increment.machine
theorem twice_ready (c : ℕ) : ClockJoin.ReadyRun twice (4*c+13)
    (fun _ => UnaryTemplate.tape c) (fun _ => UnaryTemplate.tape (c+2)) := by
  obtain ⟨first,hf,ft,fh,fs⟩ := MatrixBucketDimensions.Increment.increment_run c
  obtain ⟨last,hl,lt,lh,ls⟩ := MatrixBucketDimensions.Increment.increment_run (c+1)
  have h0 : ClockJoin.ReadyRun MatrixBucketDimensions.Increment.machine (2*c+5)
      (fun _ => UnaryTemplate.tape c) (fun _ => UnaryTemplate.tape (c+1)) := ⟨first,hf,ft,fh,fs.le⟩
  have h1 : ClockJoin.ReadyRun MatrixBucketDimensions.Increment.machine (2*(c+1)+5)
      (fun _ => UnaryTemplate.tape (c+1)) (fun _ => UnaryTemplate.tape (c+2)) := ⟨last,hl,lt,lh,ls.le⟩
  have joined := ClockJoin.join _ _ _ _ _ _ _ h0 h1
  have hb : (2*c+5)+1+(2*(c+1)+5)=4*c+13 := by omega
  rw [hb] at joined
  exact joined

noncomputable def first := Composition.machine (move .left) twice
noncomputable def machine := Composition.machine first (move .right)
def input (bit : ℕ) := Composition.leftConfig 2 (Composition.leftConfig 10 (moveCfg 0 (UnaryTemplate.tape (2*bit)) 1))
def budget (bit : ℕ) := 8*bit+17

theorem advance_run (bit : ℕ) : ∃ actual,
    runFrom machine (budget bit) (input bit)=some actual ∧
    actual.final.tapes=(fun _ => UnaryTemplate.tape (2*(bit+1))) ∧
    actual.final.heads=(fun _ => 1) ∧ actual.steps≤budget bit := by
  obtain ⟨pre,hp,pf,ps⟩ := move_run .left (UnaryTemplate.tape (2*bit)) 1
  obtain ⟨middle,hm,mt,mh,ms⟩ := twice_ready (2*bit)
  have hi : Composition.restart pre.final twice.start=initialConfiguration twice (fun _ => UnaryTemplate.tape (2*bit)) := by
    rw [pf]
    rfl
  change runFrom twice (4*(2*bit)+13) (initialConfiguration twice (fun _ => UnaryTemplate.tape (2*bit)))=some middle at hm
  rw [←hi] at hm
  have joined := Composition.run_join (move .left) twice _ _ _ pre middle hp hm
  let before := Composition.joinedReceipt pre middle
  obtain ⟨last,hl,lf,ls⟩ := move_run .right (UnaryTemplate.tape (2*bit+2)) 0
  have hj : Composition.restart before.final (move .right).start=moveCfg 0 (UnaryTemplate.tape (2*bit+2)) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      exact mh i
    · exact mt
  rw [←hj] at hl
  have complete := Composition.run_join first (move .right) _ _ _ before last joined hl
  have hb : (1+1+(4*(2*bit)+13))+1+1=budget bit := by unfold budget; omega
  rw [hb] at complete
  refine ⟨Composition.joinedReceipt before last,complete,?_,?_,?_⟩
  · change last.final.tapes=_
    rw [lf]
    change (fun _ : Fin 1 => UnaryTemplate.tape (2*bit+2))=(fun _ => UnaryTemplate.tape (2*(bit+1)))
    rw [show 2*bit+2=2*(bit+1) by omega]
  · change last.final.heads=_
    rw [lf]
    rfl
  · change (pre.steps+1+middle.steps)+1+last.steps≤budget bit
    rw [ps,ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixPacketOffset
