import Proof.MachineModel.OrdinaryMatrixUnaryCompare

/-! Physical append and sentinel termination of the growing dimension
tape. The final return scan is charged once, after the binary counter stops. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnaryFinish
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def append (bit : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => some bit,fun _ => if bit then .right else .stay⟩ else none
def config {s : ℕ} (q : Fin s) (out : List Bool) (pos : ℕ) : Configuration 1 s :=
  ⟨q,fun _ => pos,fun _ => out⟩

theorem append_step (bit : Bool) (out : List Bool) :
    step (append bit) (config 0 out out.length) =
      some (config 1 (out++[bit]) (out.length + if bit then 1 else 0)) := by
  simp [step,append,config]
  apply configuration_ext
  · rfl
  · funext i; cases bit <;> simp [applyAction,HeadMove.apply]
  · funext i; simp [applyAction,write_append]

theorem append_run (bit : Bool) (out : List Bool) :
    ∃ r : ExecutionReceipt 1 2,
      runFrom (append bit) 1 (config 0 out out.length) = some r ∧
      r.final = config 1 (out++[bit]) (out.length + if bit then 1 else 0) ∧ r.steps=1 := by
  exact (Timed.single (by rfl) (append_step bit out)).run (by rfl)

def machine : Machine 1 5 := Composition.machine (append false) UnaryTemplate.machine

theorem finish_run (n : ℕ) :
    ∃ r : ExecutionReceipt 1 5,
      runFrom machine (n+4) (config 0 (false::List.replicate n true) (n+1))=some r ∧
      r.final = config 4 (UnaryTemplate.tape n) 1 ∧ r.steps=n+4 := by
  obtain ⟨first,hr,hf,hs⟩ := append_run false (false::List.replicate n true)
  obtain ⟨last,hl,hlf,hls,_⟩ := UnaryTemplate.reset_run n
  have hmid : Composition.restart first.final UnaryTemplate.machine.start =
      UnaryTemplate.config 0 (UnaryTemplate.tape n) (n+1) := by
    rw [hf]
    simp [Composition.restart,UnaryTemplate.machine,UnaryTemplate.config,UnaryTemplate.tape,config]
  rw [← hmid] at hl
  have hj := Composition.run_join (append false) UnaryTemplate.machine 1 (n+2) _ first last hr hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · simpa [machine,Composition.leftConfig,config,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hj
  · change Composition.rightConfig 2 last.final = _
    rw [hlf]
    rfl
  · change first.steps+1+last.steps = _
    omega

end NearCubicWires.RepairOrdinary.MatrixUnaryFinish
