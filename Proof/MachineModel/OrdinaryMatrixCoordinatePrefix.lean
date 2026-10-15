import Proof.MachineModel.OrdinaryMatrixRightLoop

/-! Copy the two physical cells encoding a matrix payload bit. Both global
cursors advance; no growing source or output is rewound. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinatePrefix
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scanned => if q.val=0 then
      some ⟨1,![none,some (scanned 0)],fun _ => .right⟩
    else if q.val=1 then some ⟨2,![none,some (scanned 0)],fun _ => .right⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem first_step (pre tail out : List Bool) (bit : Bool) :
    step machine (cfg 0 (pre++bit::tail) pre.length out)=
      some (cfg 1 (pre++bit::tail) (pre.length+1) (out++[bit])) := by
  have hr := read_append pre tail bit
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_append]

theorem second_step (pre tail out : List Bool) (bit : Bool) :
    step machine (cfg 1 (pre++bit::tail) pre.length out)=
      some (cfg 2 (pre++bit::tail) (pre.length+1) (out++[bit])) := by
  have hr := read_append pre tail bit
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_append]

theorem prefix_run (pre suffix out : List Bool) (cell : Bool) :
    ∃ r : ExecutionReceipt 2 3,
      runFrom machine 2 (cfg 0 (pre++[true,cell]++suffix) pre.length out)=some r ∧
      r.final=cfg 2 (pre++[true,cell]++suffix) (pre.length+2) (out++[true,cell]) ∧ r.steps=2 := by
  have hfirst := Timed.single (by rfl) (first_step pre (cell::suffix) out true)
  have hsecond := Timed.single (by rfl) (second_step (pre++[true]) suffix (out++[true]) cell)
  have hs : Timed machine 1
      (cfg 1 (pre++[true,cell]++suffix) (pre.length+1) (out++[true]))
      (cfg 2 (pre++[true,cell]++suffix) (pre.length+2) (out++[true,cell])) := by
    simpa [List.append_assoc,Nat.add_assoc] using hsecond
  have hf : Timed machine 1
      (cfg 0 (pre++[true,cell]++suffix) pre.length out)
      (cfg 1 (pre++[true,cell]++suffix) (pre.length+1) (out++[true])) := by
    simpa [List.append_assoc] using hfirst
  exact (hf.trans hs).run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixCoordinatePrefix
