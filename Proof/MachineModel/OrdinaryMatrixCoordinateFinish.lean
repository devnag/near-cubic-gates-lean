import Proof.MachineModel.OrdinaryMatrixRightPaper

/-! Close the transposed record stream with its actual terminator. The
aggregate output is closed once, after the complete streaming traversal. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def closeMachine : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=10 then some false else none,
      fun i => if i.val=10 then .right else .stay⟩ else none
noncomputable def closedMachine : Machine 12 38 := Composition.machine streamMachine closeMachine

theorem close_run (w cap : ℕ) (source record clone rank out : List Bool) (pos : ℕ) :
    ∃ actual : ExecutionReceipt 12 2,
      runFrom closeMachine 1 (cfg 0 w cap source pos record clone rank out)=some actual ∧
      actual.final=cfg 1 w cap source pos record clone rank (out++[false]) ∧ actual.steps=1 := by
  have he : step closeMachine (cfg 0 w cap source pos record clone rank out)=
      some (cfg 1 w cap source pos record clone rank (out++[false])) := by
    simp [step,closeMachine,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,write_append]
  exact (Timed.single (by rfl) he).run (by rfl)

theorem closed_run (w cap : ℕ) (rs : List Record) (pre record clone rank : List Bool)
    (hcap : 2*w ≤ cap) (hr : record.length ≤ 4*w+1)
    (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ finalRecord finalClone finalRank,
      finalRecord.length ≤ 4*w+1 ∧ finalClone.length ≤ 4*w+1 ∧ finalRank.length ≤ 2*w+1 ∧
      ∃ actual : ExecutionReceipt 12 38,
        runFrom closedMachine (rs.length*(64*w+47)+3)
          (cfg closedMachine.start w cap (pre++stream w rs) pre.length record clone rank [])=some actual ∧
        actual.final=cfg 37 w cap (pre++stream w rs) (pre.length+(stream w rs).length)
          finalRecord finalClone finalRank (output w rs++[false]) ∧ actual.steps ≤ rs.length*(64*w+47)+3 := by
  obtain ⟨fr,fc,fk,hfr,hfc,hfk,first,hfirst,hff,hfs⟩ := stream_run w cap rs pre record clone rank [] hcap hr hc hk
  simp only [List.nil_append] at hff
  obtain ⟨last,hl,hlf,hls⟩ := close_run w cap (pre++stream w rs) fr fc fk (output w rs)
    (pre.length+(stream w rs).length)
  have hi : Composition.restart first.final closeMachine.start=
      cfg 0 w cap (pre++stream w rs) (pre.length+(stream w rs).length) fr fc fk (output w rs) := by
    rw [hff]
    rfl
  rw [←hi] at hl
  have hj := Composition.run_join streamMachine closeMachine (rs.length*(64*w+47)+1) 1
    (cfg streamMachine.start w cap (pre++stream w rs) pre.length record clone rank []) first last hfirst hl
  have ht : (rs.length*(64*w+47)+1)+1+1=rs.length*(64*w+47)+3 := by omega
  rw [ht] at hj
  refine ⟨fr,fc,fk,hfr,hfc,hfk,Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 36 last.final=_
    rw [hlf]
    rfl
  · change first.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
