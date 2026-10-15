import Proof.MachineModel.OrdinaryMatrixCoordinateLoad

/-! One inner-major right-matrix row: skip the A-copy prefix and keep the
B-copy suffix using one reused U template. No source/output rewind occurs. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightSelect
open LocalBitMultitape
open StablePartition (Record recordsBits)
open PayloadCounted (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 34 := Composition.machine (PayloadRow.machine false) (PayloadRow.machine true)

theorem row_run (pre : List Bool) (left right : List Record) (suffix out : List Bool)
    (hlen : left.length=right.length) :
    ∃ actual : ExecutionReceipt 3 34,
      runFrom machine ((recordsBits left).length+(recordsBits right).length+6*right.length+9)
        (config machine.start (pre++recordsBits left++recordsBits right++suffix) pre.length out
          1 (UnaryTemplate.tape right.length))=some actual ∧
      actual.final=config 33 (pre++recordsBits left++recordsBits right++suffix)
        (pre.length+(recordsBits left).length+(recordsBits right).length) (out++right.map Prod.fst)
        1 (UnaryTemplate.tape right.length) ∧
      actual.steps=(recordsBits left).length+(recordsBits right).length+6*right.length+9 := by
  obtain ⟨first,hfirst,hff,hfs,_⟩ := PayloadRow.row_run false pre left (recordsBits right++suffix) out
  obtain ⟨last,hl,hlf,hls,_⟩ := PayloadRow.row_run true (pre++recordsBits left) right suffix out
  simp only [PayloadCounted.selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hff
  simp only [PayloadCounted.selected,↓reduceIte] at hlf
  rw [hlen] at hfirst hff hfs
  have hsource : pre++recordsBits left++(recordsBits right++suffix)=
      pre++recordsBits left++recordsBits right++suffix := by simp [List.append_assoc]
  rw [hsource] at hfirst hff
  have hpos : (pre++recordsBits left).length=pre.length+(recordsBits left).length := by simp
  rw [hpos] at hl hlf
  have hi : Composition.restart first.final (PayloadRow.machine true).start=
      config (PayloadRow.machine true).start (pre++recordsBits left++recordsBits right++suffix)
        (pre.length+(recordsBits left).length) out 1 (UnaryTemplate.tape right.length) := by
    rw [hff]
    rfl
  rw [←hi] at hl
  have hj := Composition.run_join (PayloadRow.machine false) (PayloadRow.machine true)
    ((recordsBits left).length+3*right.length+4) ((recordsBits right).length+3*right.length+4)
    (config (PayloadRow.machine false).start (pre++recordsBits left++recordsBits right++suffix)
      pre.length out 1 (UnaryTemplate.tape right.length)) first last hfirst hl
  have htime : ((recordsBits left).length+3*right.length+4)+1+
      ((recordsBits right).length+3*right.length+4)=
      (recordsBits left).length+(recordsBits right).length+6*right.length+9 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 17 last.final=_
    rw [hlf]
    rfl
  · change first.steps+1+last.steps=_
    omega

end NearCubicWires.RepairOrdinary.MatrixRightSelect
