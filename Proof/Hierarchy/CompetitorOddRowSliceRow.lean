import Proof.MachineModel.OrdinaryMatrixRawBlock
import Proof.Hierarchy.CompetitorResidueTableContext

/-! One actual raw odd-residual row: keep the first half-row and skip the
second using the same physically supplied byte-count driver. The driver
returns to1 after both calls; source and output remain streaming. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rowProgram := Composition.machine (MatrixRawBlock.machine true) (MatrixRawBlock.machine false)
def rowBudget (h : ℕ) := 4*h+9

theorem row_run (pre left right suffix out : List Bool) (hlen : right.length=left.length) :
    ∃ r,runFrom rowProgram (rowBudget left.length)
      (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape left.length) 1
        (pre++left++right++suffix) pre.length out)=some r ∧
      r.final=MatrixRawBlock.config 9 (UnaryTemplate.tape left.length) 1
        (pre++left++right++suffix) (pre.length+2*left.length) (out++left) ∧
      r.steps=rowBudget left.length := by
  obtain ⟨first,hfirst,hff,hfs,_⟩ := MatrixRawBlock.block_run true pre left (right++suffix) out
  obtain ⟨last,hlast,hlf,hls,_⟩ := MatrixRawBlock.block_run false (pre++left) right suffix (out++left)
  have he : Composition.restart first.final (MatrixRawBlock.machine false).start=
      MatrixRawBlock.config 0 (UnaryTemplate.tape right.length) 1
        ((pre++left)++right++suffix) (pre++left).length (out++left) := by
    rw [hff,hlen]
    simp only [MatrixRawBlock.selected,↓reduceIte,List.length_append,List.append_assoc]
    rfl
  have hl' : runFrom (MatrixRawBlock.machine false) (2*right.length+4)
      (Composition.restart first.final (MatrixRawBlock.machine false).start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join (MatrixRawBlock.machine true) (MatrixRawBlock.machine false)
    _ _ _ first last hfirst hl'
  have htime : (2*left.length+4)+1+(2*right.length+4)=rowBudget left.length := by
    unfold rowBudget
    omega
  rw [htime] at hall
  have hin : Composition.leftConfig 5
      (MatrixRawBlock.config 0 (UnaryTemplate.tape left.length) 1
        (pre++left++(right++suffix)) pre.length out)=
      MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape left.length) 1
        (pre++left++(right++suffix)) pre.length out := by
    apply configuration_ext <;> rfl
  rw [hin] at hall
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · simpa only [rowProgram,List.append_assoc] using hall
  · change Composition.rightConfig 5 last.final=_
    rw [hlf,hlen]
    simp only [MatrixRawBlock.selected,Bool.false_eq_true,↓reduceIte,List.append_nil,
      List.length_append,List.append_assoc]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,MatrixRawBlock.config]
      omega
    · rfl
  · change first.steps+1+last.steps=rowBudget left.length
    omega

end NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
