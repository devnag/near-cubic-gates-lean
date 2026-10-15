import Proof.MachineModel.OrdinaryMatrixRawBlock
import Proof.Circuits.DecompositionCountPosition
import Proof.MachineModel.Runs

/-! Append one completed row to the physical full table. The existing raw
block copier pays every copied cell; only its source and driver heads
return, leaving the table's append cursor in place. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.TableAppend
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions : Fin 3→HeadMove:=![.right,.stay,.stay]
def move:=DecompositionCountPosition.move directions
def core:=Composition.machine move (MatrixRawBlock.machine true)
def selected : Fin 3→Bool:=![true,true,false]
def machine:=MaskedReset.machine core selected
def budget (B : ℕ):=4*B+14

theorem append_run (bits out : List Bool) (C : ℕ) (hC:2*bits.length+6≤C):
    Step machine (budget bits.length) ![0,0,out.length,0]
      ![UnaryTemplate.tape bits.length,bits,out,List.replicate C false]
      ![0,0,(out++bits).length,0]
      ![UnaryTemplate.tape bits.length,bits,out++bits,List.replicate C false]:=by
  let data : Fin 3→List Bool:=![UnaryTemplate.tape bits.length,bits,out]
  obtain ⟨a,ar,af,_⟩:=DecompositionCountPosition.move_run directions ![0,0,out.length] data
  have first:Step move 1 ![0,0,out.length] data ![1,0,out.length] data:=by
    refine Step.of_run ar ?_ ?_
    · rw [af];funext i;fin_cases i <;> rfl
    · rw [af]
  obtain ⟨b,br,bf,_,_⟩:=MatrixRawBlock.block_run true [] bits [] out
  have copied:Step (MatrixRawBlock.machine true) (2*bits.length+4) ![1,0,out.length] data
      ![1,bits.length,(out++bits).length] ![UnaryTemplate.tape bits.length,bits,out++bits]:=by
    refine Step.of_run (r:=b) ?_ ?_ ?_
    · change runFrom (MatrixRawBlock.machine true) _ (MatrixRawBlock.config 0 _ 1 bits 0 out)=some b
      simpa only [List.nil_append,List.append_nil,List.length_nil] using br
    · rw [bf];simp only [MatrixRawBlock.config,MatrixRawBlock.selected,if_true,List.length_nil,Nat.zero_add]
    · rw [bf];simp only [MatrixRawBlock.config,MatrixRawBlock.selected,if_true,List.nil_append,List.append_nil]
  have both:=first.seq copied
  have time:1+1+(2*bits.length+4)=2*bits.length+6:=by omega
  rw [time] at both
  have masked:=both.mask selected (by intro i hi;fin_cases i <;> simp_all [selected]) hC
  have allTime:2*(2*bits.length+6)+2=budget bits.length:=by unfold budget;omega
  rw [allTime] at masked
  exact masked.congr_in (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> rfl) |>.congr
    (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.TableAppend
