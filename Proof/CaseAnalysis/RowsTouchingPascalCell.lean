import Proof.MachineModel.OrdinaryAdd
import Proof.Circuits.DecompositionCountPosition
import Proof.CaseAnalysis.TouchingArithmeticBounds
import Proof.CaseAnalysis.RowsCircuitBottomReturned

/-! A Pascal cell uses the existing streaming binary adder. Its two
actual row cursors consume adjacent fixed-width fields; the sum appends
at the table cursor, and one paid move passes both input delimiters. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalCell
open LocalBitMultitape SignedSortKey RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions : Fin 3→HeadMove:=![.right,.right,.stay]
def move:=DecompositionCountPosition.move directions
def machine:=Composition.machine Add.machine move
def budget (w : ℕ):=2*w+3

theorem cell_run (w a b : ℕ) (leftPre rightPre leftTail rightTail out : List Bool)
    (hfit:a+b<2^w):
    ∃ r,runFrom machine (budget w)
      ⟨machine.start,![leftPre.length,rightPre.length,out.length],
        ![leftPre++frame (binary w a)++leftTail,rightPre++frame (binary w b)++rightTail,out]⟩=some r ∧
      r.steps≤budget w ∧
      r.final.heads=![leftPre.length+2*w+1,rightPre.length+2*w+1,(out++frame (binary w (a+b))).length] ∧
      r.final.tapes=![leftPre++frame (binary w a)++leftTail,rightPre++frame (binary w b)++rightTail,
        out++frame (binary w (a+b))]:=by
  have hpref:=Add.add_prefix leftPre rightPre (binary w a) (binary w b) leftTail rightTail out [] false (by simp)
  obtain ⟨first,firstRun,ff,fs,_⟩:=hpref.run (by rfl) (by simp;omega)
  have hs:Add.sum (binary w a) (binary w b) false=binary w (a+b):=Add.sum_binary w a b hfit
  rw [hs] at ff
  have fh:first.final.heads=![leftPre.length+2*w,rightPre.length+2*w,(out++frame (binary w (a+b))).length]:=by
    rw [ff]
    simp only [Add.config,binary_length]
  have ft:first.final.tapes=![leftPre++frame (binary w a)++leftTail,rightPre++frame (binary w b)++rightTail,
      out++frame (binary w (a+b))]:=by
    rw [ff]
    simp only [Add.config,StablePartition.Workspace.overlay,List.drop_nil,List.append_nil]
  obtain ⟨last,lastRun,lf,ls⟩:=DecompositionCountPosition.move_run directions first.final.heads first.final.tapes
  obtain ⟨r,run,rs,rh,rt⟩:=joined Add.machine move (2*w+1) 1
    ![leftPre.length,rightPre.length,out.length]
    ![leftPre++frame (binary w a)++leftTail,rightPre++frame (binary w b)++rightTail,out]
    first last (by simpa only [Add.machine,Add.config,binary_length,StablePartition.Workspace.overlay,List.drop_nil,List.append_nil] using firstRun)
    lastRun (by simpa only [binary_length] using fs.le) ls.le
  refine ⟨r,run,rs,?_,?_⟩
  · rw [rh,lf]
    change (fun i=>(directions i).apply (first.final.heads i))=_
    rw [fh]
    funext i;fin_cases i <;> rfl
  · rw [rt,lf];exact ft

theorem choose_fit (q m k : ℕ) (hm:m<q):
    Nat.choose m k+Nat.choose m (k+1)<2^(q+1):=by
  rw [←Nat.choose_succ_succ]
  exact RepairSource.CloseoutTouchingArithmetic.binomial_fits q (m+1) (k+1) (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalCell
