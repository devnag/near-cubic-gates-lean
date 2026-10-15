import Proof.CaseAnalysis.RowsTouchingPascalNext

/-! The whole next-row call begins and ends with zero heads. Its only
workspace tape is a paid reusable reset log; the output bank has the exact
fixed row capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalReady
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (q : ℕ):=(q+1)*(2*(q+1)+1)
def directions : Fin 4→HeadMove:=![.stay,.stay,.stay,.right]
def move:=DecompositionCountPosition.move directions
noncomputable def core:=Composition.machine move PascalNext.machine
noncomputable def machine:=MaskedReset.machine core (fun _=>true)
def budget (q : ℕ):=2*(PascalNext.budget q+2)+2

theorem ready (q m C : ℕ) (hm:m<q) (hC:PascalNext.budget q+2≤C):
    Step machine (budget q) (fun _=>0)
      ![PascalRow.row (q+1) m q,PascalRow.row (q+1) m q,List.replicate (width q) false,
        CompareMachine.word q,List.replicate C false]
      (fun _=>0)
      ![PascalRow.row (q+1) m q,PascalRow.row (q+1) m q,PascalRow.row (q+1) (m+1) q,
        CompareMachine.word q,List.replicate C false]:=by
  let oldRow:=PascalRow.row (q+1) m q
  let nextRow:=PascalRow.row (q+1) (m+1) q
  let data : Fin 4→List Bool:=![oldRow,oldRow,[],CompareMachine.word q]
  obtain ⟨a,ar,af,_⟩:=DecompositionCountPosition.move_run directions (fun _=>0) data
  have first:Step move 1 (fun _=>0) data ![0,0,0,1] data:=by
    refine Step.of_run ar ?_ ?_
    · rw [af];funext i;fin_cases i <;> rfl
    · rw [af]
  obtain ⟨b,br,_,bh,bt⟩:=PascalNext.next_run q m [] hm
  have next:Step PascalNext.machine (PascalNext.budget q) ![0,0,0,1] data
      ![q*(2*(q+1)+1),width q,nextRow.length,1]
      ![oldRow,oldRow,nextRow,CompareMachine.word q]:=by
    refine Step.of_run (r:=b) ?_ ?_ ?_
    · exact br
    · simpa only [List.nil_append,width,nextRow] using bh
    · simpa only [List.nil_append] using bt
  have both:=first.seq next
  have capEq:1+1+PascalNext.budget q=PascalNext.budget q+2:=by omega
  rw [capEq] at both
  have padded:=both.pad (![0,0,width q,0] : Fin 4→ℕ)
  have masked:=padded.mask (fun _=>true) (by intro i _;rfl) hC
  have rowLen:nextRow.length=width q:=PascalRow.row_length (q+1) (m+1) q
  have hin:(Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad ((![0,0,width q,0] : Fin 4→ℕ) i) (data i))
      (fun _ : Fin 1=>List.replicate C false))=
      ![oldRow,oldRow,List.replicate (width q) false,CompareMachine.word q,List.replicate C false]:=by
    funext i;fin_cases i <;> simp [data,ZeroPadding.pad,Fin.addCases]
  have hout:(Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad ((![0,0,width q,0] : Fin 4→ℕ) i)
        ((![oldRow,oldRow,nextRow,CompareMachine.word q] : Fin 4→List Bool) i))
      (fun _ : Fin 1=>List.replicate C false))=
      ![oldRow,oldRow,nextRow,CompareMachine.word q,List.replicate C false]:=by
    funext i;fin_cases i <;> simp [ZeroPadding.pad,Fin.addCases,rowLen]
  exact masked.congr_in (by funext i;fin_cases i <;> rfl) hin |>.congr
    (by funext i;fin_cases i <;> rfl) hout

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalReady
