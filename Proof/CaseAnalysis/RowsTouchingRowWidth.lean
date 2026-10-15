import Proof.CaseAnalysis.RowsTouchingFrameMeasure

/-! The row-width driver is read from the actual initialized Pascal row;
no computed row length is installed as a tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.RowWidth
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions : Fin 3→HeadMove:=![.stay,.stay,.right]
def move:=DecompositionCountPosition.move directions
noncomputable def raw:=Composition.machine move FrameMeasure.machine
noncomputable def machine:=MaskedReset.machine raw (fun _=>true)
def budget (q : ℕ):=2*(FrameMeasure.budget (q+1) (q+1)+2)+2

theorem width_run (q C : ℕ) (hC:FrameMeasure.budget (q+1) (q+1)+2≤C):
    Step machine (budget q) (fun _=>0)
      ![PascalRow.row (q+1) 0 q,[],CompareMachine.word (q+1),List.replicate C false]
      (fun _=>0)
      ![PascalRow.row (q+1) 0 q,List.replicate (PascalReady.width q) true,
        CompareMachine.word (q+1),List.replicate C false]:=by
  let w:=q+1
  let words:=(List.range (q+1)).map (fun k=>binary w (Nat.choose 0 k))
  have length:words.length=w:=by simp [words,w]
  have source:words.flatMap frame=PascalRow.row w 0 q:=by
    simp only [words,List.flatMap_map,PascalRow.row,PascalRow.field]
  have size:(words.flatMap frame).length=PascalReady.width q:=by rw [source];exact PascalRow.row_length w 0 q
  obtain ⟨r,run,rf,_⟩:=FrameMeasure.measure_run words [] [] w (by
    intro bits h;obtain ⟨k,_,rfl⟩:=List.mem_map.mp h;simp)
  rw [length] at run rf
  let data : Fin 3→List Bool:=![PascalRow.row w 0 q,[],CompareMachine.word w]
  have input:RepeatMachine.cfg 0 (FrameMeasure.entry words [] [] 0 []) w 1=
      (⟨FrameMeasure.machine.start,![0,0,1],data⟩ : Configuration 3 _):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,FrameMeasure.entry,FrameSkipMark.cfg,
        List.nil_append,List.append_nil,source]
      funext i;fin_cases i <;> rfl
  rw [input] at run
  have measured:Step FrameMeasure.machine (FrameMeasure.budget w w) ![0,0,1] data r.final.heads
      ![PascalRow.row w 0 q,List.replicate (PascalReady.width q) true,CompareMachine.word w]:=by
    refine Step.of_run run rfl ?_
    rw [rf]
    simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,FrameMeasure.entry,FrameSkipMark.cfg,
      List.nil_append,List.append_nil,source,List.length_replicate,PascalRow.row_length]
    funext i;fin_cases i <;> rfl
  obtain ⟨a,ar,af,_⟩:=DecompositionCountPosition.move_run directions (fun _=>0) data
  have first:Step move 1 (fun _=>0) data ![0,0,1] data:=by
    refine Step.of_run ar ?_ ?_
    · rw [af];funext i;fin_cases i <;> rfl
    · rw [af]
  have both:=first.seq measured
  rw [show 1+1+FrameMeasure.budget w w=FrameMeasure.budget w w+2 by omega] at both
  have reset:=both.mask (fun _=>true) (by intro i _;rfl) hC
  exact reset.congr_in (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> rfl) |>.congr
    (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.RowWidth
