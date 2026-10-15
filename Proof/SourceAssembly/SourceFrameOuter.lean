import Proof.SourceAssembly.SourceCircuitFrame
import Proof.SourceAssembly.SLoadSuffixFrame
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyFrameOuter
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
noncomputable section

def machine:=AppendOutputFrame.machine (CloseoutRowsTupleSeek.frameMachine true) 1

theorem run (bits : List Bool) : ∃ A,
    Step machine (12*bits.length+13) (fun _=>0)
      (AppendOutputFrame.input (![frame bits,[]] : Fin 2→List Bool)) (fun _=>0) A ∧
      A 4=frame (frame bits) := by
  have raw:Step (CloseoutRowsTupleSeek.frameMachine true) (2*bits.length+1)
      (fun _=>0) ![frame bits,[]] (![ (frame bits).length,(frame bits).length]) ![frame bits,frame bits]:=by
    apply ((CloseoutRowsTupleSeek.frame_run true [] bits [] []).congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;>simp [CloseoutRowsTupleSeek.fieldHeads,
      CloseoutRowsTupleSeek.fieldData,CloseoutRowsTupleSeek.selected]
  obtain ⟨r,hr,hh,ht,hs⟩:=raw
  obtain ⟨f,hf,fo,fh,fs⟩:=AppendOutputFrame.frame_run (CloseoutRowsTupleSeek.frameMachine true) 1
    SourceAssemblyCircuitFrame.frame_forward _ _ r hr (frame bits)
    (congrFun ht 1) (congrFun hh 1)
  have bound:2*r.steps+4*(frame bits).length+7≤12*bits.length+13:=by
    rw [frame_length];omega
  refine ⟨f.final.tapes,?_,fo⟩
  exact (Step.of_run hf (funext fh) rfl).enlarge bound

end
end SourceAssemblyFrameOuter
