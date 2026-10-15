import Proof.CaseAnalysis.RowsTupleSeekDock

/-! The count parser's actual unary template supplies the paired loop.
Its trailing false cell is ordinary zero padding of the original driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairsHeads (np sp : ℕ) (native support : List Bool) : Fin 5→ℕ :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>ℕ) (pairHeads np sp native support) (fun _=>1)
def pairsData (ns ss native support : List Bool) (n : ℕ) : Fin 5→List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool) (pairData ns ss native support) (fun _=>UnaryTemplate.tape n)

theorem pairs_unary_run (keep : Bool) (gs : List GatePair) (np nt sp st native support : List Bool) :
    Step (pairsMachine keep) (pairsCost gs) (pairsHeads np.length sp.length native support)
      (pairsData (np++nativeWord gs++nt) (sp++supportWord gs++st) native support gs.length)
      (pairsHeads (np.length+(nativeWord gs).length) (sp.length+(supportWord gs).length)
        (native++selected keep (nativeWord gs)) (support++selected keep (supportWord gs)))
      (pairsData (np++nativeWord gs++nt) (sp++supportWord gs++st)
        (native++selected keep (nativeWord gs)) (support++selected keep (supportWord gs)) gs.length) := by
  obtain ⟨r,hr,rf,_⟩ := pairs_run keep gs np nt sp st native support
  have raw := Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have padded := raw.pad (fun i=>if i=4 then gs.length+2 else 0)
  apply (padded.congr_in rfl ?_).congr rfl ?_
  all_goals
    funext i;fin_cases i <;>
      simp [pairsCfg,pairEntry,pairsData,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        UnaryTemplate.tape,CompareMachine.word,Fin.addCases,ZeroPadding.pad,List.append_assoc]

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
