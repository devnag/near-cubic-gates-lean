import Proof.SourceAssembly.SourceNativeList
import Proof.Assembly.AppendOutputFrame

/- Exact native-field loop on the actual retained unary template. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyNativeListReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SourceAssemblyNativeList
noncomputable section

theorem template_eq (n : Nat) : ZeroPadding.pad (n+2) (CompareMachine.word n)=UnaryTemplate.tape n := by
  simp [CompareMachine.word,UnaryTemplate.tape,ZeroPadding.pad]

theorem unary_run (pre : List Bool) (xs : List Nat) (tail backing out : List Bool) :
    Step SourceAssemblyNativeList.machine ((stream xs).length+5*xs.length+3)
      ![pre.length,0,out.length,1]
      ![pre++stream xs++tail,backing,out,UnaryTemplate.tape xs.length]
      ![pre.length+(stream xs).length,0,(out++stream xs).length,1]
      ![pre++stream xs++tail,savedFields xs backing,out++stream xs,UnaryTemplate.tape xs.length] := by
  obtain ⟨r,hr,hf,hs⟩:=copy_run pre xs tail backing out
  have base:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have paid:=base.pad (![0,0,0,xs.length+2] : Fin 4→Nat)
  apply (paid.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> simp [SourceAssemblyNativeList.cfg,
    PCPPQueryField.store,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases,template_eq]

theorem forward : CursorRestore.NoLeft SourceAssemblyNativeList.machine 2 :=
  CursorRestore.repeat_forward (PCPPQueryField.machine true) (fun _ _=>true) 2
    EquationRowRaw.header_field_forward

end
end SourceAssemblyNativeListReady
