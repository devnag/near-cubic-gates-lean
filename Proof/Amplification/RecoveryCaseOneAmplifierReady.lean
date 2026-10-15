import Proof.MachineModel.OrdinaryAmplifierReplay
import Proof.Amplification.RecoveryPCPFormulaResumeProofHierarchyActual

/-! Execute the selected schedule amplifier and physically reset its exact
framed output for the enclosing recovery graph. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneAmplifier
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ExecutableInterfaces OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine (p : OrdinaryProgram) := Rewind.machine (AmplifierReplay.Dock.machine p.machine p.outputTape)
def tapes (p : OrdinaryProgram) := p.tapeCount+1+27+1
def output (p : OrdinaryProgram) : Fin (tapes p) := (AmplifierReplay.Dock.output p.tapeCount).castAdd 1
def input (p : OrdinaryProgram) (word : List Bool) : Fin (tapes p)→List Bool :=
  Fin.addCases (m:=p.tapeCount+1+27) (n:=1) (motive:=fun _=>List Bool)
    (AmplifierReplay.Dock.input (p.inputTapes word)) (fun _=>[])
def budget {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d) (request : AmplifierRequest) :=
  2*AmplifierReplay.Dock.budget
    (2^(amplifier.constructionExponent*max 1 request.inputArity))
    (amplifier.output request.inputArity request.function).arity
    (boolFunctionTable (amplifier.output request.inputArity request.function).function)+2

theorem input_lookup (p : OrdinaryProgram) (word : List Bool) (i : Fin (tapes p)) :
    input p word i=if i.val=0 then frame word else [] := by
  have hp : 0<p.tapeCount+1+27 := by omega
  refine Fin.addCases (m:=p.tapeCount+1+27) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left]
    rw [OrdinaryAmplifierReplay.input_tapes]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem constructor_ready {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d) (request : AmplifierRequest) :
    ∃ out,ClockJoin.ReadyRun (machine amplifier.constructor.program) (budget amplifier request)
      (input amplifier.constructor.program (amplifierInput request)) out ∧
      out (output amplifier.constructor.program)=frame (amplifierOutput amplifier.toScheduleAmplifier request) := by
  obtain ⟨src,hsrc,srcValue⟩ := amplifier.constructor.realizes request
  obtain ⟨dock,hdock,dockValue,dockSteps⟩ := AmplifierReplay.Dock.dock_run
    amplifier.constructor.program.machine amplifier.constructor.program.outputTape
    (amplifier.constructor.program.inputTapes (amplifierInput request))
    (2^(amplifier.constructionExponent*max 1 request.inputArity))
    (amplifier.output request.inputArity request.function).arity
    (boolFunctionTable (amplifier.output request.inputArity request.function).function)
    (GeneratedAmplifier.table_length _) src hsrc srcValue
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run _ _ _ dock hdock
  have hb : 2*dock.steps+2≤budget amplifier request := by unfold budget; omega
  have hm:=run_moreFuel (machine amplifier.constructor.program) _
    (budget amplifier request-(2*dock.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r.final.tapes,⟨r,hm,rfl,rh,rs.le.trans hb⟩,?_⟩
  exact (rt (AmplifierReplay.Dock.output amplifier.constructor.program.tapeCount)).trans dockValue

end
end NearCubicWires.RepairSource.RecoveryCaseOneAmplifier
