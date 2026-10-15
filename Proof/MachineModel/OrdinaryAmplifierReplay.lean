import Proof.MachineModel.OrdinaryAmplifierReplayBounds
import Proof.MachineModel.OrdinaryOracleComposeGraph
import Proof.Foundations.RecoverySourceContracts

/-! Literal selected-amplifier replay in the ordinary oracle interface.
The imported ordinary constructor is actually executed; the raw schema is
physically framed using its produced arity and complete table. -/
namespace NearCubicWires.RepairSource.OrdinaryAmplifierReplay
open LocalBitMultitape RepairOrdinary RepairOrdinary.AmplifierReplay ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def ports (p : OrdinaryProgram) : OrdinaryOracleCompose.Ports (p.tapeCount+1+27) where
  twoTapes := by omega
  outputTape := Dock.output p.tapeCount
  outputFresh := by change p.tapeCount+1+26≠0; omega
  queryTape := Dock.output p.tapeCount
  queryFresh := by change p.tapeCount+1+26≠0; omega

def program (p : OrdinaryProgram) : OrdinaryOracleProgram :=
  (ports p).program (OrdinaryOracleCompose.ordinary (Dock.machine p.machine p.outputTape))

theorem input_tapes (p : OrdinaryProgram) (word : List Bool) :
    Dock.input (p.inputTapes word)=(program p).base.inputTapes word := by
  have ht : 0<p.tapeCount := lt_of_lt_of_le (by decide : 0<2) p.twoTapes
  funext i
  change Dock.input (p.inputTapes word) i=(if i.val=0 then RepairOrdinary.frame word else [])
  refine Fin.addCases (m:=p.tapeCount+1) (n:=27) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=p.tapeCount) (n:=1) (fun j => ?_) (fun j => ?_) j
    · simp only [Dock.input,Fin.addCases_left,Program.inputTapes,Fin.val_castAdd]
      rfl
    · simp only [Dock.input,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
      rw [if_neg (by omega)]
  · simp only [Dock.input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem runs (oracle : ℕ→Bool) (p : OrdinaryProgram) (word : List Bool)
    (b n : ℕ) (table : List Bool) (hlen : table.length=2^n)
    (source : ExecutionReceipt p.tapeCount p.stateCount)
    (hr : run p.machine b (p.inputTapes word)=some source)
    (hout : source.final.tapes p.outputTape=RepairOrdinary.frame n.bits++table) :
    OrdinaryOracleRuns oracle (program p) word (RepairOrdinary.frame n.bits++table)
      (1024*(b+word.length+(RepairOrdinary.frame n.bits++table).length+1)^2) := by
  obtain ⟨r,hrun,houtput,hsteps⟩ := Dock.dock_run p.machine p.outputTape (p.inputTapes word)
    b n table hlen source hr hout
  rw [input_tapes p word] at hrun
  refine ⟨r.steps,r.final,hsteps.trans (budget_bound b word.length n table hlen),?_,?_,houtput⟩
  · exact OrdinaryOracleCompose.ordinary_trace (ports p)
      (Dock.machine p.machine p.outputTape) _ _ r hrun
  · exact (RepairOrdinary.prefix_of_run _ _ _ r hrun).2

def coefficient : ℕ := 1024
def degree : ℕ := 2
theorem coefficient_positive : 1 ≤ coefficient := by decide
theorem degree_positive : 1 ≤ degree := by decide

def budget {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (request : AmplifierRequest) :=
  coefficient*(2^(amplifier.constructionExponent*max 1 request.inputArity)+
    (amplifierInput request).length+(amplifierOutput amplifier.toScheduleAmplifier request).length+1)^degree

def replay {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) :
    OrdinaryOracleWordFunction RecoveryOracle.correctedSat AmplifierRequest amplifierInput
      (amplifierOutput amplifier.toScheduleAmplifier) (budget amplifier) where
  program := program amplifier.constructor.program
  realizes := by
    intro request
    obtain ⟨source,hr,hout⟩ := amplifier.constructor.realizes request
    exact runs RecoveryOracle.correctedSat amplifier.constructor.program (amplifierInput request)
      (2^(amplifier.constructionExponent*max 1 request.inputArity))
      (amplifier.output request.inputArity request.function).arity
      (ExecutableInterfaces.boolFunctionTable (amplifier.output request.inputArity request.function).function)
      (GeneratedAmplifier.table_length _) source hr hout

end
end NearCubicWires.RepairSource.OrdinaryAmplifierReplay
