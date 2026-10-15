import Proof.CaseAnalysis.WitnessAliases
import Proof.Assembly.SelectedRecoveryIntegration
import Proof.Amplification.RecoveryCaseOneRequest

/-! The paper's single canonical language, fixed before either class is
considered. Its semantic definition is total; the physical schedule and
all-length ordinary certificate remain separate producer obligations. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary OuterPCPRecovery
open RecoveryPipeline RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def paddedUnsigned {q : Nat} {c : BooleanCircuit q} (pcpp : PointwisePCPP c)
    {r : Nat} (hclause : pcpp.clauseBits≤r) : BoolFunction (q+r+1) :=
  fun address=>CloseoutWitness.unsignedHonest pcpp (projectPaddedOccurrenceInput hclause address)

def core {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target : Nat) : BoolFunction target := by
  classical
  exact if hsmall : RecoveryChoice.SmallOracle pcp d input then
    let oracle:=(RecoveryChoice.oracleSelector pcp d input hsmall).circuit
    let request:=PCPPSubstitution.sourceRequest a oracle (pcp.queryAddressBits input)
      (pcp.decision input (fun _=>false))
    let pcpp:=a.output request
    if hc : pcpp.clauseBits≤clauseBits then
      if ht : copies*(request.arity+clauseBits+1)≤target then
        padCore (xorPower (paddedUnsigned pcpp hc) copies) ht
      else fun _=>false
    else fun _=>false
  else
    let request:=RecoveryCaseOneRequest.request pcp input
    let generated:=amplifier.output request.inputArity request.function
    if ht : generated.arity≤target then padCore generated.function ht
    else fun _=>false

theorem core_case_one {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target : Nat) (hsmall : ¬RecoveryChoice.SmallOracle pcp d input)
    (hfit : (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
      (RecoveryCaseOneRequest.request pcp input).function).arity≤target) :
    core pcp a amplifier input copies clauseBits target=
      padCore (amplifier.output (RecoveryCaseOneRequest.request pcp input).inputArity
        (RecoveryCaseOneRequest.request pcp input).function).function hfit := by
  simp only [core,dif_neg hsmall,dif_pos hfit]

/-- Exact integer form of ceil(d_G log_2(q+2)), with fixed d_G. -/
def clauseWidth (degree q : Nat) := Nat.clog 2 ((q+2)^degree)
def coreWidth (copies degree q : Nat) := copies*(q+clauseWidth degree q+1)

/-- Enumerate s=1,...,n; zero denotes the empty finite-search result. -/
def selectedIndex (width : Nat→Nat) (n : Nat) :=
  Nat.findGreatest (fun s=>1 ≤ s ∧ width s≤n/2) n

theorem selectedIndex_le (width : Nat→Nat) (n : Nat) : selectedIndex width n ≤ n :=
  Nat.findGreatest_le _

theorem selectedIndex_fits (width : Nat→Nat) (n : Nat)
    (h : selectedIndex width n≠0) :
    1 ≤ selectedIndex width n ∧ width (selectedIndex width n)≤n/2 :=
  Nat.findGreatest_of_ne_zero rfl h

def selectedPCPP (sources : EightSources) : PointwisePCPPAlgorithm :=
  Classical.choice sources.pcp.proximity

def widthAt (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (copies clauseDegree s : Nat) :=
  coreWidth copies clauseDegree ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth (2^s))

/-- Both branches use the same source length, refuter output, source PCP and
canonical selectors. Direct padding to n reads the same prefix as padding
first to m_s and then to n; the m_s arity envelope remains a required bound. -/
def language (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (machine : OrdinaryWeakMachine) (degree copies clauseDegree sourceOnset : Nat) : Language :=
  fun n address=>
    let s:=selectedIndex (widthAt sources k clock copies clauseDegree) n
    if 1 ≤ s ∧ sourceOnset ≤ 2^s then
      core (SelectedRecoveryIntegration.outer sources k clock).result.pcp (selectedPCPP sources)
        (selectedAmplifier sources.amplification degree)
        ((sources.hierarchy (fun n=>n^(k+2)) clock).output machine (2^s)) copies
        (clauseWidth clauseDegree ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth (2^s)))
        n address
    else false

theorem language_zero (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (machine : OrdinaryWeakMachine) (degree copies clauseDegree sourceOnset : Nat) (address : BitInput 0) :
    language sources k clock machine degree copies clauseDegree sourceOnset 0 address=false := by
  simp [language,selectedIndex]

end
end NearCubicWires.RepairSource.CloseoutLanguage
