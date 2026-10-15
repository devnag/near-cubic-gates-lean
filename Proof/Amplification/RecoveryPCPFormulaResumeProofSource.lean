import Proof.Amplification.RecoveryPCPFormulaResumeProofInput
import Proof.Amplification.RecoveryPCPFormulaResumeProofMeaning

/-! Execute the same hierarchy source/stream prefix and pay its return scan.
The five retained original fields are now available together at zero heads. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofSource
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def tapes (k : Nat) := HierarchyStreams.tapes source k+1
def port (k : Nat) (i : Fin 5) : Fin (tapes source k) :=
  (RecoveryPCPFormulaResumeHierarchy.port source k i).castAdd 1
def machine (k CH Cpad : Nat) (code : List Bool) :=
  Rewind.machine (HierarchyStreams.machine source k CH Cpad code)
def budget (k CH Cpad : Nat) (code x : List Bool) := 2*HierarchyStreams.budget source k CH Cpad code x+2

private theorem extend_input {t : Nat} (ht : 0<t) (word : List Bool) :
    (Fin.addCases (m:=t) (n:=1) (motive:=fun _=>List Bool) (SourceHandoff.sourceTapes word) (fun _=>[]))=
      SourceHandoff.sourceTapes word := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) (fun i=>?_) (fun i=>?_) i
  · rw [Fin.addCases_left]
    rfl
  · rw [Fin.addCases_right]
    simp only [SourceHandoff.sourceTapes,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem source_ready (k CH Cpad : Nat) (code x bound : List Bool) (hpad : k+3≤Cpad) : ∃ out,
    ClockJoin.ReadyRun (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (SourceHandoff.sourceTapes (frame x++frame bound)) out ∧
      out (port source k 0)=frame (HierarchyStreams.R source k CH Cpad code x).bits ∧
      out (port source k 1)=frame (HierarchyStreams.Q source k CH Cpad code x).bits ∧
      out (port source k 2)=QueryBytes.framedCodes
        (normalizedRows (source.output (HierarchyStreams.request k CH Cpad code x))
          (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)).flatten ∧
      out (port source k 3)=DedupBytes.fields (source.output (HierarchyStreams.request k CH Cpad code x)) ∧
      out (port source k 4)=CompareMachine.word
        (Codec.clauses (source.output (HierarchyStreams.request k CH Cpad code x))).length := by
  obtain ⟨prior,hprior,priorSteps,hf⟩ := HierarchyStreams.scalar_run source k CH Cpad code x bound hpad
  obtain ⟨r,hr,rt,rh,rSteps,_rPeak⟩ := Rewind.reset_run (HierarchyStreams.machine source k CH Cpad code) _ _ prior hprior
  rw [extend_input (by omega)] at hr
  have hb : 2*prior.steps+2≤budget source k CH Cpad code x := by
    unfold budget
    omega
  have hm:=run_moreFuel (machine source k CH Cpad code) _
    (budget source k CH Cpad code x-(2*prior.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rSteps.trans_le hb⟩,
    (rt (HierarchyStreams.old source k (HierarchyStreams.bitsR source k))).trans hf.width,
    (rt (HierarchyStreams.old source k (HierarchyStreams.bitsQ source k))).trans hf.queries,
    (rt (HierarchyStreams.slots source k 29)).trans hf.queryStream,
    (rt (HierarchyStreams.slots source k 38)).trans hf.clauseStream,
    (rt (HierarchyStreams.slots source k 46)).trans hf.clauseCount⟩

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofSource
