import Proof.Packets.PacketsXWalkPoweredRun
import Proof.Packets.PacketsXWalkTranscriptList
import Proof.Packets.PhysicalRepeatStep

/-! One fixed ordinary machine consumes all powered transition words using
an actual unary count driver. No transition-execution premise is accepted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 18000
set_option warningAsError true
namespace Theorem25Completion.WalkTimeLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.RepairSource.VerifierDecoding
open FixedLivePackets.Materializer
noncomputable section

def vertex {r n : Nat} (sample : MargulisWalkSample (2^r) (n+1)) (i : Nat):=
  sample.vertex ⟨min i n,by omega⟩
def H (n i : Nat):=WalkLabelDispatch.heads (160*min i n)
def A {r n : Nat} (R L : Nat) (sample : MargulisWalkSample (2^r) (n+1)) (tail : List Bool) (i : Nat):=
  WalkLabelDispatch.bank r R L (vertex sample i)
    (WalkSampleWord.labelsWord (sampleTransitionLabels sample)++tail)
def machine:=RepeatMachine.machine WalkPoweredRun.machine (fun _ _=>true)
def budget (r R n : Nat):=n*(160*r+160*R+1163)+3

theorem vertex_succ {r n : Nat} (sample : MargulisWalkSample (2^r) (n+1)) (i : Nat) (hi : i<n) :
    vertex sample (i+1)=poweredMargulisNeighbor (sampleTransitionLabels sample ⟨i,hi⟩) (vertex sample i) := by
  simp only [vertex,Nat.min_eq_left (by omega : i+1≤n),Nat.min_eq_left (by omega : i≤n)]
  rw [MargulisWalkSample.vertex.eq_def]
  rfl

theorem iteration {r n : Nat} (R L : Nat) (sample : MargulisWalkSample (2^r) (n+1))
    (tail : List Bool) (i : Nat) (hi : i<n) (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step WalkPoweredRun.machine (160*r+160*R+1160) (H n i) (A R L sample tail i)
      (H n (i+1)) (A R L sample tail (i+1)) := by
  let labels:=sampleTransitionLabels sample
  have h:=WalkPoweredRun.run r R L (labels ⟨i,hi⟩) (vertex sample i)
    (WalkTranscriptList.prefixBits labels i) (WalkTranscriptList.suffix labels (i+1)++tail) hR hL
  rw [WalkTranscriptList.prefix_length,Nat.min_eq_left (by omega : i≤n)] at h
  have ht : WalkTranscriptList.prefixBits labels i++WalkPoweredWord.word (labels ⟨i,hi⟩)++
      (WalkTranscriptList.suffix labels (i+1)++tail)=WalkSampleWord.labelsWord labels++tail := by
    rw [WalkTranscriptList.split labels i hi]
    simp only [List.append_assoc]
  rw [ht] at h
  rw [←vertex_succ sample i hi] at h
  simpa only [H,A,Nat.min_eq_left (by omega : i≤n),Nat.min_eq_left (by omega : i+1≤n),
    Nat.mul_add,Nat.mul_one] using h

theorem run {r n : Nat} (R L : Nat) (sample : MargulisWalkSample (2^r) (n+1))
    (tail : List Bool) (hR : 2*r+1≤R) (hL : 2*r+1≤L) :
    Step machine (budget r R n)
      (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>Nat) (H n 0) (fun _=>1))
      (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) (A R L sample tail 0) (fun _=>CompareMachine.word n))
      (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>Nat) (H n n) (fun _=>1))
      (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) (A R L sample tail n) (fun _=>CompareMachine.word n)) := by
  exact PhysicalRepeatStep.run WalkPoweredRun.machine n (160*r+160*R+1160) (H n) (A R L sample tail)
    (fun i hi=>iteration R L sample tail i hi hR hL)

end
end Theorem25Completion.WalkTimeLoop
