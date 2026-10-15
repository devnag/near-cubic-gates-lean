import Proof.Hierarchy.CompetitorSameBucketPacketReturn

/-! Complete supplied native-gate pass: all actual bucket work followed by
the paid local packet return using retained B/H/Buckets templates. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGate
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketGateScan (cfg fields heads output distance)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine CompetitorSameBucketGateScan.machine CompetitorSameBucketPacketReturn.machine
def budget (r : Request) (cap : ℕ) := CompetitorSameBucketGateScan.budget r cap+1+
  CompetitorSameBucketPacketReturn.budget (H r) (r.bucketSize+1) r.Buckets

theorem return_run (r : Request) (cap : ℕ) (gate : Fin r.Gates) (outPos : ℕ) (ambient : Fin 41 → List Bool) :
    ∃ actual,runFrom CompetitorSameBucketPacketReturn.machine
        (CompetitorSameBucketPacketReturn.budget (H r) (r.bucketSize+1) r.Buckets)
        (cfg CompetitorSameBucketPacketReturn.machine.start r cap gate (distance r) outPos ambient)=some actual ∧
      actual.steps≤CompetitorSameBucketPacketReturn.budget (H r) (r.bucketSize+1) r.Buckets ∧
      actual.final.heads=heads 0 outPos ∧ actual.final.tapes=fields r cap gate ambient := by
  let core := (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
    (r.bucketSize+1) 0 0 ambient (CompetitorSameBucketGateScan.source r gate) (List.replicate (MatrixScoreReusableRanks.D r) false)).tapes
  obtain ⟨actual,ha,ast,ah,atapes⟩ := CompetitorSameBucketPacketReturn.return_run (H r) (r.bucketSize+1) r.Buckets
    (distance r) outPos core rfl rfl
  have hi : CompetitorSameBucketPacketReturn.cfg CompetitorSameBucketPacketReturn.machine.start (distance r) outPos r.Buckets core=
      cfg CompetitorSameBucketPacketReturn.machine.start r cap gate (distance r) outPos ambient := rfl
  rw [hi] at ha
  have hd : distance r-r.Buckets*((r.bucketSize+1)*(4*H r+1))=0 := by
    unfold distance CompetitorSameBucketPackets.count CompetitorSameBucketPackets.width
    rw [Nat.mul_assoc,Nat.sub_self]
  rw [hd] at ah
  exact ⟨actual,ha,ast,ah,atapes⟩

theorem gate_run (r : Request) (cap : ℕ) (coefficient : ℤ) (gate : Fin r.Gates) (old : Option KeyLoop.Record)
    (oldRight out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (hstate : State r cap coefficient old oldRight out ambient) :
    ∃ actual next cached rightData,runFrom machine (budget r cap) (cfg machine.start r cap gate 0 out.length ambient)=some actual ∧
      actual.steps≤budget r cap ∧ actual.final.heads=heads 0 (out++output r coefficient gate).length ∧
      actual.final.tapes=fields r cap gate next ∧ State r cap coefficient cached rightData (out++output r coefficient gate) next ∧
      (next 39).length≤MatrixScoreReusableRanks.D r := by
  obtain ⟨scan,next,cached,rightData,hs,ss,sh,st,so,fit⟩ := CompetitorSameBucketGateScan.scan_run r cap coefficient gate old oldRight out ambient hc hp targetFit hstate
  obtain ⟨back,hb,bs,bh,bt⟩ := return_run r cap gate (out++output r coefficient gate).length next
  have hi : Composition.restart scan.final CompetitorSameBucketPacketReturn.machine.start=
      cfg CompetitorSameBucketPacketReturn.machine.start r cap gate (distance r) (out++output r coefficient gate).length next :=
    configuration_ext rfl sh st
  rw [←hi] at hb
  have hall := Composition.run_join CompetitorSameBucketGateScan.machine CompetitorSameBucketPacketReturn.machine _ _ _ scan back hs hb
  refine ⟨Composition.joinedReceipt scan back,next,cached,rightData,hall,?_,bh,bt,so,fit⟩
  change scan.steps+1+back.steps≤budget r cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGate
