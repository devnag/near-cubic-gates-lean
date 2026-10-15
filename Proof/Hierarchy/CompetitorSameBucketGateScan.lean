import Proof.Hierarchy.CompetitorSameBucketPacketRows

/-! The actual native ranked gate packet supplies every bucket and every
bounded record. Only retained scalar fields are inputs at this local gate
boundary; no bucket contents, IDs or ranks are installed for free. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateScan
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketPacketRows (rows)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos outPos : ℕ) : Fin 51 → ℕ := Fin.addCases (m := 50) (n := 1) (motive := fun _ => ℕ)
  (CompetitorSameBucketBucketPrepare.heads pos outPos) (fun _ => 1)
noncomputable def source (r : Request) (gate : Fin r.Gates) := ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixScoreRawRanks.output r gate)
noncomputable def fields (r : Request) (cap : ℕ) (gate : Fin r.Gates) (ambient : Fin 41 → List Bool) : Fin 51 → List Bool :=
  Fin.addCases (m := 50) (n := 1) (motive := fun _ => List Bool)
    (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
      (r.bucketSize+1) 0 0 ambient (source r gate) (List.replicate (MatrixScoreReusableRanks.D r) false)).tapes
    (fun _ => UnaryTemplate.tape r.Buckets)
noncomputable def cfg {s : ℕ} (q : Fin s) (r : Request) (cap : ℕ) (gate : Fin r.Gates) (pos outPos : ℕ)
    (ambient : Fin 41 → List Bool) : Configuration 51 s := ⟨q,heads pos outPos,fields r cap gate ambient⟩
def capacities (n : ℕ) : Fin 51 → ℕ := fun i => if i=50 then n+2 else 0
noncomputable def machine := CompetitorSameBucketBucketLoop.machine
def budget (r : Request) (cap : ℕ) := CompetitorSameBucketBucketLoop.budget r (MatrixScoreReusableRanks.D r) cap (r.bucketSize+1) r.Buckets
noncomputable def output (r : Request) (coefficient : ℤ) (gate : Fin r.Gates) := CompetitorSameBucketBucketLoop.emissions r coefficient (rows r gate)
def distance (r : Request) := CompetitorSameBucketPackets.count r*CompetitorSameBucketPackets.width r

theorem source_eq (r : Request) (gate : Fin r.Gates) :
    source r gate=CompetitorSameBucketBucketLoop.packet r (rows r gate)++
      List.replicate (MatrixScoreReusableRanks.D r-(CompetitorSameBucketBucketLoop.packet r (rows r gate)).length) false := by
  unfold source
  rw [CompetitorSameBucketPackets.actual_padding]
  rw [CompetitorSameBucketPacketRows.packet_eq]
  rfl
theorem packet_length (r : Request) (gate : Fin r.Gates) :
    (CompetitorSameBucketBucketLoop.packet r (rows r gate)).length=distance r := by
  rw [CompetitorSameBucketPacketRows.packet_eq,CompetitorSameBucketCandidate.words_length,CompetitorSameBucketPackets.records_length]
  rfl

theorem padded_heads (phase : Fin 5) (r : Request) (cap pos outPos : ℕ) (gate : Fin r.Gates) (ambient : Fin 41 → List Bool) :
    (ZeroPadding.config (capacities r.Buckets) (RepeatMachine.cfg phase
      (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
        (r.bucketSize+1) pos outPos ambient (source r gate) (List.replicate (MatrixScoreReusableRanks.D r) false)) r.Buckets 1)).heads=heads pos outPos := by
  funext i; fin_cases i <;> rfl
theorem padded_tapes (phase : Fin 5) (r : Request) (cap pos outPos : ℕ) (gate : Fin r.Gates) (ambient : Fin 41 → List Bool) :
    (ZeroPadding.config (capacities r.Buckets) (RepeatMachine.cfg phase
      (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
        (r.bucketSize+1) pos outPos ambient (source r gate) (List.replicate (MatrixScoreReusableRanks.D r) false)) r.Buckets 1)).tapes=fields r cap gate ambient := by
  funext i
  fin_cases i <;> simp [ZeroPadding.config,capacities,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    CompetitorSameBucketBucketBody.cfg,CompetitorSameBucketBucketPrepare.cfg,fields,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem scan_run (r : Request) (cap : ℕ) (coefficient : ℤ) (gate : Fin r.Gates) (old : Option KeyLoop.Record)
    (oldRight out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (hstate : State r cap coefficient old oldRight out ambient) :
    ∃ actual next cached rightData,runFrom machine (budget r cap) (cfg machine.start r cap gate 0 out.length ambient)=some actual ∧
      actual.steps≤budget r cap ∧ actual.final.heads=heads (distance r) (out++output r coefficient gate).length ∧
      actual.final.tapes=fields r cap gate next ∧
      State r cap coefficient cached rightData (out++output r coefficient gate) next ∧ (next 39).length≤MatrixScoreReusableRanks.D r := by
  obtain ⟨base,next,cached,rightData,hb,bs,bf,bo,fit⟩ := CompetitorSameBucketBucketLoop.loop_run r (MatrixScoreReusableRanks.D r) cap
    (r.bucketSize+1) coefficient old (rows r gate) []
    (List.replicate (MatrixScoreReusableRanks.D r-(CompetitorSameBucketBucketLoop.packet r (rows r gate)).length) false)
    oldRight out ambient hc hp (CompetitorSameBucketPacketRows.rows_size r gate) (CompetitorSameBucketPacketRows.rows_fit r gate)
    (CompetitorSameBucketBucketBody.native_bucket_copy_fit r) targetFit hstate
  simp only [List.length_nil,List.nil_append,Nat.zero_add,CompetitorSameBucketPacketRows.rows_length,←source_eq] at hb bs bf
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (capacities r.Buckets) _ _ base hb
  have hi : ZeroPadding.config (capacities r.Buckets) (RepeatMachine.cfg 0
      (CompetitorSameBucketBucketBody.cfg CompetitorSameBucketBucketBody.machine.start (MatrixScoreReusableRanks.D r) cap (H r)
        (r.bucketSize+1) 0 out.length ambient (source r gate) (List.replicate (MatrixScoreReusableRanks.D r) false)) r.Buckets 1)=
      cfg machine.start r cap gate 0 out.length ambient :=
    configuration_ext rfl (padded_heads 0 r cap 0 out.length gate ambient) (padded_tapes 0 r cap 0 out.length gate ambient)
  rw [hi] at ha
  refine ⟨actual,next,cached,rightData,ha,hs.trans_le bs,?_,?_,bo,fit⟩
  · rw [hf,bf]
    rw [packet_length]
    exact padded_heads 3 r cap (distance r) _ gate next
  · rw [hf,bf]
    exact padded_tapes 3 r cap _ _ gate next

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateScan
