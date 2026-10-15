import Proof.Hierarchy.CompetitorSameBucketGateLoad

/-! Both actual gate inputs are loaded consecutively from their original
streams, before executing the whole bucket pass. Both global cursors advance. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGatePrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketGateLoad (cfg heads tapes packetBudget coefficientBudget)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bits (r : Request) (gate : Fin r.Gates) := MatrixScoreBatch.signMagnitude r.p (MatrixScoreBatch.weight r gate)
noncomputable def updated (r : Request) (cap : ℕ) (gate : Fin r.Gates) (ambient : Fin 41 → List Bool) :=
  Function.update ambient 31 (ZeroPadding.pad cap (frame (bits r gate)))
noncomputable def budget (r : Request) (cap : ℕ) (gate : Fin r.Gates) :=
  packetBudget r gate+1+coefficientBudget cap (bits r gate)

theorem prepare_run (r : Request) (cap outPos : ℕ) (gate : Fin r.Gates) (ambient : Fin 41 → List Bool)
    (rankPre rankSuffix coefficientPre coefficientSuffix packet rankLog coefficientLog : List Bool)
    (hp : packet.length≤MatrixScoreReusableRanks.D r) (hr : rankLog.length≤MatrixScoreReusableRanks.D r)
    (driver : ambient 36=List.replicate cap true) (reset : ambient 37=List.replicate (cap+1) false)
    (hc : (ambient 31).length≤cap) (hl : coefficientLog.length≤cap) (hsize : 2*(bits r gate).length+1≤cap) :
    ∃ actual,runFrom CompetitorSameBucketGateLoad.machine (budget r cap gate)
      (cfg CompetitorSameBucketGateLoad.machine.start r cap rankPre.length coefficientPre.length outPos ambient packet
        (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
        (coefficientPre++frame (bits r gate)++coefficientSuffix) rankLog coefficientLog)=some actual ∧
      actual.final.heads=heads (rankPre.length+(MatrixScoreRawRanks.output r gate).length)
        (coefficientPre.length+(frame (bits r gate)).length) outPos ∧
      actual.final.tapes=tapes r cap (updated r cap gate ambient) (CompetitorSameBucketGateScan.source r gate)
        (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
        (coefficientPre++frame (bits r gate)++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false) ∧
      actual.steps≤budget r cap gate := by
  obtain ⟨first,hfirst,fh,ft,fs⟩:=CompetitorSameBucketGateLoad.packet_run r cap coefficientPre.length outPos gate ambient
    rankPre rankSuffix packet (coefficientPre++frame (bits r gate)++coefficientSuffix) rankLog coefficientLog hp hr
  obtain ⟨last,hlast,lh,lt,ls⟩:=CompetitorSameBucketGateLoad.coefficient_run r cap
    (rankPre.length+(MatrixScoreRawRanks.output r gate).length) outPos ambient (bits r gate) coefficientPre coefficientSuffix
    (CompetitorSameBucketGateScan.source r gate) (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
    (List.replicate (MatrixScoreReusableRanks.D r) false) coefficientLog driver reset hc hl hsize
  have hi : Composition.restart first.final CompetitorSameBucketGateLoad.last.start=
      cfg CompetitorSameBucketGateLoad.last.start r cap
        (rankPre.length+(MatrixScoreRawRanks.output r gate).length) coefficientPre.length outPos ambient
        (CompetitorSameBucketGateScan.source r gate) (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
        (coefficientPre++frame (bits r gate)++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) coefficientLog := configuration_ext rfl fh ft
  rw [←hi] at hlast
  have joined:=Composition.run_join CompetitorSameBucketGateLoad.first CompetitorSameBucketGateLoad.last
    _ _ _ first last hfirst hlast
  exact ⟨Composition.joinedReceipt first last,joined,lh,lt,
    by change first.steps+1+last.steps≤budget r cap gate; unfold budget; omega⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGatePrepare
