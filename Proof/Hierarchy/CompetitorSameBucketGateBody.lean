import Proof.Hierarchy.CompetitorSameBucketGatePrepare
import Proof.Hierarchy.CompetitorSameBucketGateExecute

/-! One actual streamed gate body: paid native packet load, coefficient
load, all bounded bucket pairs, and local packet return. Global input/output
cursors remain live for the actual enclosing Gates repetition. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketGateLoad (cfg heads tapes)
open CompetitorSameBucketGatePrepare (bits updated)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine CompetitorSameBucketGateLoad.machine CompetitorSameBucketGateExecute.machine
noncomputable def budget (r : Request) (cap : ℕ) (gate : Fin r.Gates) :=
  CompetitorSameBucketGatePrepare.budget r cap gate+1+CompetitorSameBucketGate.budget r cap

theorem coefficient_fits (r : Request) (cap : ℕ) (coefficient : ℤ) (cached : Option KeyLoop.Record)
    (right out : List Bool) (ambient : Fin 41 → List Bool) (h : State r cap coefficient cached right out ambient)
    (hp : 2*(r.p+1)+1≤cap) : (ambient 31).length≤cap := by
  have hf : ambient 31=ZeroPadding.pad cap (frame (MatrixScoreBatch.signMagnitude r.p coefficient)) := h.fields 3
  rw [hf,ZeroPadding.pad_length]
  have hl : (frame (MatrixScoreBatch.signMagnitude r.p coefficient)).length=2*(r.p+1)+1 := by simp
  rw [hl]
  exact max_le (Nat.le_refl _) hp

theorem body_run (r : Request) (cap : ℕ) (before : ℤ) (gate : Fin r.Gates) (cached : Option KeyLoop.Record)
    (right out : List Bool) (ambient : Fin 41 → List Bool)
    (rankPre rankSuffix coefficientPre coefficientSuffix packet rankLog coefficientLog : List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (packetFit : packet.length≤MatrixScoreReusableRanks.D r) (rankFit : rankLog.length≤MatrixScoreReusableRanks.D r)
    (coefficientFit : coefficientLog.length≤cap)
    (hstate : State r cap before cached right out ambient) :
    ∃ actual next nextCached nextRight,runFrom machine (budget r cap gate)
      (cfg machine.start r cap rankPre.length coefficientPre.length out.length ambient packet
        (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
        (coefficientPre++frame (bits r gate)++coefficientSuffix) rankLog coefficientLog)=some actual ∧
      actual.final.heads=heads (rankPre.length+(MatrixScoreRawRanks.output r gate).length)
        (coefficientPre.length+(frame (bits r gate)).length)
        (out++CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r gate) gate).length ∧
      actual.final.tapes=tapes r cap next (CompetitorSameBucketGateScan.source r gate)
        (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix)
        (coefficientPre++frame (bits r gate)++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false) ∧
      State r cap (MatrixScoreBatch.weight r gate) nextCached nextRight
        (out++CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r gate) gate) next ∧
      (next 39).length≤MatrixScoreReusableRanks.D r ∧ actual.steps≤budget r cap gate := by
  have hsize : 2*(bits r gate).length+1≤cap := by simpa [bits] using hp
  obtain ⟨prepared,hr,ph,pt,ps⟩:=CompetitorSameBucketGatePrepare.prepare_run r cap out.length gate ambient
    rankPre rankSuffix coefficientPre coefficientSuffix packet rankLog coefficientLog packetFit rankFit
    hstate.store.driver hstate.store.reset (coefficient_fits r cap before cached right out ambient hstate hp) coefficientFit hsize
  have nextState : State r cap (MatrixScoreBatch.weight r gate) cached right out (updated r cap gate ambient) :=
    CompetitorSameBucketGateExecute.coefficient_state r cap before (MatrixScoreBatch.weight r gate) cached right out ambient hstate
  have nextFit : ((updated r cap gate ambient) 39).length≤MatrixScoreReusableRanks.D r := by
    unfold updated
    rw [Function.update_of_ne (by decide : (39 : Fin 41)≠31)]
    exact targetFit
  obtain ⟨finished,next,nextCached,nextRight,hf,fh,ft,hs,hfit,fs⟩:=CompetitorSameBucketGateExecute.execute_run r cap
    (rankPre.length+(MatrixScoreRawRanks.output r gate).length) (coefficientPre.length+(frame (bits r gate)).length)
    (MatrixScoreBatch.weight r gate) gate cached right out (updated r cap gate ambient)
    (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix) (coefficientPre++frame (bits r gate)++coefficientSuffix)
    (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false) hc hp nextFit nextState
  have hi : Composition.restart prepared.final CompetitorSameBucketGateExecute.machine.start=
      cfg CompetitorSameBucketGateExecute.machine.start r cap
        (rankPre.length+(MatrixScoreRawRanks.output r gate).length) (coefficientPre.length+(frame (bits r gate)).length)
        out.length (updated r cap gate ambient) (CompetitorSameBucketGateScan.source r gate)
        (rankPre++MatrixScoreRawRanks.output r gate++rankSuffix) (coefficientPre++frame (bits r gate)++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false) := configuration_ext rfl ph pt
  rw [←hi] at hf
  have joined:=Composition.run_join CompetitorSameBucketGateLoad.machine CompetitorSameBucketGateExecute.machine
    _ _ _ prepared finished hr hf
  exact ⟨Composition.joinedReceipt prepared finished,next,nextCached,nextRight,joined,fh,ft,hs,hfit,
    by change prepared.steps+1+finished.steps≤budget r cap gate; unfold budget; omega⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateBody
