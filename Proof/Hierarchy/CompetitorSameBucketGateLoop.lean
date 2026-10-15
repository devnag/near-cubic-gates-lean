import Proof.Hierarchy.CompetitorSameBucketGateBodyBounds

/-! The physical Gates sentinel drives all streamed gate packets and their
coefficients. Global source and contribution cursors advance throughout;
only the bounded local packet is returned after each gate. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketGateLoad (cfg)
open CompetitorSameBucketGateBody (fuel)
open private cfg_eq from Proof.PCP.VerifierDecodingRepeat
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ranks (r : Request) (gates : List (Fin r.Gates)) := gates.flatMap (MatrixScoreRawRanks.output r)
noncomputable def coefficients (r : Request) (gates : List (Fin r.Gates)) :=
  gates.flatMap (fun g => frame (CompetitorSameBucketGatePrepare.bits r g))
noncomputable def emissions (r : Request) (gates : List (Fin r.Gates)) :=
  gates.flatMap (fun g => CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r g) g)
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 55 → Bool) := true
noncomputable def machine := RepeatMachine.machine CompetitorSameBucketGateBody.machine accepted
noncomputable def budget (r : Request) (cap n : ℕ) := n*(fuel r cap+3)+3

theorem driver_run (r : Request) (cap : ℕ) (before : ℤ) (cached : Option KeyLoop.Record)
    (right out : List Bool) (ambient : Fin 41 → List Bool) (gates : List (Fin r.Gates))
    (total pos : ℕ) (rankPre rankSuffix coefficientPre coefficientSuffix packet : List Bool)
    (hpos : pos+gates.length=total) (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (packetFit : packet.length≤MatrixScoreReusableRanks.D r)
    (hstate : State r cap before cached right out ambient) :
    ∃ actual next nextCoefficient nextCached nextRight nextPacket,
      runFrom machine (gates.length*(fuel r cap+2)+total+3)
        (RepeatMachine.cfg 0 (cfg CompetitorSameBucketGateBody.machine.start r cap
          rankPre.length coefficientPre.length out.length ambient packet
          (rankPre++ranks r gates++rankSuffix) (coefficientPre++coefficients r gates++coefficientSuffix)
          (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total (pos+1))=some actual ∧
      actual.steps≤gates.length*(fuel r cap+2)+total+3 ∧
      actual.final=RepeatMachine.cfg 3 (cfg CompetitorSameBucketGateBody.machine.start r cap
        (rankPre.length+(ranks r gates).length) (coefficientPre.length+(coefficients r gates).length)
        (out++emissions r gates).length next nextPacket
        (rankPre++ranks r gates++rankSuffix) (coefficientPre++coefficients r gates++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total 1 ∧
      State r cap nextCoefficient nextCached nextRight (out++emissions r gates) next ∧
      (next 39).length≤MatrixScoreReusableRanks.D r ∧ nextPacket.length≤MatrixScoreReusableRanks.D r := by
  induction gates generalizing before cached right out ambient pos rankPre coefficientPre packet with
  | nil =>
    have he : pos=total := by simpa using hpos
    subst pos
    obtain ⟨actual,ha,af,ast⟩ := (RepeatMachine.exhaust CompetitorSameBucketGateBody.machine accepted
      (cfg CompetitorSameBucketGateBody.machine.start r cap rankPre.length coefficientPre.length out.length ambient packet
        (rankPre++ranks r []++rankSuffix) (coefficientPre++coefficients r []++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨actual,ambient,before,cached,right,packet,by simpa [machine] using ha,by simpa using ast.le,
      by simpa [ranks,coefficients,emissions] using af,by simpa [emissions] using hstate,targetFit,packetFit⟩
  | cons gate gates ih =>
    obtain ⟨one,mid,midCached,midRight,hone,oh,ot,ostate,ofit,os⟩ := CompetitorSameBucketGateBody.body_run r cap before gate cached
      right out ambient rankPre (ranks r gates++rankSuffix) coefficientPre (coefficients r gates++coefficientSuffix) packet
      (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)
      hc hp targetFit packetFit (by simp) (by simp) hstate
    have hb := CompetitorSameBucketGateBody.budget_le r cap gate
    have honeFuel := runFrom_moreFuel CompetitorSameBucketGateBody.machine _ (fuel r cap-CompetitorSameBucketGateBody.budget r cap gate)
      _ one hone
    rw [Nat.add_sub_of_le hb] at honeFuel
    have hone' : runFrom CompetitorSameBucketGateBody.machine (fuel r cap)
        (cfg CompetitorSameBucketGateBody.machine.start r cap rankPre.length coefficientPre.length out.length ambient packet
          (rankPre++ranks r (gate::gates)++rankSuffix) (coefficientPre++coefficients r (gate::gates)++coefficientSuffix)
          (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false))=some one := by
      simpa only [ranks,coefficients,List.flatMap_cons,List.append_assoc] using honeFuel
    have iteration := RepeatMachine.iteration CompetitorSameBucketGateBody.machine accepted
      (cfg CompetitorSameBucketGateBody.machine.start r cap rankPre.length coefficientPre.length out.length ambient packet
        (rankPre++ranks r (gate::gates)++rankSuffix) (coefficientPre++coefficients r (gate::gates)++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total pos one rfl
      (by simp only [List.length_cons] at hpos; omega) hone'
    simp only [accepted,if_true] at iteration
    have hend := cfg_eq 0 one.final
      (cfg CompetitorSameBucketGateBody.machine.start r cap
        (rankPre++MatrixScoreRawRanks.output r gate).length
        (coefficientPre++frame (CompetitorSameBucketGatePrepare.bits r gate)).length
        (out++CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r gate) gate).length mid
        (CompetitorSameBucketGateScan.source r gate)
        ((rankPre++MatrixScoreRawRanks.output r gate)++ranks r gates++rankSuffix)
        ((coefficientPre++frame (CompetitorSameBucketGatePrepare.bits r gate))++coefficients r gates++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total (pos+2)
      (by simpa only [cfg,List.length_append] using oh)
      (by simpa only [cfg,List.append_assoc] using ot)
    rw [hend] at iteration
    obtain ⟨tail,next,nextCoefficient,nextCached,nextRight,nextPacket,htail,ts,tf,tailState,tailFit,nextFit⟩ :=
      ih (before := MatrixScoreBatch.weight r gate) (cached := midCached) (right := midRight)
        (out := out++CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r gate) gate)
        (ambient := mid) (pos := pos+1) (rankPre := rankPre++MatrixScoreRawRanks.output r gate)
        (coefficientPre := coefficientPre++frame (CompetitorSameBucketGatePrepare.bits r gate))
        (packet := CompetitorSameBucketGateScan.source r gate)
        (by simp only [List.length_cons] at hpos; omega) ofit (CompetitorSameBucketGateBody.source_fits r gate) ostate
    have ht : runFrom machine (gates.length*(fuel r cap+2)+total+3)
      (RepeatMachine.cfg 0 (cfg CompetitorSameBucketGateBody.machine.start r cap
        (rankPre++MatrixScoreRawRanks.output r gate).length
        (coefficientPre++frame (CompetitorSameBucketGatePrepare.bits r gate)).length
        (out++CompetitorSameBucketGateScan.output r (MatrixScoreBatch.weight r gate) gate).length mid
        (CompetitorSameBucketGateScan.source r gate)
        ((rankPre++MatrixScoreRawRanks.output r gate)++ranks r gates++rankSuffix)
        ((coefficientPre++frame (CompetitorSameBucketGatePrepare.bits r gate))++coefficients r gates++coefficientSuffix)
        (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,path⟩
    obtain ⟨actual,ha,af,ast,_⟩ := path.followedBy tail ht
    have bound : (one.steps+2)+(gates.length*(fuel r cap+2)+total+3)≤
        (gate::gates).length*(fuel r cap+2)+total+3 := by
      simp only [List.length_cons]; nlinarith
    have more := runFrom_moreFuel machine _
      ((gate::gates).length*(fuel r cap+2)+total+3-
        ((one.steps+2)+(gates.length*(fuel r cap+2)+total+3))) _ actual ha
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨actual,next,nextCoefficient,nextCached,nextRight,nextPacket,more,?_,?_,?_,tailFit,nextFit⟩
    · rw [ast]
      simp only [List.length_cons]
      nlinarith
    · rw [af,tf]
      simp only [ranks,coefficients,emissions,List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc]
    · simpa only [emissions,List.flatMap_cons,List.append_assoc] using tailState

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateLoop
