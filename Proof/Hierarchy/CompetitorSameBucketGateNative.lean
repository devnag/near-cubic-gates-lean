import Proof.Hierarchy.CompetitorSameBucketGateLoop

/-! Canonical all-gate streams and the real sentinel from the header parser.
This is the exact prepared consumer of the cold rank/coefficient producer. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateNative
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixBatchBucketEndpoints (H)
open MatrixScoreBatch (Request)
open RepairSource.VerifierDecoding
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketGateLoop (machine budget ranks coefficients emissions)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def output (r : Request) := emissions r (List.finRange r.Gates)
def padding (r : Request) (i : Fin 56) := if i=55 then r.Gates+2 else 0
noncomputable def core (r : Request) (cap rankPos coefficientPos : ℕ) (out : List Bool)
    (ambient : Fin 41 → List Bool) (packet : List Bool) :=
  CompetitorSameBucketGateLoad.cfg CompetitorSameBucketGateBody.machine.start r cap rankPos coefficientPos out.length ambient packet
    (MatrixBatchGateNativeLoop.output r) (MatrixCoefficientLoop.output r.p r.cuts)
    (List.replicate (MatrixScoreReusableRanks.D r) false) (List.replicate cap false)
noncomputable def cfg (r : Request) (cap : ℕ) (phase : Fin 5) (rankPos coefficientPos : ℕ)
    (out : List Bool) (ambient : Fin 41 → List Bool) (packet : List Bool) :=
  ZeroPadding.config (padding r) (RepeatMachine.cfg phase (core r cap rankPos coefficientPos out ambient packet) r.Gates 1)

theorem all_ranks (r : Request) : ranks r (List.finRange r.Gates)=MatrixBatchGateNativeLoop.output r := rfl
theorem all_coefficients (r : Request) : coefficients r (List.finRange r.Gates)=MatrixCoefficientLoop.output r.p r.cuts := by
  have h := congrArg (List.flatMap (fun c : MatrixScoreBatch.Cut => frame (MatrixScoreBatch.signMagnitude r.p c.coefficient)))
    (List.map_get_finRange r.cuts)
  simpa only [coefficients,MatrixCoefficientLoop.output,CompetitorSameBucketGatePrepare.bits,
    MatrixScoreBatch.weight,Request.Gates,List.flatMap_map,Function.comp_def] using h

theorem cfg_heads (r : Request) (cap : ℕ) (phase : Fin 5) (rankPos coefficientPos : ℕ)
    (out : List Bool) (ambient : Fin 41 → List Bool) (packet : List Bool) :
    (cfg r cap phase rankPos coefficientPos out ambient packet).heads=
      Fin.addCases (m := 55) (n := 1) (motive := fun _ => ℕ)
        (CompetitorSameBucketGateLoad.heads rankPos coefficientPos out.length) (fun _ => 1) := rfl

theorem cfg_tapes (r : Request) (cap : ℕ) (phase : Fin 5) (rankPos coefficientPos : ℕ)
    (out : List Bool) (ambient : Fin 41 → List Bool) (packet : List Bool) :
    (cfg r cap phase rankPos coefficientPos out ambient packet).tapes=
      Fin.addCases (m := 55) (n := 1) (motive := fun _ => List Bool)
        (core r cap rankPos coefficientPos out ambient packet).tapes (fun _ => UnaryTemplate.tape r.Gates) := by
  funext i
  refine Fin.addCases (m := 55) (n := 1) (motive := fun j => (cfg r cap phase rankPos coefficientPos out ambient packet).tapes j=_) ?_ ?_ i
  · intro j
    have hj : (j.castAdd 1 : Fin 56)≠55 := by
      intro h; have hv:=congrArg Fin.val h; change j.val=55 at hv; omega
    simp only [cfg,ZeroPadding.config,padding,hj,ite_false,ZeroPadding.pad_zero,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
  · intro j
    fin_cases j
    change ZeroPadding.pad (r.Gates+2) (CompareMachine.word r.Gates)=UnaryTemplate.tape r.Gates
    simp [CompareMachine.word,ZeroPadding.pad,UnaryTemplate.tape]

theorem native_run (r : Request) (cap : ℕ) (before : ℤ) (cached : Option KeyLoop.Record)
    (right out : List Bool) (ambient : Fin 41 → List Bool) (packet : List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap)
    (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (packetFit : packet.length≤MatrixScoreReusableRanks.D r)
    (hstate : State r cap before cached right out ambient) :
    ∃ actual next nextCoefficient nextCached nextRight nextPacket,
      runFrom machine (budget r cap r.Gates) (cfg r cap 0 0 0 out ambient packet)=some actual ∧
      actual.steps≤budget r cap r.Gates ∧
      actual.final=cfg r cap 3 (MatrixBatchGateNativeLoop.output r).length (MatrixCoefficientLoop.output r.p r.cuts).length
        (out++output r) next nextPacket ∧
      State r cap nextCoefficient nextCached nextRight (out++output r) next ∧
      (next 39).length≤MatrixScoreReusableRanks.D r ∧ nextPacket.length≤MatrixScoreReusableRanks.D r := by
  obtain ⟨base,next,nextCoefficient,nextCached,nextRight,nextPacket,hb,bs,bf,st,nt,np⟩ :=
    CompetitorSameBucketGateLoop.driver_run r cap before cached right out ambient (List.finRange r.Gates)
      r.Gates 0 [] [] [] [] packet (by simp) hc hp targetFit packetFit hstate
  have hbudget : (List.finRange r.Gates).length*(CompetitorSameBucketGateBody.fuel r cap+2)+r.Gates+3=budget r cap r.Gates := by
    simp only [List.length_finRange,budget]
    ring
  simp only [all_ranks,all_coefficients,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,hbudget] at hb bs bf
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (padding r) _ _ base hb
  refine ⟨actual,next,nextCoefficient,nextCached,nextRight,nextPacket,ha,hs.trans_le bs,?_,st,nt,np⟩
  rw [hf,bf]
  rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateNative
