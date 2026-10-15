import Proof.Hierarchy.CompetitorSameBucketGateLoad

/-! The whole native gate pass preserves the four global load fields.
The physical coefficient overwrite transports the exact reusable state. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGateExecute
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketCandidate (State)
open CompetitorSameBucketGateLoad (cfg heads tapes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem coefficient_state (r : Request) (cap : ℕ) (before after : ℤ) (cached : Option KeyLoop.Record)
    (right out : List Bool) (ambient : Fin 41 → List Bool) (h : State r cap before cached right out ambient) :
    State r cap after cached right out (Function.update ambient 31
      (ZeroPadding.pad cap (frame (MatrixScoreBatch.signMagnitude r.p after)))) := by
  have other (i : Fin 41) (hi : i≠31) :
      Function.update ambient 31 (ZeroPadding.pad cap (frame (MatrixScoreBatch.signMagnitude r.p after))) i=ambient i :=
    Function.update_of_ne hi _ _
  constructor
  · constructor
    · exact (other 36 (by decide)).trans h.store.driver
    · exact (other 37 (by decide)).trans h.store.reset
    · intro i
      rw [other _ (by fin_cases i <;> decide)]
      exact h.store.support i
  · intro i
    fin_cases i
    · exact (other 0 (by decide)).trans (h.fields 0)
    · exact (other 7 (by decide)).trans (h.fields 1)
    · exact (other 25 (by decide)).trans (h.fields 2)
    · exact Function.update_self ..
    · exact (other 32 (by decide)).trans (h.fields 4)
    · exact (other 33 (by decide)).trans (h.fields 5)
    · exact (other 34 (by decide)).trans (h.fields 6)
  · exact (other 38 (by decide)).trans h.width
  · exact (other 39 (by decide)).trans h.source

noncomputable def machine := TapeEmbedding.machine 4 CompetitorSameBucketGate.machine

theorem execute_run (r : Request) (cap rankPos coefficientPos : ℕ) (coefficient : ℤ) (gate : Fin r.Gates)
    (cached : Option KeyLoop.Record) (right out : List Bool) (ambient : Fin 41 → List Bool)
    (rankSource coefficientSource rankLog coefficientLog : List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (targetFit : (ambient 39).length≤MatrixScoreReusableRanks.D r)
    (hstate : State r cap coefficient cached right out ambient) :
    ∃ actual next nextCached nextRight,runFrom machine (CompetitorSameBucketGate.budget r cap)
      (cfg machine.start r cap rankPos coefficientPos out.length ambient (CompetitorSameBucketGateScan.source r gate)
        rankSource coefficientSource rankLog coefficientLog)=some actual ∧
      actual.final.heads=heads rankPos coefficientPos (out++CompetitorSameBucketGateScan.output r coefficient gate).length ∧
      actual.final.tapes=tapes r cap next (CompetitorSameBucketGateScan.source r gate)
        rankSource coefficientSource rankLog coefficientLog ∧
      State r cap coefficient nextCached nextRight (out++CompetitorSameBucketGateScan.output r coefficient gate) next ∧
      (next 39).length≤MatrixScoreReusableRanks.D r ∧ actual.steps≤CompetitorSameBucketGate.budget r cap := by
  obtain ⟨base,next,nextCached,nextRight,hb,bs,bh,bt,hnext,hfit⟩:=
    CompetitorSameBucketGate.gate_run r cap coefficient gate cached right out ambient hc hp targetFit hstate
  have he:=TapeEmbedding.run_embed CompetitorSameBucketGate.machine
    (![rankPos,coefficientPos,0,0] : Fin 4 → ℕ) (![rankSource,coefficientSource,rankLog,coefficientLog] : Fin 4 → List Bool)
    _ _ base hb
  let actual:=TapeEmbedding.receipt (![rankPos,coefficientPos,0,0] : Fin 4 → ℕ)
    (![rankSource,coefficientSource,rankLog,coefficientLog] : Fin 4 → List Bool) base
  have hi : TapeEmbedding.config (![rankPos,coefficientPos,0,0] : Fin 4 → ℕ)
      (![rankSource,coefficientSource,rankLog,coefficientLog] : Fin 4 → List Bool)
      (CompetitorSameBucketGateScan.cfg CompetitorSameBucketGate.machine.start r cap gate 0 out.length ambient)=
      cfg machine.start r cap rankPos coefficientPos out.length ambient (CompetitorSameBucketGateScan.source r gate)
        rankSource coefficientSource rankLog coefficientLog := rfl
  rw [hi] at he
  refine ⟨actual,next,nextCached,nextRight,he,?_,?_,hnext,hfit,bs⟩
  · change Fin.addCases (motive := fun _ => ℕ) base.final.heads (![rankPos,coefficientPos,0,0] : Fin 4 → ℕ)=_
    exact congrArg (fun h : Fin 51 → ℕ => Fin.addCases (motive := fun _ => ℕ) h (![rankPos,coefficientPos,0,0] : Fin 4 → ℕ)) bh
  · change Fin.addCases (motive := fun _ => List Bool) base.final.tapes
      (![rankSource,coefficientSource,rankLog,coefficientLog] : Fin 4 → List Bool)=_
    exact congrArg (fun t : Fin 51 → List Bool => Fin.addCases (motive := fun _ => List Bool) t
      (![rankSource,coefficientSource,rankLog,coefficientLog] : Fin 4 → List Bool)) bt

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGateExecute
