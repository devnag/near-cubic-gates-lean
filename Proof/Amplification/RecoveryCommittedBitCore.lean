import Proof.Amplification.RecoveryCommittedBitGraph

/-! Whole bounded committed-word scan from the marker node. The current
query counter is decremented only while an actual committed bit remains. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCommittedBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem core_run (bits : List Bool) (d : Data) (pre : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length)
    (hc : 2*d.query.length+1≤d.capacity) :
    ∃ n,n≤bits.length*(4*d.query.length+9)+2 ∧
      Timed raw n (d.cfg (RecoveryCalls.code graphSizes 0 (0 : Fin 3)))
        ((finishData bits d).cfg (RecoveryCalls.controlCode graphSizes none)) := by
  induction bits generalizing d pre with
  | nil =>
    obtain ⟨r,hr,hf,_⟩ := marker_nil d pre hs hp
    obtain ⟨n,hn,h⟩ := stop_receipt graphSizes programs 4 next 0 _ _ r hr (by rw [hf]; rfl)
    rw [hf] at h
    exact ⟨n,by simpa using hn,h⟩
  | cons bit bits ih =>
    obtain ⟨r0,hr0,hf0,_⟩ := marker_cons d pre bits bit hs hp
    obtain ⟨n0,hn0,h0⟩ := call_receipt graphSizes programs 4 next 0 1 _ _ r0 hr0 (by rw [hf0]; rfl)
    rw [hf0] at h0
    change Timed raw n0 (d.cfg (RecoveryCalls.code graphSizes 0 (0 : Fin 3)))
      (d.atBit.cfg (RecoveryCalls.code graphSizes 1 predMachine.start)) at h0
    obtain ⟨r1,hr1,hf1,_⟩ := pred_run d.atBit hc
    have hflag : r1.final.scanned 1=decide (value d.query≠0) := by rw [hf1]; rfl
    by_cases hz : value d.query=0
    · obtain ⟨n1,hn1,h1⟩ := call_receipt graphSizes programs 4 next 1 3 _ _ r1 hr1 (by simp [next,hflag,hz])
      rw [hf1] at h1
      change Timed raw n1 (d.atBit.cfg (RecoveryCalls.code graphSizes 1 predMachine.start))
        (d.atBit.afterPred.cfg (RecoveryCalls.code graphSizes 3 (0 : Fin 2))) at h1
      have hread : readTapeBit d.atBit.afterPred.source d.atBit.afterPred.pos=bit := by
        change readTapeBit d.source (d.pos+1)=bit
        rw [hs,hp]
        simpa [frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame bits) bit
      obtain ⟨r2,hr2,hf2,_⟩ := write_run d.atBit.afterPred true false
      change r2.final=(d.atBit.afterPred.picked (readTapeBit d.atBit.afterPred.source d.atBit.afterPred.pos)).cfg 1 at hf2
      rw [hread] at hf2
      obtain ⟨n2,hn2,h2⟩ := stop_receipt graphSizes programs 4 next 3 _ _ r2 hr2 (by rfl)
      rw [hf2] at h2
      change Timed raw n2 (d.atBit.afterPred.cfg (RecoveryCalls.code graphSizes 3 (0 : Fin 2)))
        ((d.atBit.afterPred.picked bit).cfg (RecoveryCalls.controlCode graphSizes none)) at h2
      have h := (h0.trans h1).trans h2
      refine ⟨n0+n1+n2,?_,?_⟩
      · change n1≤4*d.query.length+4+1 at hn1
        simp only [List.length_cons]
        nlinarith
      · simpa only [finishData,hz,↓reduceIte] using h
    · obtain ⟨n1,hn1,h1⟩ := call_receipt graphSizes programs 4 next 1 2 _ _ r1 hr1 (by simp [next,hflag,hz])
      rw [hf1] at h1
      change Timed raw n1 (d.atBit.cfg (RecoveryCalls.code graphSizes 1 predMachine.start))
        (d.atBit.afterPred.cfg (RecoveryCalls.code graphSizes 2 (0 : Fin 2))) at h1
      obtain ⟨r2,hr2,hf2,_⟩ := advance_run d.atBit.afterPred
      obtain ⟨n2,hn2,h2⟩ := call_receipt graphSizes programs 4 next 2 0 _ _ r2 hr2 (by rfl)
      rw [hf2] at h2
      change Timed raw n2 (d.atBit.afterPred.cfg (RecoveryCalls.code graphSizes 2 (0 : Fin 2)))
        (d.atBit.afterPred.atBit.cfg (RecoveryCalls.code graphSizes 0 (0 : Fin 3))) at h2
      have hs' : d.atBit.afterPred.atBit.source=(pre++[true,bit])++frame bits := by
        change d.source=_
        rw [hs]
        simp only [frame,List.append_assoc,List.cons_append,List.nil_append]
      have hp' : d.atBit.afterPred.atBit.pos=(pre++[true,bit]).length := by
        simp [Data.atBit,Data.afterPred,hp,Nat.add_assoc]
      have hc' : 2*d.atBit.afterPred.atBit.query.length+1≤d.atBit.afterPred.atBit.capacity := by
        simpa only [Data.atBit,Data.afterPred,RecoveryListPredecessor.result_length] using hc
      obtain ⟨nt,hnt,ht⟩ := ih d.atBit.afterPred.atBit (pre++[true,bit]) hs' hp' hc'
      have h := ((h0.trans h1).trans h2).trans ht
      refine ⟨n0+n1+n2+nt,?_,?_⟩
      · change n1≤4*d.query.length+4+1 at hn1
        change nt≤bits.length*(4*(RecoveryListPredecessor.result d.query true).length+9)+2 at hnt
        rw [RecoveryListPredecessor.result_length] at hnt
        simp only [List.length_cons]
        nlinarith
      · simpa only [finishData,hz,↓reduceIte] using h

end NearCubicWires.RepairOrdinary.RecoveryCommittedBit
