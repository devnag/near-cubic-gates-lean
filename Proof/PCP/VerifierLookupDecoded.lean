import Proof.PCP.VerifierLookupReuseState

/-! The runtime canonical-code premise follows from the actual decoder's
semantic success on the same source word. No selected-row supplier remains. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_of_decode (N : ℕ) (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (hd : decode N d.code=some v) (ht : d.t=v.tapeCount) (hs : d.s=v.stateCount)
    (hj : d.j=natBitLength v.stateCount) (hq : d.state=binary (natBitLength v.stateCount) q.val) :
    Canonical d v q := ⟨(decode_code_length hd).2.symm,ht,hs,hj,hq⟩

theorem decoded_lookup_run (N : ℕ) (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (scanned : Fin v.tapeCount→Bool) (hd : decode N d.code=some v)
    (ht : d.t=v.tapeCount) (hv : d.s=v.stateCount) (hj : d.j=natBitLength v.stateCount)
    (hstate : d.state=binary (natBitLength v.stateCount) q.val) (pre tail : List Bool)
    (hpos : d.codePos≤2*d.code.length+1)
    (hs : d.scans=pre++Streaming.marks (List.ofFn scanned)++tail) (hp : d.scanPos=pre.length)
    (hcap : 2*(d.t+d.j)+2≤d.cap)
    (hsc : d.scanCopy.length≤2*d.t+1)
    (hfq : d.flagQuery.length≤2*d.j+1) (hfz : d.flagCounter.length≤2*d.j+1)
    (hquery : d.query.length≤2*(d.t+d.j)+1) (hz : d.counter.length≤2*(d.t+d.j)+1)
    (hn : d.nextState.length≤2*d.j+1) (htags : d.tags.length≤8*d.t+1) :
    let word := actionCode d.j (v.machine.rule q scanned)
    ∃ r,runFrom machine (128*(d.code.length+1)^2) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d (List.ofFn scanned)) ∧
      r.steps≤128*(d.code.length+1)^2 ∧
      r.final.tapes 8=[v.machine.halted q] ∧ r.final.tapes 9=[v.accepting q] ∧
      r.final.tapes 10=[word.getD 0 false] ∧
      r.final.tapes 11=frame (slice word 1 d.j) ∧ r.final.tapes 12=frame (slice word (1+d.j) (4*d.t)) := by
  exact canonical_lookup_run d v q scanned (canonical_of_decode N d v q hd ht hv hj hstate) pre tail
    hpos hs hp hcap hsc hfq hfz hquery hz hn htags

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
