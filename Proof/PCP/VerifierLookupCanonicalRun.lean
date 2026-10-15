import Proof.PCP.VerifierLookupCanonical

/-! Canonical verifier lookup by one fixed ordinary finite machine, with a
quadratic literal-code budget and exact halted/acceptance/action fields. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Canonical.dimensions {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    d.t≤d.code.length ∧ d.s≤d.code.length ∧ d.j≤d.code.length ∧
    value d.state+1≤d.code.length ∧ value (List.ofFn scanned++d.state)+1≤d.code.length := by
  have ht : v.tapeCount≤(code v).length := tapes_le_code_length v
  have hs : v.stateCount≤(code v).length := by rw [code_length]; omega
  have hj : natBitLength v.stateCount≤(code v).length := by rw [code_length]; omega
  have he : v.stateCount*2^v.tapeCount≤(code v).length := by
    have hp := Nat.le_mul_of_pos_right (v.stateCount*2^v.tapeCount)
      (by omega : 0<1+natBitLength v.stateCount+4*v.tapeCount)
    rw [code_length]
    omega
  rw [h.tapes_eq,h.states_eq,h.width_eq,h.code_eq,h.state_value,h.query_value scanned]
  have ho := LookupLiteral.ordinal_lt v q scanned
  exact ⟨ht,hs,hj,(Nat.succ_le_of_lt q.isLt).trans hs,(Nat.succ_le_of_lt ho).trans he⟩

theorem Canonical.budget_le {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) : budget d (List.ofFn scanned)≤128*(d.code.length+1)^2 := by
  obtain ⟨ht,hs,hj,hq,ho⟩ := h.dimensions scanned
  have hfirst := Nat.mul_le_mul hq (by omega : 8*d.j+14≤8*d.code.length+14)
  have hsecond := Nat.mul_le_mul ho
    (by omega : 8*(d.t+d.j)+3*d.j+12*d.t+27≤31*d.code.length+27)
  unfold budget flagsBudget tableBudget
  nlinarith

theorem canonical_lookup_run (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (scanned : Fin v.tapeCount→Bool) (hc : Canonical d v q) (pre tail : List Bool)
    (hpos : d.codePos≤2*d.code.length+1)
    (hs : d.scans=pre++Streaming.marks (List.ofFn scanned)++tail) (hp : d.scanPos=pre.length)
    (hcap : 2*(d.t+d.j)+2≤d.cap)
    (hsc : d.scanCopy.length≤2*d.t+1)
    (hfq : d.flagQuery.length≤2*d.j+1) (hfz : d.flagCounter.length≤2*d.j+1)
    (hq : d.query.length≤2*(d.t+d.j)+1) (hz : d.counter.length≤2*(d.t+d.j)+1)
    (hn : d.nextState.length≤2*d.j+1) (htags : d.tags.length≤8*d.t+1) :
    let word := actionCode d.j (v.machine.rule q scanned)
    ∃ r,runFrom machine (128*(d.code.length+1)^2) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d (List.ofFn scanned)) ∧
      r.steps≤128*(d.code.length+1)^2 ∧
      r.final.tapes 8=[v.machine.halted q] ∧ r.final.tapes 9=[v.accepting q] ∧
      r.final.tapes 10=[word.getD 0 false] ∧
      r.final.tapes 11=frame (slice word 1 d.j) ∧ r.final.tapes 12=frame (slice word (1+d.j) (4*d.t)) := by
  dsimp only
  have hl : (List.ofFn scanned).length=d.t := by rw [List.length_ofFn,hc.tapes_eq]
  obtain ⟨r,hr,hrf,hrs⟩ := lookup_run d pre (List.ofFn scanned) tail hpos hs hp hl hc.state_length hcap
    hsc hfq hfz hq hz hn htags hc.flag_fit (hc.table_fit scanned)
  have hb := hc.budget_le scanned
  have hm := runFrom_moreFuel machine (budget d (List.ofFn scanned))
    (128*(d.code.length+1)^2-budget d (List.ofFn scanned)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  obtain ⟨hh,ha,hp,hnext,ht⟩ := hc.finished_fields scanned
  refine ⟨r,hm,hrf,hrs.trans hb,?_,?_,?_,?_,?_⟩
  · rw [hrf]
    exact congrArg (fun b=>[b]) hh
  · rw [hrf]
    exact congrArg (fun b=>[b]) ha
  · rw [hrf]
    exact congrArg (fun b=>[b]) hp
  · rw [hrf]
    exact hnext
  · rw [hrf]
    exact ht

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
