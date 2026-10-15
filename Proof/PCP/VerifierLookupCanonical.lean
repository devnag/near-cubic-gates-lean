import Proof.PCP.VerifierLookupLiteralSlices

/-! The complete runtime consumer identifies its physical fields with the
same verifier and state appearing in literal_lookup. Canonical code supplies
all flag/record range facts; none is an additional runtime assumption. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Canonical (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount) : Prop where
  code_eq : d.code=code v
  tapes_eq : d.t=v.tapeCount
  states_eq : d.s=v.stateCount
  width_eq : d.j=natBitLength v.stateCount
  state_eq : d.state=binary (natBitLength v.stateCount) q.val

theorem Canonical.state_length {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    d.state.length=d.j := by rw [h.state_eq,binary_length,h.width_eq]

theorem Canonical.state_value {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    value d.state=q.val := by
  rw [h.state_eq,binary_value]
  exact q.isLt.trans (Nat.lt_pow_succ_log_self (by decide) v.stateCount)

theorem Canonical.query_value {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    value (List.ofFn scanned++d.state)=LookupLiteral.ordinal v q scanned := by
  have hs : q.val<2^natBitLength v.stateCount :=
    q.isLt.trans (Nat.lt_pow_succ_log_self (by decide) v.stateCount)
  rw [h.state_eq,LookupPosition.query_value (List.ofFn scanned) (natBitLength v.stateCount) q.val hs,List.length_ofFn]
  rfl

theorem Canonical.flag_offset {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    flagOffset d=(LookupLiteral.header v).length+2*q.val := by
  rw [flagOffset,h.tapes_eq,h.states_eq,h.width_eq,h.state_value,LookupLiteral.header_length]

theorem Canonical.table_offset {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    tableOffset d (List.ofFn scanned)=LookupLiteral.recordOffset v q scanned := by
  rw [tableOffset,h.tapes_eq,h.states_eq,h.width_eq,h.query_value scanned,LookupLiteral.recordOffset]
  simp only [List.length_append,LookupLiteral.header_length,flags_length,entryWidth]
  ring

theorem Canonical.flag_fit {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    flagOffset d+2≤d.code.length := by
  rw [h.flag_offset,h.code_eq,LookupLiteral.split_code]
  simp only [List.length_append,flags_length]
  omega

theorem Canonical.table_fit {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    tableOffset d (List.ofFn scanned)+1+d.j+4*d.t≤d.code.length := by
  rw [h.table_offset scanned,h.width_eq,h.tapes_eq,h.code_eq]
  have hb := LookupLiteral.record_fit v q scanned
  unfold entryWidth at hb
  omega

theorem Canonical.halt_bit {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    d.code.getD (flagOffset d) false=v.machine.halted q := by
  rw [h.code_eq,h.flag_offset]
  have hs := LookupLiteral.getD_slice (code v) ((LookupLiteral.header v).length+2*q.val) 2 0 (by decide)
  rw [LookupLiteral.flag_pair] at hs
  simpa only [List.getD,List.getElem?_cons_zero,Option.getD_some,Nat.add_zero] using hs.symm

theorem Canonical.accept_bit {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q) :
    d.code.getD (flagOffset d+1) false=v.accepting q := by
  rw [h.code_eq,h.flag_offset]
  have hs := LookupLiteral.getD_slice (code v) ((LookupLiteral.header v).length+2*q.val) 2 1 (by decide)
  rw [LookupLiteral.flag_pair] at hs
  simpa only [List.getD,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using hs.symm

theorem Canonical.record_word {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    slice d.code (tableOffset d (List.ofFn scanned)) (1+d.j+4*d.t)=
      actionCode d.j (v.machine.rule q scanned) := by
  rw [h.code_eq,h.table_offset scanned,h.width_eq,h.tapes_eq]
  exact LookupLiteral.code_record v q scanned

theorem Canonical.finished_fields {d : Store} {v : OrdinaryVerifier} {q : Fin v.stateCount} (h : Canonical d v q)
    (scanned : Fin v.tapeCount→Bool) :
    let word := actionCode d.j (v.machine.rule q scanned)
    (finished d (List.ofFn scanned)).halt=v.machine.halted q ∧
    (finished d (List.ofFn scanned)).accept=v.accepting q ∧
    (finished d (List.ofFn scanned)).present=word.getD 0 false ∧
    (finished d (List.ofFn scanned)).nextState=frame (slice word 1 d.j) ∧
    (finished d (List.ofFn scanned)).tags=frame (slice word (1+d.j) (4*d.t)) := by
  dsimp only
  obtain ⟨hh,ha,hp,hn,ht⟩ := LookupRuntime.finished_fields d (List.ofFn scanned)
  rw [h.halt_bit] at hh
  rw [h.accept_bit] at ha
  have hw := h.record_word scanned
  have hpr := LookupLiteral.getD_slice d.code (tableOffset d (List.ofFn scanned)) (1+d.j+4*d.t) 0 (by omega)
  rw [hw] at hpr
  simp only [Nat.add_zero] at hpr
  have hnxt := Sequential.slice_slice d.code (tableOffset d (List.ofFn scanned)) (1+d.j+4*d.t) 1 d.j (by omega)
  rw [hw] at hnxt
  have htag := Sequential.slice_slice d.code (tableOffset d (List.ofFn scanned)) (1+d.j+4*d.t) (1+d.j) (4*d.t) (by omega)
  rw [hw] at htag
  refine ⟨hh,ha,hp.trans hpr.symm,hn.trans (congrArg frame hnxt.symm),?_⟩
  have ho : tableOffset d (List.ofFn scanned)+(1+d.j)=tableOffset d (List.ofFn scanned)+1+d.j := by omega
  rw [ho] at htag
  exact ht.trans (congrArg frame htag.symm)

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
