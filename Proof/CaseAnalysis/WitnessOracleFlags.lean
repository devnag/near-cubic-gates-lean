import Proof.CaseAnalysis.WitnessOracleFooter

/-! The retained oracle flags refer to the same original raw code. Their
conjunction is exactly the public typed decoder, including canonicality,
node dependencies and the strict output-address bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flags (ts : Fin tapes→List Bool) (i : Fin 5):=
  readTapeBit (ts (verdictSlots (i.castAdd 1))) 0

theorem Compared.flag_heads {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts) :
    ∀ j : Fin 5,heads (verdictSlots (j.castAdd 1))=0:=by
  obtain ⟨base,before,co,hp,hn,_,_,_⟩:=h
  intro j
  fin_cases j
  · exact (hn.outside 201 (node_outside _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide)))).1
  · exact (hn.outside 373 (node_outside _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide)))).1
  · exact (hn.outside 549 (node_outside _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide)))).1
  · exact hn.coreHeads 754
  · exact (hn.future hp 1371 (by decide)).1

theorem Compared.flag_meaning {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Compared x bits arityBits heads ts)
    (hb : arityBits.length ≤ x.length+1) :
    DAGVerdict.accepted (flags ts)=true ↔
      (CanonicalWitnessCodec.decodeBooleanCircuit (value arityBits) (value bits)).isSome:=by
  obtain ⟨base,before,co,hp,hn,hcompare,_,rfl⟩:=h
  have old (i : Fin tapes) (hc : ∀ j,compareSlots j≠i) (hnode : ∀ j,nodeSlots j≠i) :
      install compareSlots before co i=base i:=by
    rw [install_other _ _ _ _ hc]
    exact (hn.outside i hnode).2
  have hbin:value (binary (x.length+1) (value arityBits))=value arityBits:=
    binary_value _ _ ((value_lt arityBits).trans_le (Nat.pow_le_pow_right (by decide) hb))
  apply DAGVerdict.accepted_iff
  · change readTapeBit (install compareSlots before co 201) 0=true ↔_
    rw [old 201 (compare_outside _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))) (node_outside _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (Or.inl (by decide)))]
    exact hp.header
  · change readTapeBit (install compareSlots before co 373) 0=true ↔_
    rw [old 373 (compare_outside _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))) (node_outside _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (Or.inl (by decide)))]
    exact hp.list
  · change readTapeBit (install compareSlots before co 549) 0=true ↔_
    rw [old 549 (compare_outside _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))) (node_outside _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (Or.inl (by decide)))]
    exact hp.natural
  · change readTapeBit (install compareSlots before co 1306) 0=true ↔_
    rw [install_other _ _ _ _ (compare_outside 1306 (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide)))]
    have ht:=hn.core 754
    change before 1306=[NodeLoop.validity (value (binary (x.length+1) (value arityBits)))
      true (DAGChecks.words bits) (DAGChecks.words bits).length] at ht
    rw [ht,hbin]
    exact NodeLoop.validity_true _ _
  · change readTapeBit (install compareSlots before co (compareSlots 19)) 0=true ↔_
    rw [install_slot _ compare_injective,hcompare]
    exact Bool.decide_iff ((DAGChecks.words bits).length ≤ DAGChecks.output bits)

theorem flag_outside_footer (j : Fin 5) : ∀ k,footerSlots k≠verdictSlots (j.castAdd 1):=by
  fin_cases j
  all_goals exact footer_outside _ (by decide) (by decide) (by decide) (Or.inl (by decide))

theorem Described.flag_heads {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Described x bits arityBits heads ts) :
    ∀ j : Fin 5,heads (verdictSlots (j.castAdd 1))=0:=by
  obtain ⟨bh,bt,hb,_,_,ho⟩:=h
  intro j
  exact ((ho _ (flag_outside_footer j)).1).trans (hb.flag_heads j)

theorem Described.flag_meaning {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Described x bits arityBits heads ts)
    (hb : arityBits.length ≤ x.length+1) :
    DAGVerdict.accepted (flags ts)=true ↔
      (CanonicalWitnessCodec.decodeBooleanCircuit (value arityBits) (value bits)).isSome:=by
  obtain ⟨bh,bt,hbefore,_,_,ho⟩:=h
  have he:flags ts=flags bt:=by
    funext j
    unfold flags
    rw [(ho _ (flag_outside_footer j)).2]
  rw [he]
  exact hbefore.flag_meaning hb

theorem Described.fresh {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Described x bits arityBits heads ts) :
    heads 1379=0 ∧ ts 1379=[]:=by
  obtain ⟨bh,bt,hb,_,_,ho⟩:=h
  obtain ⟨hh,ht⟩:=ho 1379 (footer_outside _ (by decide) (by decide) (by decide) (Or.inr (by decide)))
  exact ⟨hh.trans (hb.future 1379 (by decide)).1,ht.trans (hb.future 1379 (by decide)).2⟩

theorem verdict_heads {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Described x bits arityBits heads ts) :
    ∀ j,heads (verdictSlots j)=0:=by
  intro j
  refine Fin.addCases (m:=5) (n:=1) ?_ ?_ j
  · intro i
    exact h.flag_heads i
  · intro i
    have hi:i=0:=Fin.eq_zero i
    subst i
    exact h.fresh.1

theorem verdict_input {x bits arityBits : List Bool} {ts : Fin tapes→List Bool}
    {heads : Fin tapes→ℕ} (h : Described x bits arityBits heads ts) :
    ∀ j,ts (verdictSlots j)=DAGVerdict.input (fun i=>ts (verdictSlots (i.castAdd 1))) j:=by
  intro j
  refine Fin.addCases (m:=5) (n:=1) ?_ ?_ j
  · intro i
    simp [DAGVerdict.input]
  · intro i
    have hi:i=0:=Fin.eq_zero i
    subst i
    exact h.fresh.2

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
