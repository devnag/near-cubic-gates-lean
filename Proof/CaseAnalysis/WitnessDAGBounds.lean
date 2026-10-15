import Proof.CaseAnalysis.WitnessDAGChecks

/-! The exact raw count and input-derived width pay for every node round.
This fixed polynomial degree is chosen before the hierarchy clock exponent;
no source resource or numeric coefficient cap is used to bound malformed codes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGBounds
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_word_length (bits : List Bool) :
    (PCPPNativeCanonical.nodeWord bits).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits 1)

theorem guarded_fields (N : ℕ) (bits : List Bool) (hN : 2≤N) (hcap : 16*bits.length≤N) :
    (DAGChecks.words bits).length≤N ∧
    (∀ word∈DAGChecks.words bits,word.length+1≤N+1) ∧
    (DAGChecks.words bits).length<2^(N+1):=by
  obtain ⟨hc,hw⟩:=DAGChecks.fields_bound bits
  rw [node_word_length] at hc hw
  have hk:(DAGChecks.words bits).length≤N:=by omega
  refine ⟨hk,?_,?_⟩
  · intro word hword
    rw [hw word hword]
    omega
  · have hp:N+1<2^(N+1):=Nat.lt_two_pow_self
    omega

theorem loop_budget (w count : ℕ) (hw : 1≤w) (hc : count≤w) :
    NodeLoop.budget w count≤565000000000000000006*w^25:=by
  have h:=Nat.mul_le_mul_right (5*NodeReady.capacity w+3) hc
  have he:w*(5*NodeReady.capacity w+3)=565000000000000000000*w^25+3*w:=by
    unfold NodeReady.capacity
    rw [pow_succ]
    ring
  rw [he] at h
  have hp:w≤w^25:=Nat.le_self_pow (by decide) _
  have hpos:1≤w^25:=Nat.one_le_pow _ _ hw
  unfold NodeLoop.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGBounds
