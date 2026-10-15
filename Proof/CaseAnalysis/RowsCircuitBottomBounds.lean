import Proof.CaseAnalysis.RowsCircuitBottomChoice

/-! The reusable append log is paid from the SAME all-raw gate budget.
Its counters are actual produced unary lengths, never declared numeric
values. A single fixed enlargement of the preprocessing capacity suffices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics CloseoutRowsGatePairHeads CanonicalWitnessCodec SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem counter_bound (core : ℕ) (bits : List Bool) (out : Fin 1049→List Bool)
    (h : ReadyAt (CloseoutRowsGateMeasured.machine false) (CloseoutRowsGateMeasured.budget bits)
      CloseoutRowsGateMeasured.heads (CloseoutRowsGateMeasured.input core bits) out)
    (i : Fin 1049) (hi : 1038 ≤ i.val) : (out i).length ≤ CloseoutRowsGateMeasured.budget bits+1 := by
  obtain ⟨r,hr,rt,_rh,rs⟩:=h
  have bound:=PCPSerializerReuse.tape_support (CloseoutRowsGateMeasured.machine false) _ _ r hr i 0 0
    (by change CloseoutRowsGateMeasured.heads i ≤ 0;rw [CloseoutRowsGateBank.heads_eq,if_neg (by omega)])
    (by
      change (CloseoutRowsGateMeasured.input core bits i).length ≤ max 0 (0+1)
      rw [CloseoutRowsGateBank.input_eq,if_neg (by omega),if_neg (by omega)]
      decide)
  rw [rt] at bound
  simpa only [Nat.zero_add,Nat.max_eq_right (Nat.zero_le _)] using
    bound.trans (by omega : max 0 (0+r.steps+1) ≤ CloseoutRowsGateMeasured.budget bits+1)

theorem gate_counter_bounds {core : ℕ} (g : SupportedNormalizedGate core) (bits : List Bool)
    (hg : decodeSupportedNormalizedGate core (value bits)=some g) :
    ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length+
      (RepairRepresentation.natWord g.gate.threshold.natAbs).length+2 ≤ 2*CloseoutRowsGateMeasured.budget bits+4 ∧
      g.wireCount+1+2 ≤ 2*CloseoutRowsGateMeasured.budget bits+4 := by
  obtain ⟨out,run,meaning⟩:=CloseoutRowsGateMeasured.allraw false core bits
  obtain ⟨_native,weights,threshold,support⟩:=meaning.2.2 g hg
  have hw:=counter_bound core bits out run 1041 (by decide)
  have ht:=counter_bound core bits out run 1045 (by decide)
  have hs:=counter_bound core bits out run 1047 (by decide)
  change out 1041=_ at weights
  change out 1045=_ at threshold
  change out 1047=_ at support
  rw [weights,List.length_replicate] at hw
  rw [threshold,List.length_replicate] at ht
  rw [support,List.length_replicate] at hs
  omega

theorem choice_budget_bound (cap support : ℕ) (bits : List Bool)
    (hb : 2*bits.length+1 ≤ cap) (hs : support+1+2 ≤ cap) : choiceBudget bits support ≤ 4*cap+6 := by
  unfold choiceBudget;omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
