import Proof.CaseAnalysis.RowsGateNativeFrame

/-! The physical native word is exactly the corrected source request.
Bottom gates keep their full arity; the retained top uses its original
sorted support map. The same strict threshold is used in both cases. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
open LocalBitMultitape RepairRepresentation CloseoutRowsGateSupport
open SupplierPipeline CompilerSemantics RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_bound {n : ℕ} (g : NormalizedThresholdGate n) :
    ∀ field∈gateFields g,field.2.length ≤ g.encodingBits := by
  intro field hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  simp only [intField,binary_length]
  change intBitLength (g.weight i) ≤ g.encodingBits
  have hsum := Finset.single_le_sum (fun j _ => Nat.zero_le (intBitLength (g.weight j)))
    (Finset.mem_univ i)
  unfold NormalizedThresholdGate.encodingBits
  omega

theorem ordinary_weights {n : ℕ} (g : NormalizedThresholdGate n) (s : Finset (Fin n)) :
    weights false (gateFields g) (gateMembers s)=(List.ofFn g.weight).flatMap intWord := by
  unfold weights
  rw [show (gateFields g).length=n by simp [gateFields],gate_emission]
  simp [selected,keep,PCPPQueryField.selected,List.ofFn_eq_map,List.flatMap_map]

theorem retained_weights_word {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) :
    weights true (gateFields c.top.gate) (gateMembers c.top.support)=
      (List.ofFn (retainedTopGate c).weight).flatMap intWord := by
  unfold weights
  rw [show (gateFields c.top.gate).length=c.bottomCount by simp [gateFields]]
  exact retained_weights c

theorem ordinary_word {n : ℕ} (g : SupportedNormalizedGate n) (source : List Bool)
    (hs : readTapeBit source 1=decide (g.gate.threshold<0)) :
    word false (gateFields g.gate) (gateMembers g.support) source g.gate.threshold.natAbs=
      thresholdWord (nonStrictAsStrict g.gate) := by
  change natWord (gateFields g.gate).length++weights false (gateFields g.gate) (gateMembers g.support)++
    CloseoutRowsStrictNative.produced source g.gate.threshold.natAbs=_
  rw [show (gateFields g.gate).length=n by simp [gateFields],ordinary_weights,
    CloseoutRowsStrictNative.produced_eq source g.gate.threshold hs]
  rfl

theorem retained_word {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (source : List Bool)
    (hs : readTapeBit source 1=decide (c.top.gate.threshold<0)) :
    word true (gateFields c.top.gate) (gateMembers c.top.support) source c.top.gate.threshold.natAbs=
      thresholdWord (nonStrictAsStrict (retainedTopGate c)) := by
  change natWord (CloseoutRowsSupportCount.ones (gateMembers c.top.support))++
    weights true (gateFields c.top.gate) (gateMembers c.top.support)++
    CloseoutRowsStrictNative.produced source c.top.gate.threshold.natAbs=_
  rw [CloseoutRowsSupportCount.support_card,retained_weights_word,
    CloseoutRowsStrictNative.produced_eq source c.top.gate.threshold hs]
  rfl

theorem ordinary_run {n : ℕ} (g : SupportedNormalizedGate n) (source : List Bool)
    (hs : readTapeBit source 1=decide (g.gate.threshold<0)) : ∃ out,
    ClockJoin.ReadyRun (framedMachine false)
      (framedBudget false (gateFields g.gate) (gateMembers g.support) source
        g.gate.threshold.natAbs g.gate.encodingBits)
      (framedInput (gateFields g.gate) (gateMembers g.support) source g.gate.threshold.natAbs) out ∧
      out 40=frame (thresholdWord (nonStrictAsStrict g.gate)) ∧ out 25=[true] := by
  obtain ⟨out,hr,ht,hflag⟩ := framed_run false (gateFields g.gate) (gateMembers g.support) source
    g.gate.threshold.natAbs g.gate.encodingBits (field_bound g.gate)
  refine ⟨out,hr,?_,?_⟩
  · rw [ht,ordinary_word g source hs]
  · rw [hflag,show (gateFields g.gate).length=n by simp [gateFields],gate_validity]

theorem retained_run {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (source : List Bool)
    (hs : readTapeBit source 1=decide (c.top.gate.threshold<0)) : ∃ out,
    ClockJoin.ReadyRun (framedMachine true)
      (framedBudget true (gateFields c.top.gate) (gateMembers c.top.support) source
        c.top.gate.threshold.natAbs c.top.gate.encodingBits)
      (framedInput (gateFields c.top.gate) (gateMembers c.top.support) source c.top.gate.threshold.natAbs) out ∧
      out 40=frame (thresholdWord (nonStrictAsStrict (retainedTopGate c))) ∧ out 25=[true] := by
  obtain ⟨out,hr,ht,hflag⟩ := framed_run true (gateFields c.top.gate) (gateMembers c.top.support) source
    c.top.gate.threshold.natAbs c.top.gate.encodingBits (field_bound c.top.gate)
  refine ⟨out,hr,?_,?_⟩
  · rw [ht,retained_word c source hs]
  · rw [hflag,show (gateFields c.top.gate).length=c.bottomCount by simp [gateFields],gate_validity]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
