import Proof.MachineModel.UEmissionData

/-! The decoded and bounded witness fields are uniquely determined by the
literal external words. They imply the already executed front's predicate. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Fields.count_lt {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    d.count < 2^ClockDyadicLedger.width raw.length := by
  have hp := (ClockDyadicLedger.width_bounds raw.length).1
  have hm := h.count_bound.trans h.choices_bound
  omega

theorem Fields.unique {raw witness : List Bool} {d e : TraceData}
    (h : Fields raw witness d) (h' : Fields raw witness e) : d=e := by
  obtain ⟨hw,hx,hb,hp⟩ := UInputEntry.source_unique _ _ _ _ _ _ _ _ (h.source.symm.trans h'.source)
  have hv : d.verifier=e.verifier := by
    have he := h.decoded
    rw [hw,h'.decoded] at he
    exact (Option.some.inj he).symm
  have hprefix := h.witness_eq.symm.trans h'.witness_eq
  rw [List.append_assoc,List.append_assoc] at hprefix
  obtain ⟨hmword,htail⟩ := List.append_inj hprefix (by simp only [binary_length])
  have hm : d.count=e.count := by
    have he := congrArg RadixSemantics.value hmword
    simpa only [binary_value _ _ h.count_lt,binary_value _ _ h'.count_lt] using he
  obtain ⟨hc,hs⟩ := List.append_inj htail (by rw [h.choices_length,h'.choices_length,hb])
  cases d
  cases e
  simp_all

theorem Fields.witness_valid {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    UWitness.Valid (ClockDyadicLedger.width raw.length) (RadixSemantics.value d.bound) witness := by
  have hm : UWitness.mValue (ClockDyadicLedger.width raw.length) witness=d.count := by
    simp [UWitness.mValue,h.witness_eq,binary_length,binary_value _ _ h.count_lt]
  have hlen : witness.length=ClockDyadicLedger.width raw.length+d.choices.length+d.suffix.length := by
    simp only [h.witness_eq,List.length_append,binary_length]
  refine ⟨by omega,?_,?_⟩
  · rw [hm,←h.choices_length]
    exact h.count_bound
  · rw [←h.choices_length]
    omega

theorem Fields.front_accepted {raw witness : List Bool} {d : TraceData} (h : Fields raw witness d) :
    UFront.Accepted raw witness :=
  ⟨d.word,d.input,d.bound,d.padding,h.source,h.guards,⟨d.verifier,h.decoded⟩,h.witness_valid⟩

end NearCubicWires.RepairOrdinary.UEmission
