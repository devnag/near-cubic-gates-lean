import Proof.CaseAnalysis.RowsGateMeasuredLayout

/-! Complete all-raw inner gate worker with its original native request and
actual original-description/support counters. Invalid public syntax never
enters the metadata copier; every accepted counter comes from retained fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads CanonicalWitnessCodec SupplierPipeline
open RadixSemantics CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Output (compressed : Bool) (core : ℕ) (bits : List Bool) (out : Fin 1049→List Bool) : Prop :=
  out (old 1035)=UnaryTemplate.tape core ∧
    (readTapeBit (out (old 1037)) 0=true ↔ (decodeSupportedNormalizedGate core (value bits)).isSome) ∧
    ∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
      out (old 1033)=frame (RepairRepresentation.thresholdWord (CloseoutRowsGateSource.request compressed g).gate) ∧
      out (slots 6)=List.replicate ((List.ofFn g.gate.weight).flatMap RepairRepresentation.intWord).length true ∧
      out (slots 11)=List.replicate (RepairRepresentation.natWord g.gate.threshold.natAbs).length true ∧
      out (slots 13)=List.replicate g.wireCount true

theorem outside (i : Fin 1038) (hi : i=1033 ∨ i=1035 ∨ i=1037) : ∀ j,slots j≠old i := by
  rcases hi with rfl|rfl|rfl <;> decide

theorem allraw (compressed : Bool) (core : ℕ) (bits : List Bool) : ∃ out,
    ReadyAt (machine compressed) (budget bits) heads (input core bits) out ∧ Output compressed core bits out := by
  obtain ⟨bank,hr,hdom,hflag,hnative⟩ := CloseoutRowsGateGuard.guard_run compressed core bits
  have firstReady := first_run compressed core bits bank hr
  by_cases hd : (decodeSupportedNormalizedGate core (value bits)).isSome
  · obtain ⟨g,hg⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨out,hs,hw,ht,hc⟩ := second_run compressed g bits hg bank hr
    have joined := CloseoutRowsGatePairHeads.joined (first compressed) second (fun scanned=>scanned (old 1037))
      _ _ heads _ _ _ firstReady hs (hflag.mpr hd)
    refine ⟨_,joined,?_,?_,?_⟩
    · rw [install_other _ _ _ _ (outside _ (Or.inr (Or.inl rfl)))]
      exact hdom
    · rw [install_other _ _ _ _ (outside _ (Or.inr (Or.inr rfl)))]
      exact hflag
    · intro g' hg'
      have he : g'=g := Option.some.inj (hg'.symm.trans hg)
      subst g'
      refine ⟨?_,?_,?_,?_⟩
      · rw [install_other _ _ _ _ (outside _ (Or.inl rfl))]
        change bank 1033=_
        rw [hnative g hg,CloseoutRowsGateSource.request_word compressed g _
          (CloseoutRowsGateGuard.sign_of_gate g bits hg)]
      · exact (install_slot _ slots_injective _ _ 6).trans hw
      · exact (install_slot _ slots_injective _ _ 11).trans ht
      · exact (install_slot _ slots_injective _ _ 13).trans hc
  · have hf : readTapeBit (bank 1037) 0=false := Bool.eq_false_iff.mpr (fun h=>hd (hflag.mp h))
    have stopped := CloseoutRowsGatePairHeads.rejected (first compressed) second
      (fun scanned=>scanned (old 1037)) _ heads _ _ firstReady hf
    refine ⟨extend bank,enlarge _ _ (budget bits) heads _ _ stopped (by unfold budget;omega),hdom,hflag,?_⟩
    intro g hg
    exact False.elim (hd (by rw [hg];rfl))

theorem budget_bound (bits : List Bool) : budget bits ≤ 4000000000000000000001086*(bits.length+2)^26 := by
  have hg := CloseoutRowsGateGuard.budget_bound bits
  have hs : (bits.length+2)^2 ≤ (bits.length+2)^26 := Nat.pow_le_pow_right (by omega) (by decide)
  have ho : 1 ≤ (bits.length+2)^26 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateMeasured
