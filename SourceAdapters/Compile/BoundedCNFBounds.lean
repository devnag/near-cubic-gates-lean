import SourceAdapters.Compile.BoundedCNFValues

/-!
proof of `lem:multitape-refuter`, Step 3: charge the literal machine table and
clock in one fixed request measure. Every exponent/coefficient below is global,
independent of the verifier. These are layout-size bounds, not an ordinary
program execution bound. -/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
set_option autoImplicit false

theorem request_measure_positive (r : CNFCompilationRequest) : 1 ≤ r.measure := by
  simp only [CNFCompilationRequest.measure]
  omega

theorem request_parameters_le (r : CNFCompilationRequest) :
    r.verifier.tapeCount ≤ r.measure ∧ r.verifier.stateCount ≤ r.measure ∧
    r.verifier.stateCount * 2^r.verifier.tapeCount ≤ r.measure ∧
    r.fuel+1 ≤ r.measure ∧ r.witnessLength ≤ r.measure := by
  have hc : (VerifierEncoding.code r.verifier).length ≤ r.measure := by
    simp only [CNFCompilationRequest.measure]
    omega
  have hl := VerifierEncoding.code_length r.verifier
  have ht := VerifierEncoding.tapes_le_code_length r.verifier
  have hr : r.verifier.stateCount * 2^r.verifier.tapeCount ≤
      r.verifier.stateCount * 2^r.verifier.tapeCount *
        (1+natBitLength r.verifier.stateCount+4*r.verifier.tapeCount) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  simp only [CNFCompilationRequest.measure] at *
  omega

theorem request_transition_bound (r : CNFCompilationRequest) :
    transitionBitBound r.verifier.tapeCount r.verifier.stateCount (r.fuel+1) ≤
      36*r.measure^3 := by
  obtain ⟨ht, hs, hr, hw, _⟩ := request_parameters_le r
  have hm := request_measure_positive r
  have hsq : r.measure ≤ r.measure^2 := Nat.le_self_pow (by decide) _
  have hcu : r.measure ≤ r.measure^3 := Nat.le_self_pow (by decide) _
  have hA : r.verifier.tapeCount * (2*(r.fuel+1)+3) + 2 +
      4*(r.verifier.tapeCount+1)*((r.fuel+1)+2)+2 ≤ 33*r.measure^2 := by
    calc
      _ ≤ r.measure * (2*r.measure+3) + 2 + 4*(r.measure+1)*(r.measure+2)+2 := by gcongr
      _ ≤ _ := by nlinarith
  calc
    _ = (r.verifier.stateCount*2^r.verifier.tapeCount) *
      (r.verifier.tapeCount * (2*(r.fuel+1)+3) + 2 +
        4*(r.verifier.tapeCount+1)*((r.fuel+1)+2)+2) + 2*r.verifier.stateCount+1 := by
          unfold transitionBitBound
          ring
    _ ≤ r.measure*(33*r.measure^2)+2*r.measure+1 := by gcongr
    _ ≤ _ := by nlinarith

theorem request_window_bound (r : CNFCompilationRequest) :
    windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel+1) ≤ 3*r.measure^2 := by
  obtain ⟨ht, hs, _, hw, _⟩ := request_parameters_le r
  have hsq : r.measure ≤ r.measure^2 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ r.measure + (r.measure*r.measure+r.measure*r.measure) := by unfold windowBits; gcongr
    _ ≤ _ := by nlinarith

/-- proof of `lem:multitape-refuter`, Step 3: globally fixed degree-six bound for the actual request circuit. -/
theorem requestCircuit_polynomial (r : CNFCompilationRequest) :
    (requestCircuit r).size ≤ 128*r.measure^6 := by
  obtain ⟨_, hs, _, hw, hn⟩ := request_parameters_le r
  have hm := request_measure_positive r
  have hm6 : 1 ≤ r.measure^6 := one_le_pow₀ hm
  have h16 : r.measure ≤ r.measure^6 := Nat.le_self_pow (by decide) _
  have h26 : r.measure^2 ≤ r.measure^6 := Nat.pow_le_pow_right hm (by decide)
  have hc := requestCircuit_size r
  have hv := verifierCircuit_size r.verifier r.input r.witnessLength r.fuel
  have hwindow := request_window_bound r
  have htransition := request_transition_bound r
  have hf : r.fuel ≤ r.measure := by omega
  have hb : windowBits r.verifier.tapeCount r.verifier.stateCount (r.fuel+1) *
      (1+r.fuel*transitionBitBound r.verifier.tapeCount r.verifier.stateCount (r.fuel+1)) +
      3*r.verifier.stateCount+1 ≤
      3*r.measure^2*(1+r.measure*(36*r.measure^3))+3*r.measure+1 := by gcongr
  have hn6 : 5*r.witnessLength+2 ≤ 7*r.measure^6 := by omega
  nlinarith

/-- Native formula clause count, with global coefficient and degree. -/
theorem requestFormula_length (r : CNFCompilationRequest) :
    (requestFormula r).length ≤ 512*r.measure^6 := by
  have hc := circuitCNF_length (requestCircuit r)
  have hs := requestCircuit_polynomial r
  have hn := (request_parameters_le r).2.2.2.2
  have hm := request_measure_positive r
  have hpow : r.measure ≤ r.measure^6 := Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ r.measure^6 := one_le_pow₀ hm
  change (requestFormula r).length ≤ _ at hc
  omega

/-- proof of `lem:multitape-refuter`, Step 3: fixed degree-36 balanced native payload bound. -/
theorem requestFormula_bits (r : CNFCompilationRequest) :
    natBitLength (RecoveryOracle.sourceSATCode (requestFormula r)) ≤
      (16000*130^6)*r.measure^36 := by
  have hb := circuitSATCode_bits (requestCircuit r)
  have hs := requestCircuit_polynomial r
  have hn := (request_parameters_le r).2.2.2.2
  have hm := request_measure_positive r
  have hpow : r.measure ≤ r.measure^6 := Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ r.measure^6 := one_le_pow₀ hm
  have hsum : r.witnessLength+(requestCircuit r).size+1 ≤ 130*r.measure^6 := by omega
  change natBitLength (RecoveryOracle.sourceSATCode (requestFormula r)) ≤ _ at hb
  calc
    _ ≤ 16000*(r.witnessLength+(requestCircuit r).size+1)^6 := hb
    _ ≤ 16000*(130*r.measure^6)^6 := by gcongr
    _ = _ := by ring

end NearCubicGates.Adapters.Compile
