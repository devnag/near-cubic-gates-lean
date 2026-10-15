import Proof.CaseAnalysis.RowsGateGuardMeaning

/-! Total public supported-gate decision and retained native request from
the original raw code plus the existing source-domain template. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
open LocalBitMultitape CanonicalBinary CanonicalWitnessCodec SupplierPipeline RadixSemantics
open RecoveryRootRound CloseoutRowsGatePairHeads CloseoutRowsGateRawRun CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Output (compressed : Bool) (core : ℕ) (bits : List Bool) (out : Fin 1038 → List Bool) : Prop :=
  out 1035=UnaryTemplate.tape core ∧
    (readTapeBit (out 1037) 0=true ↔ (decodeSupportedNormalizedGate core (value bits)).isSome) ∧
    ∀ g,decodeSupportedNormalizedGate core (value bits)=some g →
      out 1033=frame (CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support)
        (CloseoutRowsGateCold.signSource bits) g.gate.threshold.natAbs)

theorem reject_run (compressed : Bool) (core : ℕ) (bits : List Bool) (old : Fin 1035 → List Bool)
    (hr : ClockJoin.ReadyRun (CloseoutRowsGateCold.actualMachine compressed)
      (CloseoutRowsGateRawRun.budget bits) (CloseoutRowsGateCold.input bits) old)
    (hf : readTapeBit (old 1018) 0=false)
    (hd : ¬(decodeSupportedNormalizedGate core (value bits)).isSome) :
    ∃ out,ReadyAt (machine compressed) (budget bits) heads (input core bits) out ∧ Output compressed core bits out := by
  have stopped := rejected (first compressed) second (fun scanned => scanned 1018) _ heads _ _
    (first_run compressed core bits old hr) hf
  have more := enlarge _ _ (budget bits) heads _ _ stopped (by unfold budget;omega)
  refine ⟨extend core old,more,rfl,?_,?_⟩
  · constructor
    · intro h
      change false=true at h
      contradiction
    · intro h
      exact False.elim (hd h)
  · intro g hg
    exact False.elim (hd (by rw [hg];rfl))

theorem positive_run (compressed : Bool) (core : ℕ) (bits : List Bool) (old : Fin 1035 → List Bool)
    (hr : ClockJoin.ReadyRun (CloseoutRowsGateCold.actualMachine compressed)
      (CloseoutRowsGateRawRun.budget bits) (CloseoutRowsGateCold.input bits) old)
    (weights : List ℤ) (threshold : ℤ) (members : List Bool)
    (hc : Components bits weights threshold members) (hp : Produced compressed bits weights threshold members old)
    (hv : validity (CloseoutRowsGateDecisionMeaning.fields weights) members true weights.length=true) :
    ∃ out,ReadyAt (machine compressed) (budget bits) heads (input core bits) out ∧ Output compressed core bits out := by
  have joined := CloseoutRowsGatePairHeads.joined (first compressed) second (fun scanned => scanned 1018)
    _ _ heads _ _ _ (first_run compressed core bits old hr)
    (second_run core weights.length members.length old hp.2.2.1 hp.2.2.2) (by
      change readTapeBit (old 1018) 0=true
      rw [hp.2.1]
      simp only [readTapeBit,List.getD_cons_zero,hv])
  have hw : weights.length≤bits.length+1 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.list_count _ weights hc.2.1
  have hm : members.length≤bits.length+1 := by
    simpa only [CloseoutRowsGateFields.field_length] using CloseoutRowsGateRawBounds.members_count _ members hc.2.2.2
  have bound := CloseoutRowsGateCounts.budget_bound weights.length members.length core bits.length hw hm
  have more := enlarge _ _ (budget bits) heads _ _ joined (by unfold budget;omega)
  let final := install slots (extend core old) (CloseoutRowsGateCounts.output weights.length members.length core)
  have port (i : Fin 5) : final (slots i)=CloseoutRowsGateCounts.output weights.length members.length core i :=
    install_slot _ injective _ _ _
  refine ⟨final,more,port 2,?_,?_⟩
  · have flag : final 1037=CloseoutRowsGateCounts.output weights.length members.length core 4 := port 4
    rw [flag,CloseoutRowsGateCounts.decision_exact,
      CloseoutRowsGateDecisionMeaning.decision_exact core bits weights threshold members
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
    simp only [hv,and_true]
  · intro g hg
    change install slots (extend core old) _ 1033=_
    rw [install_other _ _ _ _ (by decide)]
    exact native_of_components compressed g bits weights threshold members old hg hc hp

theorem guard_run (compressed : Bool) (core : ℕ) (bits : List Bool) :
    ∃ out,ReadyAt (machine compressed) (budget bits) heads (input core bits) out ∧ Output compressed core bits out := by
  obtain ⟨old,hr,outcome⟩ := CloseoutRowsGateRawRun.allraw compressed bits
  rcases outcome with ⟨weights,threshold,members,hc,hp⟩ | ⟨hf,hn⟩
  · by_cases hv : validity (CloseoutRowsGateDecisionMeaning.fields weights) members true weights.length=true
    · exact positive_run compressed core bits old hr weights threshold members hc hp hv
    · apply reject_run compressed core bits old hr
      · rw [hp.2.1]
        simp [readTapeBit,hv]
      · intro hd
        exact hv ((CloseoutRowsGateDecisionMeaning.decision_exact core bits weights threshold members
          hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).mp hd).2.2
  · apply reject_run compressed core bits old hr
    · rw [hf];rfl
    · exact fun hd => hn (decoded_exists core bits hd)

theorem budget_bound (bits : List Bool) : budget bits ≤ 4000000000000000000001020*(bits.length+2)^26 := by
  have raw := CloseoutRowsGateRawRun.budget_bound bits
  have one : 1≤(bits.length+2)^26 := Nat.one_le_pow _ _ (by omega)
  have linear : bits.length+2≤(bits.length+2)^26 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (n := bits.length+2) (by omega) (show 1≤26 by decide)
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateGuard
