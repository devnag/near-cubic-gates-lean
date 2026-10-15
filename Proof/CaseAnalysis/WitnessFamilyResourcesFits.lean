import Proof.CaseAnalysis.WitnessFamilyResourcesLocal

/-! One common capacity discharges every numerical family-worker premise.
All source-dependent scalar sizes are bounded by S before this application. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem mass_width (S C T : ℕ) (hc : C ≤ S) (ht : T ≤ S) :
    natBitLength C ≤ S+1 ∧ width T (natBitLength C) ≤ (S+2)^2 := by
  have hb: natBitLength C ≤ S+1 := (PCPPQueryCost.width_le C).trans (by omega)
  refine ⟨hb,?_⟩
  unfold width
  have hmul:=Nat.mul_le_mul (by omega : T+1 ≤ S+2) (by omega : natBitLength C+1 ≤ S+2)
  nlinarith

theorem mass_costs (S B k : ℕ) (hb : B ≤ (S+2)^2) (hk : k ≤ S) :
    MassStep.budget B+1 ≤ 100000*(S+2)^4 ∧
      CompetitorReusableDecision.capacity B+1 ≤ 100000*(S+2)^4 ∧
      MassCheck.budget B k+1 ≤ 100000*(S+2)^4 ∧
      bootstrapBudget B ≤ 100000*(S+2)^4 := by
  have hpos:1 ≤ (S+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hsq:(B+1)^2 ≤ 4*(S+2)^4 := by
    have h:=Nat.pow_le_pow_left (by omega : B+1 ≤ 2*(S+2)^2) 2
    norm_num [mul_pow,←pow_mul] at h
    exact h
  have hp2:(S+2)^2 ≤ (S+2)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1:S+2 ≤ (S+2)^4 := Nat.le_self_pow (by decide) _
  have h4:1 ≤ (S+2)^4 := Nat.one_le_pow _ _ (by omega)
  unfold MassStep.budget MassPrepare.budget Mass.tailBudget MassCheck.budget
    CompetitorThresholdAmbient.budget CompetitorThresholdConstants.budget
    bootstrapBudget CompetitorReusableDecision.capacity CompetitorRationalDecision.width
  omega

theorem capacity_parts (S : ℕ) :
    3*(S+2) ≤ capacity S ∧ 2*parser S ≤ capacity S ∧
      200*(S+2)^2 ≤ capacity S ∧ 100000*(S+2)^4 ≤ capacity S ∧
      CloseoutRowsCircuitCapacity.capacity S ≤ capacity S := by
  have h1:S+2 ≤ (S+2)^26 := Nat.le_self_pow (by decide) _
  have h2:(S+2)^2 ≤ (S+2)^26 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4:(S+2)^4 ≤ (S+2)^26 := Nat.pow_le_pow_right (by omega) (by decide)
  have h24:(S+2)^24 ≤ (S+2)^26 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold capacity parser CloseoutRowsCircuitCapacity.capacity
  omega

structure Fits (P V C T k : ℕ) (bits arity : List Bool) : Prop where
  circuit : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P
  raw : 2*bits.length+1 ≤ P
  header : FamilyCount.budget bits V+1 ≤ P
  guard : ∀ field∈FamilyFields.words bits,SumGuard.budget field arity T+1 ≤ P
  append : ∀ field∈FamilyFields.words bits,EquationHeaderAppend.budget (SumFields.count field)+1 ≤ P
  read : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,
    TermCoefficient.budget C term+1 ≤ P
  coefficientWidth : natBitLength C ≤ P
  mass : MassStep.budget (width T (natBitLength C))+1 ≤ P
  bits : 2*natBitLength C+1 ≤ P
  native : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P
  check : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P
  bootstrap : bootstrapBudget (width T (natBitLength C)) ≤ P

theorem fits (S P V C T k : ℕ) (bits arity : List Bool)
    (hp : capacity S ≤ P) (hlen : bits.length ≤ S) (ha : arity.length ≤ S)
    (hc : C ≤ S) (ht : T ≤ S) (hk : k ≤ S) : Fits P V C T k bits arity := by
  obtain ⟨hraw,hparser,happend,hmass,hcircuit⟩:=capacity_parts S
  obtain ⟨hw,hB⟩:=mass_width S C T hc ht
  obtain ⟨hm,hn,hk',hb⟩:=mass_costs S _ k hB hk
  have fieldLength (field : List Bool) (hf : field∈FamilyFields.words bits) : field.length ≤ S :=
    (FamilyMode.field_width bits field hf).le.trans hlen
  refine ⟨?_,by omega,?_,?_,?_,?_,by omega,hm.trans (hmass.trans hp),by omega,
    hn.trans (hmass.trans hp),hk'.trans (hmass.trans hp),hb.trans (hmass.trans hp)⟩
  · exact (show CloseoutRowsCircuitCapacity.capacity bits.length ≤
      CloseoutRowsCircuitCapacity.capacity S by unfold CloseoutRowsCircuitCapacity.capacity;gcongr).trans
      (hcircuit.trans hp)
  · have h:=header S V bits hlen
    omega
  · intro field hf
    have h:=guard S T field arity (fieldLength field hf) ha
    omega
  · intro field hf
    exact (append S field (fieldLength field hf)).trans (happend.trans hp)
  · intro field hf term ht'
    have hterm:term.length ≤ S := (FamilyMode.term_width field term ht').le.trans (fieldLength field hf)
    exact (coefficient S C term hterm hc).trans (hparser.trans hp)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
