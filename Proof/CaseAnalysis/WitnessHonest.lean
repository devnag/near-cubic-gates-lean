import Proof.CaseAnalysis.WitnessFibers
import Proof.CaseAnalysis.WitnessRestriction

/-! The honest C.10 witness: select redundant padding, restrict the actual
source terms, then average only occurrences of the same proof variable. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Honest
open SourceInterfaces CanonicalWitnessCodec ExecutableInterfaces SupplierPipeline
open ComponentwiseCircuitRestriction OccurrenceSliceTransport OuterPCPRecovery
open RepairRepresentation SupplierEstimator
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem family_from_restrictions {Circuit : CanonicalWitnessCodec.CircuitFamily}
    (evaluate : {n : ℕ}→Circuit n→BitInput n→Bool)
    (wires description : {n : ℕ}→Circuit n→ℕ)
    (source : PointwisePCPPAlgorithm) (request : PCPPRequest source.minimumArity)
    (r : ℕ) (hr : (source.output request).clauseBits ≤ r)
    (ts : List (LegalCircuitTerm Circuit (request.arity+r+1)))
    (J B : ℕ) (A : ℚ) (W L : ℕ)
    (hA : 0 ≤ A) (hj : ts.length ≤ J) (hm : Average.mass ts ≤ A)
    (hc : ∀ t∈ts,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (restrictAtom : BitInput (r-(source.output request).clauseBits)→
      Fibers.Slot (source.output request)→Circuit (request.arity+r+1)→Circuit request.arity)
    (hw : ∀ padding slot t,t∈ts→wires (restrictAtom padding slot t.circuit) ≤ W)
    (hl : ∀ padding slot t,t∈ts→description (restrictAtom padding slot t.circuit) ≤ L)
    (heval : ∀ padding slot atom u,evaluate (restrictAtom padding slot atom) u=
      evaluate atom (Padding.extend hr padding
        (occurrenceAddress u (bitInputIndexEquiv (source.output request).clauseBits slot.1) slot.2)))
    (h0 : ∀ x,0 ≤ Average.value evaluate ts x)
    (h1 : ∀ x,Average.value evaluate ts x ≤ 1) :
    ∃ family : SumFamily Circuit wires description
      (Average.limits request.arity J B (2*2^(source.output request).clauseBits) A W L)
      ((source.output request).systematicBits+(source.output request).auxiliaryBits),
      CompetitorSourceAverage.honestError source request (family.value evaluate) ≤
        l1DistanceFromBoolean
          (fun x=>unsignedHonest (source.output request) (projectPaddedOccurrenceInput hr x))
          (Average.value evaluate ts) ∧
      ∀ u i,0 ≤ family.value evaluate u i ∧ family.value evaluate u i ≤ 1 := by
  classical
  obtain ⟨padding,hpadding⟩:=Padding.exists_restriction hr (unsignedHonest (source.output request))
    (Average.value evaluate ts)
  let atSlot := fun slot=>ts.map (mapLegalCircuitTerm (restrictAtom padding slot))
  have hj' : ∀ slot,(atSlot slot).length ≤ J := by intro slot;simpa only [atSlot,List.length_map] using hj
  have hm' : ∀ slot,Average.mass (atSlot slot) ≤ A := by
    intro slot
    exact (Restriction.map_mass _ ts).le.trans hm
  have hc' : ∀ slot,∀ t∈atSlot slot,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B := by
    intro slot t ht
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ht
    exact hc a ha
  have hw' : ∀ slot,∀ t∈atSlot slot,wires t.circuit ≤ W := by
    intro slot t ht
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ht
    exact hw padding slot a ha
  have hl' : ∀ slot,∀ t∈atSlot slot,description t.circuit ≤ L := by
    intro slot t ht
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ht
    exact hl padding slot a ha
  let family:=Fibers.family (source.output request) wires description atSlot J B A W L
    hA hj' hm' hc' hw' hl'
  have hv : family.value evaluate=averagedValue (source.output request)
      (fun x=>Average.value evaluate ts (Padding.extend hr padding x)) := by
    funext u i
    rw [Fibers.family_value]
    unfold averagedValue
    congr 1
    funext slot
    exact Restriction.map_value evaluate (restrictAtom padding slot)
      (fun u=>Padding.extend hr padding
        (occurrenceAddress u (bitInputIndexEquiv (source.output request).clauseBits slot.1) slot.2))
      (heval padding slot) ts u
  refine ⟨family,?_,?_⟩
  · rw [hv,honestError_eq_distance source request _ (fun _=>h0 _) (fun _=>h1 _)]
    exact hpadding
  · rw [hv]
    exact averagedValue_unit (source.output request) _ (fun _=>h0 _) (fun _=>h1 _)

theorem symmetric_family (source : PointwisePCPPAlgorithm)
    (request : PCPPRequest source.minimumArity) (r : ℕ)
    (hr : (source.output request).clauseBits ≤ r)
    (ts : List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit (request.arity+r+1)))
    (J B : ℕ) (A : ℚ) (W L : ℕ)
    (hA : 0 ≤ A) (hj : ts.length ≤ J) (hm : Average.mass ts ≤ A)
    (hc : ∀ t∈ts,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (hw : ∀ t∈ts,t.circuit.wireCount ≤ W) (hl : ∀ t∈ts,t.circuit.descriptionBits ≤ L)
    (h0 : ∀ x,0 ≤ Average.value NormalizedSymmetricThresholdCircuit.eval ts x)
    (h1 : ∀ x,Average.value NormalizedSymmetricThresholdCircuit.eval ts x ≤ 1) :
    ∃ family : SumFamily NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount NormalizedSymmetricThresholdCircuit.descriptionBits
      (Average.limits request.arity J B (2*2^(source.output request).clauseBits) A W
        (restrictedSymmetricDescriptionCap request.arity (request.arity+r+1) (2^L) W))
      ((source.output request).systematicBits+(source.output request).auxiliaryBits),
      CompetitorSourceAverage.honestError source request (family.value NormalizedSymmetricThresholdCircuit.eval) ≤
        l1DistanceFromBoolean
          (fun x=>unsignedHonest (source.output request) (projectPaddedOccurrenceInput hr x))
          (Average.value NormalizedSymmetricThresholdCircuit.eval ts) ∧
      ∀ u i,0 ≤ family.value NormalizedSymmetricThresholdCircuit.eval u i ∧
        family.value NormalizedSymmetricThresholdCircuit.eval u i ≤ 1 := by
  apply family_from_restrictions _ _ _ source request r hr ts J B A W _ hA hj hm hc
    (fun padding slot=>Restriction.symmetric hr padding
      (bitInputIndexEquiv (source.output request).clauseBits slot.1) slot.2) ?_ ?_ ?_ h0 h1
  · intro padding slot t ht
    exact (restrictNormalizedSymmetricCircuit_wireCount_le _ _ _).trans (hw t ht)
  · intro padding slot t ht
    exact restrictNormalizedSymmetricCircuit_descriptionBits_le_of_source _ _ _ (hw t ht) (hl t ht)
  · intro padding slot atom u
    exact Restriction.symmetric_value hr padding _ _ atom u

theorem threshold_family (source : PointwisePCPPAlgorithm)
    (request : PCPPRequest source.minimumArity) (r : ℕ)
    (hr : (source.output request).clauseBits ≤ r)
    (ts : List (LegalCircuitTerm NormalizedThresholdThresholdCircuit (request.arity+r+1)))
    (J B : ℕ) (A : ℚ) (W L : ℕ)
    (hA : 0 ≤ A) (hj : ts.length ≤ J) (hm : Average.mass ts ≤ A)
    (hc : ∀ t∈ts,t.coefficient.num.natAbs ≤ B ∧ t.coefficient.den ≤ B)
    (hw : ∀ t∈ts,t.circuit.wireCount ≤ W) (hl : ∀ t∈ts,t.circuit.descriptionBits ≤ L)
    (h0 : ∀ x,0 ≤ Average.value NormalizedThresholdThresholdCircuit.eval ts x)
    (h1 : ∀ x,Average.value NormalizedThresholdThresholdCircuit.eval ts x ≤ 1) :
    ∃ family : SumFamily NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount NormalizedThresholdThresholdCircuit.descriptionBits
      (Average.limits request.arity J B (2*2^(source.output request).clauseBits) A W
        (restrictedThresholdDescriptionCap request.arity (request.arity+r+1) (2^L) L))
      ((source.output request).systematicBits+(source.output request).auxiliaryBits),
      CompetitorSourceAverage.honestError source request (family.value NormalizedThresholdThresholdCircuit.eval) ≤
        l1DistanceFromBoolean
          (fun x=>unsignedHonest (source.output request) (projectPaddedOccurrenceInput hr x))
          (Average.value NormalizedThresholdThresholdCircuit.eval ts) ∧
      ∀ u i,0 ≤ family.value NormalizedThresholdThresholdCircuit.eval u i ∧
        family.value NormalizedThresholdThresholdCircuit.eval u i ≤ 1 := by
  apply family_from_restrictions _ _ _ source request r hr ts J B A W _ hA hj hm hc
    (fun padding slot=>Restriction.threshold hr padding
      (bitInputIndexEquiv (source.output request).clauseBits slot.1) slot.2) ?_ ?_ ?_ h0 h1
  · intro padding slot t ht
    exact (restrictNormalizedThresholdCircuit_wireCount_le _ _ _).trans (hw t ht)
  · intro padding slot t ht
    exact restrictNormalizedThresholdCircuit_descriptionBits_le_of_source _ _ _ (hl t ht)
  · intro padding slot atom u
    exact Restriction.threshold_value hr padding _ _ atom u

end NearCubicWires.RepairOrdinary.CloseoutWitness.Honest
