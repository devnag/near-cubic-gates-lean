import Proof.Foundations.RepresentationSourceContracts
import Proof.Amplification.RecoveryWitnessPolicy

/-! Realize the unchanged source sum by canonical normalized circuit terms.
The exact ordered coefficient/function list is retained; averaging belongs
to the subsequent witness consumer. No legacy XOR witness is required. -/
namespace NearCubicWires.RepairSource.CloseoutSourceTerms
open SourceInterfaces SupplierPipeline CanonicalWitnessCodec CircuitRestriction RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem realize {Circuit : SupplierPipeline.CircuitFamily} {n : Nat}
    (eval : Circuit n→BoolFunction n) (wires description : Circuit n→Nat)
    (wireCap descriptionCap : Nat) (source : List (ℚ×BoolFunction n))
    (supply : ∀ term ∈ source, ∃ circuit : Circuit n,
      eval circuit=term.2 ∧ wires circuit ≤ wireCap ∧ description circuit ≤ descriptionCap) :
    ∃ terms : List (LegalCircuitTerm Circuit n),
      terms.map (fun term=>(term.coefficient,eval term.circuit))=source ∧
      ∀ term ∈ terms, wires term.circuit ≤ wireCap ∧ description term.circuit ≤ descriptionCap := by
  induction source with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons term rest ih =>
    obtain ⟨circuit,heval,hw,hd⟩:=supply term (by simp)
    obtain ⟨terms,hterms,hbounds⟩:=ih (fun term ht=>supply term (List.mem_cons_of_mem _ ht))
    refine ⟨⟨term.1,circuit⟩::terms,?_,?_⟩
    · simp only [List.map_cons,heval,hterms,Prod.mk.eta]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hw,hd⟩
      · exact hbounds t ht

theorem symmetric_terms (normalization : ThresholdNormalizationContract)
    {n wireCap : Nat} (sum : UnitIntervalCircuitSum symmetricWireFamily n wireCap) :
    ∃ terms : List (LegalCircuitTerm NormalizedSymmetricThresholdCircuit n),
      terms.map (fun term=>(term.coefficient,term.circuit.eval))=sum.terms ∧
      ∀ term ∈ terms, term.circuit.wireCount ≤ wireCap ∧
        term.circuit.descriptionBits ≤ symmetricDescriptionCap n wireCap := by
  apply realize _ _ _ _ _ sum.terms
  intro term ht
  obtain ⟨source,hwires,heval⟩:=sum.legal term ht
  obtain ⟨circuit,hvalue,hw,hparameters⟩:=normalizeSymmetricCircuit normalization source
  refine ⟨circuit,?_,hw.le.trans hwires,?_⟩
  · funext input
    rw [hvalue input,heval]
  · exact normalizedSymmetric_descriptionBits_le circuit (hw.le.trans hwires) hparameters

theorem threshold_terms (normalization : ThresholdNormalizationContract)
    {n wireCap : Nat} (sum : UnitIntervalCircuitSum thresholdWireFamily n wireCap) :
    ∃ terms : List (LegalCircuitTerm NormalizedThresholdThresholdCircuit n),
      terms.map (fun term=>(term.coefficient,term.circuit.eval))=sum.terms ∧
      ∀ term ∈ terms, term.circuit.wireCount ≤ wireCap ∧
        term.circuit.descriptionBits ≤ thresholdDescriptionCap n wireCap := by
  apply realize _ _ _ _ _ sum.terms
  intro term ht
  obtain ⟨source,hwires,heval⟩:=sum.legal term ht
  obtain ⟨circuit,hvalue,hw,hcount,hbottom,htop⟩:=existsCompressedNormalizedThresholdCircuit normalization source
  refine ⟨circuit,?_,hw.le.trans hwires,?_⟩
  · funext input
    rw [hvalue input,heval]
  · exact normalizedThreshold_descriptionBits_le circuit (hcount.trans hwires) hbottom htop

end NearCubicWires.RepairSource.CloseoutSourceTerms
