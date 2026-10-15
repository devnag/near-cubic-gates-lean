import Proof.CaseAnalysis.CaseTwoWholeBudgetLocal
import Proof.CaseAnalysis.CaseTwoWholeBudgetHierarchy

/-! One fixed polynomial for the actual original Case 2 block, its complete
reset and the bridge/XOR step. All coefficients are chosen after the fixed
source, hierarchy clock, oracle degree and copy schedule. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudget
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem request_source_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    RequestSource.budget a r≤2*PCPPSourceCache.totalBudget a r+8*(pcppInput r).length+16 := by
  have hb:=PCPPSourceCache.budget_bound a r
  unfold PCPPSourceCache.budget PCPPRequestSource.budget at hb
  unfold RequestSource.budget RequestInput.budget SourceCache.budget SourceCall.budget
  omega

theorem measure_parameter (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    r.circuit.size+r.arity≤ measure a r := by
  have hd : PCPPQueryCachedBounds.degree a≠0 := by
    unfold PCPPQueryCachedBounds.degree
    omega
  have hp:=Nat.le_self_pow hd (r.circuit.size+r.arity+1)
  have hc:=PCPPQueryCachedBounds.coefficient_pos a
  have hm:=Nat.mul_le_mul_right ((r.circuit.size+r.arity+1)^PCPPQueryCachedBounds.degree a) hc
  unfold measure PCPPQueryCachedBounds.capacity
  omega

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
  (Cpad : ℕ)

theorem original_source_bound (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    let req:=WholeBlock.request source a H Cpad hpad r oracle
    OriginalSource.budget source a H Cpad hpad r oracle≤
      2*PCPPNativeHierarchySource.originalBudget source a H Cpad hpad r oracle+
        4*(PCPPNative.descriptor req.circuit).length+8*(pcppInput req).length+64 := by
  dsimp only
  have hb:=request_source_bound a (WholeBlock.request source a H Cpad hpad r oracle)
  unfold OriginalSource.budget RequestDescriptor.budget
    PCPPNativeHierarchySource.originalBudget PCPPNativeClauseDescriptorConsumer.sourceBudget PCPPNativeSource.budget
  dsimp only [WholeBlock.request] at hb ⊢
  omega

theorem local_monotone (D copies : ℕ) : Monotone (localEnvelope D copies) := by
  intro M N h
  unfold localEnvelope widthEnvelope
  gcongr

def envelope (D copies M : ℕ) := 1000*(M+5)^2+2*localEnvelope D copies M

theorem polynomial_envelope (D copies : ℕ) {f : ℕ→ℕ} (hf : SourcePoly f) :
    SourcePoly (fun n=>envelope D copies (f n)) :=
  ((sourcePoly_pow (hf.add (polyDominated_const 5)) 2).const_mul 1000).add
    ((local_polynomial D copies hf).const_mul 2)

theorem block_bound (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad)
    (degree D copies : ℕ) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (horacle : oracle.size≤oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (block : ℕ) (u : BitInput (WholeBlock.request source a H Cpad hpad r oracle).arity)
    (clause : BitInput (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits)
    (position : Bool) (padding : ℕ) (hb : block≤copies)
    (hcap : (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits+padding=
      CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity) :
    2*WholeBlock.budget source a H Cpad hpad r oracle D block u clause position padding+4≤
      envelope D copies (WholeBudgetHierarchy.envelope source a H Cpad degree r.1) := by
  let req:=WholeBlock.request source a H Cpad hpad r oracle
  let M:=WholeBudgetHierarchy.envelope source a H Cpad degree r.1
  obtain ⟨hbudget,hmeasure,horacleWord,hinputWord⟩:=
    WholeBudgetHierarchy.bounds source a H Cpad degree hcoeff hpad r oracle horacle
  change measure a req≤M at hmeasure
  have hN:= (measure_parameter a req).trans hmeasure
  have hlen:=(components a req).2.2.1
  have hlen' : (pcppInput req).length≤3*M+3 := by omega
  have hdesc:=(PCPPNative.descriptor_length_bound req.circuit).trans
    (Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left (by omega : req.arity+req.circuit.size+5≤M+5) 2))
  have hsrc:=original_source_bound source a H Cpad hpad r oracle
  change OriginalSource.budget source a H Cpad hpad r oracle≤
    2*PCPPNativeHierarchySource.originalBudget source a H Cpad hpad r oracle+
      4*(PCPPNative.descriptor req.circuit).length+8*(pcppInput req).length+64 at hsrc
  have hocc:=(occurrence_bound D copies block a req u clause position padding hb hcap).trans
    (local_monotone D copies hmeasure)
  change PCPPNativeHierarchySource.originalBudget source a H Cpad hpad r oracle≤M at hbudget
  change (PCPPNative.descriptor oracle).length≤M at horacleWord
  change (HierarchySourceInput.hierarchyInput H r).length≤M at hinputWord
  change 2*(SourceBlock.budget source a H Cpad hpad r oracle+1+
    Occurrence.budget D block a req u clause position padding)+4≤envelope D copies M
  unfold SourceBlock.budget CompoundInput.budget RecoveryPCPFormulaResumeSearchPair.budget envelope
  nlinarith

/-- Stronger than the reachable-input currency: the fixed hierarchy already
bounds this block polynomially in its original source length. -/
theorem polynomial (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad)
    (degree D copies : ℕ) : ∃ C E : ℕ,1≤C ∧
      ∀ (r : InputRequest)
        (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)),
        oracle.size≤oracleSizeBound degree
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
        ∀ (block : ℕ) (u : BitInput (WholeBlock.request source a H Cpad hpad r oracle).arity)
          (clause : BitInput (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits)
          (position : Bool) (padding : ℕ), block≤copies →
          (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits+padding=
            CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity →
          2*WholeBlock.budget source a H Cpad hpad r oracle D block u clause position padding+4≤
            C*(r.1+1)^E := by
  obtain ⟨E,C,hC⟩:=polynomial_envelope D copies
    (WholeBudgetHierarchy.envelope_polynomial source a H Cpad degree)
  refine ⟨C+1,E,by omega,fun r oracle ho block u clause position padding hb hc=>?_⟩
  exact (block_bound source a H Cpad hcoeff hpad degree D copies r oracle ho block u clause position padding hb hc).trans
    ((hC r.1).trans (Nat.mul_le_mul_right _ (by omega)))

theorem reachable_polynomial (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad)
    (degree D copies : ℕ) : ∃ C E : ℕ,1≤C ∧
      ∀ (r : InputRequest)
        (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)),
        oracle.size≤oracleSizeBound degree
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
        ∀ (target block : ℕ) (u : BitInput (WholeBlock.request source a H Cpad hpad r oracle).arity)
          (clause : BitInput (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits)
          (position : Bool) (padding : ℕ), block<copies →
          (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits+padding=
            CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity →
          2*WholeBlock.budget source a H Cpad hpad r oracle D block u clause position padding+4≤
            C*(r.1+2^target+1)^E := by
  obtain ⟨C,E,hC,hb⟩:=polynomial source a H Cpad hcoeff hpad degree D copies
  refine ⟨C,E,hC,fun r oracle ho target block u clause position padding hblock hcap=>?_⟩
  exact (hb r oracle ho block u clause position padding hblock.le hcap).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left
      (show r.1+1≤r.1+2^target+1 from Nat.add_le_add_right (Nat.le_add_right _ _) 1) E))

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudget
