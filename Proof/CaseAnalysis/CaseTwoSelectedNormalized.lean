import Proof.CaseAnalysis.CaseTwoPolynomial
import Proof.CaseAnalysis.CaseTwoLive
import Proof.CaseAnalysis.CaseTwoHardness
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual

/-! The physical Case2 request is the same global normalized source request.
The original hierarchy input is transported by the checked exact dimension
identity; duplicate deletion is idempotent on the same ordered clause list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RepairSource.ProjectionNormalization RecoveryScheduleEnvelope RecoveryPipeline OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem compact_request (a : PointwisePCPPAlgorithm) {n r Q : ℕ}
    (oracle : BooleanCircuit n) (projections : Fin Q→Fin n→ProjectedRandomBit r)
    (formula : ThreeCNF Q) :
    PCPPSubstitution.sourceRequest a oracle projections (compactThreeCNF formula)=
      PCPPSubstitution.sourceRequest a oracle projections formula := by
  simp only [PCPPSubstitution.sourceRequest,PCPPSubstitution.compactSubstituted,
    compactThreeCNF,List.dedup_idem]

def pcp (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad) :=
  RecoveryCaseOnePaddedBit.pcp source H Cpad hpad
def request (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
    {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (oracle : BooleanCircuit ((pcp source H Cpad hpad).nativeWidth r.1)) :=
  PCPPSubstitution.sourceRequest a oracle ((pcp source H Cpad hpad).queryAddressBits r.2)
    ((pcp source H Cpad hpad).decision r.2 (fun _=>false))

def localRequest {M : TimedDecisionMachine} {T : ℕ→ℕ} (a : PointwisePCPPAlgorithm)
    (p : ProjectionPCP M T) (r : InputRequest) (oracle : BooleanCircuit (p.nativeWidth r.1)) :=
  PCPPSubstitution.sourceRequest a oracle (p.queryAddressBits r.2) (p.decision r.2 (fun _=>false))

def receipt {M : TimedDecisionMachine} {T : ℕ→ℕ}
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
    {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad degree D copies C E : ℕ)
    (r : InputRequest) (p : ProjectionPCP M T) : Prop :=
  ∀ (oracle : BooleanCircuit (p.nativeWidth r.1)),
    oracle.size ≤ oracleSizeBound degree (p.nativeWidth r.1) →
    ∀ (target : ℕ) (point : BitInput target)
      (hcb : (a.output (localRequest a p r oracle)).clauseBits ≤
        CloseoutLanguage.clauseWidth D (localRequest a p r oracle).arity)
      (hfit : copies*((localRequest a p r oracle).arity+
        CloseoutLanguage.clauseWidth D (localRequest a p r oracle).arity+1) ≤ target),
    ∃ out,ClockJoin.ReadyRun
      (Execution.machine source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (C*(r.1+2^target+1)^E)
      (Execution.input source a k D copies (HierarchySourceInput.hierarchyInput H r)
        (frame (canonicalBoundedCircuitDescription (oracleSizeBound degree (p.nativeWidth r.1)) oracle))
        (frame (List.ofFn point)) (p.nativeWidth r.1) (oracleSizeBound degree (p.nativeWidth r.1))) out ∧
      out (Execution.outputSlot source a k D copies)=
        [padCore (xorPower (CloseoutLanguage.paddedUnsigned
          (a.output (localRequest a p r oracle)) hcb) copies) hfit point] ∧
      out (Execution.old source a k D copies 0)=HierarchySourceInput.hierarchyInput H r ∧
      out (Execution.old source a k D copies 1)=
        frame (canonicalBoundedCircuitDescription (oracleSizeBound degree (p.nativeWidth r.1)) oracle) ∧
      out (Execution.old source a k D copies 2)=frame (List.ofFn point)

theorem normalized_polynomial_run
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
    {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (degree D copies : ℕ) (hD : 1 ≤ D) :
    ∃ C E : ℕ,1 ≤ C ∧ ∀ (r : InputRequest)
      (oracle : BooleanCircuit ((pcp source H Cpad hpad).nativeWidth r.1)),
      oracle.size ≤ oracleSizeBound degree ((pcp source H Cpad hpad).nativeWidth r.1) →
      ∀ (target : ℕ) (point : BitInput target)
        (hcb : (a.output (request source a H Cpad hpad r oracle)).clauseBits ≤
          CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity)
        (hfit : copies*((request source a H Cpad hpad r oracle).arity+
          CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity+1) ≤ target),
      let req:=request source a H Cpad hpad r oracle
      let R:=(pcp source H Cpad hpad).nativeWidth r.1
      let B:=oracleSizeBound degree R
      let hierarchy:=HierarchySourceInput.hierarchyInput H r
      let description:=frame (canonicalBoundedCircuitDescription B oracle)
      let address:=frame (List.ofFn point)
      ∃ out,ClockJoin.ReadyRun
        (Execution.machine source a k D copies H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (C*(r.1+2^target+1)^E)
        (Execution.input source a k D copies hierarchy description address R B) out ∧
        out (Execution.outputSlot source a k D copies)=
          [padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output req) hcb) copies) hfit point] ∧
        out (Execution.old source a k D copies 0)=hierarchy ∧
        out (Execution.old source a k D copies 1)=description ∧
        out (Execution.old source a k D copies 2)=address := by
  obtain ⟨C,E,hC,run⟩:=Execution.polynomial_run source a H Cpad hcoeff hpad degree D copies hD
  refine ⟨C,E,hC,fun r=>?_⟩
  have actual : receipt source a H Cpad degree D copies C E r
      (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad) := by
    intro oracle ho target point hcb hfit
    exact run r oracle ho target point hcb hfit
  rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r] at actual
  intro oracle ho target point
  have heq : request source a H Cpad hpad r oracle=
      localRequest a (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r) r oracle :=
    compact_request a oracle _ _
  dsimp only
  rw [heq]
  exact actual oracle ho target point

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
