import Proof.CaseAnalysis.CaseTwoExecution
import Proof.CaseAnalysis.CaseTwoBudget
import Proof.CaseAnalysis.CaseTwoWholeBudget

/-! The full cold converter and every fixed original PCPP block have one
C.12 polynomial. All source, hierarchy and copy parameters precede its constants. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RepairSource.ProjectionNormalization OuterPCPRecovery RecoveryScheduleEnvelope PolynomialClock
open PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem FixedFold.budget_uniform (cost : ℕ→ℕ) (copies M : ℕ)
    (h : ∀ n<copies,cost n≤M) : FixedFold.budget cost copies≤1+copies*(1+M):=by
  induction copies with
  | zero => simp [FixedFold.budget]
  | succ n ih =>
    have hi:=ih (fun j hj=>h j (Nat.lt_succ_of_lt hj))
    have hn:=h n (Nat.lt_succ_self n)
    dsimp only [FixedFold.budget]
    rw [Nat.succ_mul]
    omega

namespace Execution
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)

theorem frame_budget_bound (r : InputRequest) :
    HierarchyFrame.budget (List.ofFn r.2) (H.time r.1).bits≤
      12*r.1+12*WholeBudgetHierarchy.clockScale H r.1+21:=by
  have hb:=PCPPQueryBounds.bits_le (H.time r.1)
  simp only [HierarchyFrame.budget,HierarchyFrame.rawBudget,List.length_append,
    frame_length,List.length_ofFn]
  dsimp only [WholeBudgetHierarchy.clockScale]
  omega

theorem budget_polynomial (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad)
    (degree D copies : ℕ) : ∃ C E : ℕ,1≤C ∧
      ∀ (r : InputRequest)
        (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)),
        oracle.size≤oracleSizeBound degree
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
        ∀ (target : ℕ) (point : BitInput target),
        (a.output (WholeBlock.request source a H Cpad hpad r oracle)).clauseBits≤
          CloseoutLanguage.clauseWidth D (WholeBlock.request source a H Cpad hpad r oracle).arity →
        budget source a H Cpad hpad r oracle
          (oracleSizeBound degree (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
            (VerifierEncoding.code H.verifier) r.2)) D copies point≤C*(r.1+2^target+1)^E:=by
  obtain ⟨Cc,Ec,_,hcold⟩:=ColdBudget.polynomial
  obtain ⟨Cb,Eb,_,hblock⟩:=WholeBudget.polynomial source a H Cpad hcoeff hpad degree D copies
  let W:=WholeBudgetHierarchy.width source H Cpad
  let O:=WholeBudgetHierarchy.oracleSize source H Cpad degree
  let F:=fun n=>(Cc*(W n+O n+1)^Ec+1+(12*n+12*WholeBudgetHierarchy.clockScale H n+21))+1+
    (1+copies*(1+Cb*(n+1)^Eb))
  have hz:=WholeBudgetHierarchy.clock_polynomial H
  have hw : SourcePoly W:=hz.const_mul (HierarchySourceCost.widthCoefficient source H Cpad)
  have ho : SourcePoly O:=sourcePoly_pow (hw.add (polyDominated_const 1)) (2^oracleDepth degree)
  have hcp:=(sourcePoly_pow ((hw.add ho).add (polyDominated_const 1)) Ec).const_mul Cc
  have hfp:=((sourcePoly_id.const_mul 12).add (hz.const_mul 12)).add (polyDominated_const 21)
  have hbp:=(sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1)) Eb).const_mul Cb
  have hfold:=(polyDominated_const 1).add (((polyDominated_const 1).add hbp).const_mul copies)
  have hF : SourcePoly F:=(((hcp.add (polyDominated_const 1)).add hfp).add
    (polyDominated_const 1)).add hfold
  obtain ⟨E,C,hC⟩:=hF
  refine ⟨C+1,E,by omega,fun r oracle hs target point hcb=>?_⟩
  let R:=PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2
  let B:=oracleSizeBound degree R
  have hR : R≤W r.1:=by
    obtain ⟨_,he,_⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
    dsimp only [R,PCPPNativeHierarchyNodes.width]
    rw [he]
    exact HierarchySourceCost.width_bound source H Cpad hcoeff hpad r.1
  have hB : B≤O r.1:=by
    have hb:=pairIter_add_one_le_pow (oracleDepth degree) R
    have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) (2^oracleDepth degree)
    change pairIter (oracleDepth degree) R≤(W r.1+1)^(2^oracleDepth degree)
    omega
  have hc : Cold.budget B oracle≤Cc*(W r.1+O r.1+1)^Ec:=
    (hcold R B oracle hs).trans (Nat.mul_le_mul_left Cc (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add hR hB) 1) Ec))
  have hf:=frame_budget_bound H r
  have hcost : ∀ n<copies,XorFamily.cost source a H Cpad hpad r oracle D point n≤Cb*(r.1+1)^Eb:=by
    intro n hn
    apply hblock r oracle hs n _ _ _ _ hn.le
    exact Nat.add_sub_of_le hcb
  have hsum:=FixedFold.budget_uniform (XorFamily.cost source a H Cpad hpad r oracle D point)
    copies (Cb*(r.1+1)^Eb) hcost
  have htotal : budget source a H Cpad hpad r oracle B D copies point≤F r.1:=by
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hc 1) hf) 1) hsum
  exact htotal.trans ((hC r.1).trans ((Nat.mul_le_mul_right _ (by omega : C≤C+1)).trans
    (Nat.mul_le_mul_left (C+1) (Nat.pow_le_pow_left
      (show r.1+1≤r.1+2^target+1 from Nat.add_le_add_right (Nat.le_add_right _ _) 1) E))))

end Execution
end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo
