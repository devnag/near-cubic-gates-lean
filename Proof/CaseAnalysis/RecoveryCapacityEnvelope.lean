import Proof.CaseAnalysis.RecoveryWorkspacePolynomial
import Proof.PCP.PCPPNativeCanonicalTreeWeight
import Proof.CaseAnalysis.CaseTwoWholeBudgetHierarchy
import Proof.CaseAnalysis.CapacityBudget
import Proof.CaseAnalysis.CloseoutRecoveryBudget

/-! The recovery capacity is indexed by final language length.  Its scalar
majorant uses x=2^n; the original randomness table is paid only once through
2^R <= 2^n.  No exponential in the refuter input length is introduced. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCapacity
open RepairOrdinary ProjectionNormalization SourceInterfaces OuterPCPRecovery RecoveryScheduleEnvelope
open PaddedRunnerBudgetClosure R1Leaf56BalancedAtomCodeLedger
open R1Leaf56StructuralGateBudgetEnvelope CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def width (x : ℕ) := natBitLength x
def fullBound (degree x : ℕ) := (width x+1)^(2^oracleDepth degree)

theorem width_polynomial : SourcePoly width := by
  apply (sourcePoly_id.add (polyDominated_const 1)).mono
  intro x
  exact PCPPQueryCost.width_le x

theorem table_polynomial : SourcePoly (fun x=>2^width x) := by
  apply ((sourcePoly_id.add (polyDominated_const 1)).const_mul 2).mono
  intro x
  exact (PCPPNativeCanonicalTree.bits_pow_upper x).trans
    (Nat.mul_le_mul_left 2 (by omega : max 1 x ≤ x+1))

theorem fullBound_polynomial (degree : ℕ) : SourcePoly (fullBound degree) :=
  sourcePoly_pow (width_polynomial.add (polyDominated_const 1)) _

theorem workspace_mono {R R' B B' Q Q' L L' : ℕ}
    (hr : R ≤ R') (hb : B ≤ B') (hq : Q ≤ Q') (hl : L ≤ L') :
    originalWorkspace R B Q L ≤ originalWorkspace R' B' Q' L' := by
  unfold originalWorkspace workspace structuralGateEnvelope fixedCountEnvelope
    rowBudgetEnvelope outputEnvelope nodeEnvelope grammarEnvelope rowEnvelope
    atomEnvelope boundedCircuitFieldLimit
  gcongr
  decide

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
  {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)

def clockUpper (x : ℕ) := H.coefficient*((x+1)^(k+2)+1)+2
def sourceUpper (x : ℕ) :=
  HierarchyStreamCost.sizeCoefficient source H Cpad*(x+1)^HierarchySourceCost.inputExponent source*
    (clockUpper H x)^HierarchyStreamCost.logBase source

theorem sourceUpper_polynomial : SourcePoly (sourceUpper source H Cpad) := by
  have hx:=sourcePoly_id.add (polyDominated_const 1)
  have hc : SourcePoly (clockUpper H) :=
    (((sourcePoly_pow hx (k+2)).add (polyDominated_const 1)).const_mul H.coefficient).add
      (polyDominated_const 2)
  exact ((sourcePoly_pow hx (HierarchySourceCost.inputExponent source)).const_mul
    (HierarchyStreamCost.sizeCoefficient source H Cpad)).mul
      (sourcePoly_pow hc (HierarchyStreamCost.logBase source))

theorem source_bound (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (x : ℕ) (hr : r.1 ≤ x) :
    (source.output (HierarchyEncode.encode H Cpad r)).word.length+
      HierarchyProjection.width source H Cpad r.1+HierarchyProjection.queries source H Cpad r.1+1 ≤
        sourceUpper source H Cpad x := by
  have h:=HierarchyStreamCost.size_bound source H Cpad hcoeff hpad r
  have ht : H.time r.1 ≤ H.coefficient*((x+1)^(k+2)+1) := by
    change H.coefficient*(r.1^(k+2)+1) ≤ H.coefficient*((x+1)^(k+2)+1)
    gcongr
    omega
  have hc : natBitLength (H.time r.1)+1 ≤ clockUpper H x := by
    have hw:=PCPPQueryCost.width_le (H.time r.1)
    unfold clockUpper
    omega
  apply h.trans
  unfold sourceUpper
  gcongr

def majorant (degree x : ℕ) :=
  originalWorkspace (width x) (fullBound degree x)
    (sourceUpper source H Cpad x) ((2*sourceUpper source H Cpad x)^3)+
      1024*(sourceUpper source H Cpad x+1)^3+2^width x+x+1

theorem majorant_polynomial (degree : ℕ) : SourcePoly (majorant source H Cpad degree) := by
  have hs:=sourceUpper_polynomial source H Cpad
  have hc:=sourcePoly_pow (hs.const_mul 2) 3
  have hw:=CloseoutRecoveryWorkspacePolynomial.original_workspace width_polynomial
    (fullBound_polynomial degree) hs hc table_polynomial
  exact (((hw.add ((sourcePoly_pow (hs.add (polyDominated_const 1)) 3).const_mul 1024)).add
    table_polynomial).add sourcePoly_id).add (polyDominated_const 1)

/-- Fixed constants for the existing physical W producer. -/
theorem exists_capacity (degree : ℕ) : ∃ A B : ℕ, ∀ n,
    majorant source H Cpad degree (2^n) ≤ CloseoutCapacity.capacity A B n := by
  obtain ⟨d,c,hc⟩:=majorant_polynomial source H Cpad degree
  let e:=natBitLength c+2*d+1
  refine ⟨e,e,fun n=>?_⟩
  apply (hc (2^n)).trans
  apply (Closeout.recovery_budget c d n).trans
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have hm : max 1 n ≤ n+1 := by omega
  change e*max 1 n ≤ e*n+e
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutRecoveryCapacity
