import Proof.CaseAnalysis.WitnessOracleParameter
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Proof.CaseAnalysis.WeakNativeBound

/-! A hierarchy changes only one linear scale coefficient. Both source
powers below are fixed before hierarchy k, its code, and padding are chosen. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HierarchyBudget
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open CloseoutWeakRuntime
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def coefficient {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ):=
  HierarchySourceCost.coefficient source H Cpad+HierarchyStreamCost.sizeCoefficient source H Cpad+
    logCoefficient k H.coefficient+3
def scale {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad N : ℕ):=
  coefficient source H Cpad*(N+2)
def sourceBound (T : ℕ):=T^(1+HierarchySourceCost.inputExponent source+HierarchySourceCost.logExponent source)
def sizeBound (T : ℕ):=T^(1+HierarchySourceCost.inputExponent source+HierarchyStreamCost.logBase source)

theorem components {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad N : ℕ) :
    N+2≤ scale source H Cpad N ∧ natBitLength (H.time N)+1≤ scale source H Cpad N ∧
      HierarchySourceCost.coefficient source H Cpad≤ scale source H Cpad N ∧
      HierarchyStreamCost.sizeCoefficient source H Cpad≤ scale source H Cpad N := by
  have hJ:1≤coefficient source H Cpad:=by unfold coefficient;omega
  have hNJ:N+2≤ scale source H Cpad N:=by
    simpa only [scale,one_mul] using Nat.mul_le_mul_right (N+2) hJ
  have hJscale:coefficient source H Cpad≤ scale source H Cpad N:=by
    simpa only [scale,mul_one] using Nat.mul_le_mul_left (coefficient source H Cpad) (show 1≤N+2 by omega)
  have hn:N+1<2^(N+2):=by have h:=Nat.lt_two_pow_self (n:=N+2);omega
  have clock:=clock_log_bound k H.coefficient N (N+2) (by omega) hn
  have short:=HierarchySourceScales.short_le_logScale (H.time N)
  have upper:logCoefficient k H.coefficient+2≤coefficient source H Cpad:=by unfold coefficient;omega
  have scaled:=Nat.mul_le_mul_right (N+2) upper
  refine ⟨hNJ,?_,?_,?_⟩
  · change natBitLength (H.coefficient*(N^(k+2)+1))+1≤_ at short ⊢
    dsimp only [OrdinaryHierarchy.time] at short
    unfold scale
    nlinarith
  · exact (show HierarchySourceCost.coefficient source H Cpad≤coefficient source H Cpad by unfold coefficient;omega).trans hJscale
  · exact (show HierarchyStreamCost.sizeCoefficient source H Cpad≤coefficient source H Cpad by unfold coefficient;omega).trans hJscale

theorem monomial (C X Y T e g : ℕ) (hc:C≤T) (hx:X≤T) (hy:Y≤T) : C*X^e*Y^g≤T^(1+e+g) := by
  calc
    _≤T*T^e*T^g:=Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_left hx e)) (Nat.pow_le_pow_left hy g)
    _=_:=by simp only [pow_add,pow_one]

theorem source_le {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (r : InputRequest) :
    HierarchySelectedSource.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)≤
      sourceBound source (scale source H Cpad r.1) := by
  have parts:=components source H Cpad r.1
  have bound:=HierarchySourceCost.constructor_bound source H Cpad hcoeff hpad r
  have cost:HierarchySelectedSource.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)≤
      HierarchySourceInput.constructorBudget source H Cpad r:=by
    unfold HierarchySourceInput.constructorBudget HierarchySourceInput.budget
    omega
  exact (cost.trans bound).trans (monomial _ _ _ _ _ _ parts.2.2.1 (by omega) parts.2.1)

theorem size_le {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (r : InputRequest) :
    (SelectedStreams.pcp source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)).word.length+
      SelectedOracle.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)+
      SelectedStreams.queries source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)+1≤
      sizeBound source (scale source H Cpad r.1) := by
  have parts:=components source H Cpad r.1
  have bound:=HierarchyStreamCost.size_bound source H Cpad hcoeff hpad r
  obtain ⟨he,hr,hq⟩:=HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  change (source.output (HierarchyStreams.request k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2))).word.length+
    HierarchyStreams.R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)+
    HierarchyStreams.Q source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)+1≤_
  rw [he,hr,hq]
  exact bound.trans (monomial _ _ _ _ _ _ parts.2.2.2 (by omega) parts.2.1)

theorem source_polynomial : SourcePoly (sourceBound source) := by
  exact sourcePoly_pow sourcePoly_id _
theorem size_polynomial : SourcePoly (sizeBound source) := by
  exact sourcePoly_pow sourcePoly_id _

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HierarchyBudget
