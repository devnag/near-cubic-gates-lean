import Proof.CaseAnalysis.WitnessHierarchyBudget
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget

/-! Uniform source and oracle-prefix accounting includes the inactive and
oversized-width branches. All hierarchy dependence is in a linear scale. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open CloseoutSchedule LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def parserBound (N R : ℕ):=2*R+12*N+40+40000000000000000000000*(N+2)^25

theorem parser_le (R : ℕ) (x raw : List Bool) (hN:2≤x.length) (hraw:16*raw.length≤x.length) :
    GuardedOracle.budget R x raw≤parserBound x.length R := by
  have hmin:=Nat.min_le_right R x.length
  unfold GuardedOracle.budget
  split_ifs with hR
  · have value:value R.bits=R:=DimensionProducer.bits_value R
    have length:R.bits.length≤x.length+1:=
      (HierarchySourceScales.bits_length_le R).trans ((PCPPQueryCost.width_le R).trans (by omega))
    have oracle:=Oracle.budget_polynomial x raw R.bits hN hraw (by rw [value];exact hR)
    unfold OracleCall.budget OracleCall.prepareBudget RawCompare.budget parserBound
    rw [value]
    omega
  · unfold RawCompare.budget parserBound
    omega

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def sourceBound (cutoff T : ℕ):=8*T+2*max 2 cutoff+30+1+HierarchyBudget.sourceBound source T+1
def bound (cutoff T : ℕ):=sourceBound source cutoff T+1+parserBound T (HierarchyBudget.sizeBound source T)+1

theorem source_le {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad cutoff : ℕ)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (r : InputRequest) :
    ColdSource.budget source k H.coefficient Cpad cutoff (VerifierEncoding.code H.verifier) (List.ofFn r.2)≤
      sourceBound source cutoff (HierarchyBudget.scale source H Cpad r.1) := by
  have hn:r.1≤HierarchyBudget.scale source H Cpad r.1:=by
    have h:=(HierarchyBudget.components source H Cpad r.1).1
    omega
  have actual:=HierarchyBudget.source_le source H Cpad hcoeff hpad r
  have hmin:=Nat.min_le_right (max 2 cutoff) r.1
  unfold ColdSource.budget InputGuard.budget sourceBound
  simp only [List.length_ofFn]
  split_ifs <;> omega

theorem budget_le {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad cutoff : ℕ)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (r : InputRequest) (raw : List Bool)
    (hraw:16*raw.length≤r.1) :
    budget source k H.coefficient Cpad cutoff (VerifierEncoding.code H.verifier) (List.ofFn r.2) raw≤
      bound source cutoff (HierarchyBudget.scale source H Cpad r.1) := by
  let T:=HierarchyBudget.scale source H Cpad r.1
  let R:=SelectedOracle.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
  have hn:r.1≤T:=by have h:=(HierarchyBudget.components source H Cpad r.1).1;omega
  have hR:R≤HierarchyBudget.sizeBound source T:=by
    have h:=HierarchyBudget.size_le source H Cpad hcoeff hpad r
    change _+R+_+1≤HierarchyBudget.sizeBound source T at h
    omega
  have hsourced:=source_le source H Cpad cutoff hcoeff hpad r
  unfold budget bound
  simp only [List.length_ofFn]
  split_ifs with live
  · have parser:=parser_le R (List.ofFn r.2) raw (by simp only [List.length_ofFn];omega)
      (by simpa only [List.length_ofFn] using hraw)
    have large:parserBound r.1 R≤parserBound T (HierarchyBudget.sizeBound source T):=by
      unfold parserBound
      gcongr
    simp only [List.length_ofFn] at parser
    have paid:=parser.trans large
    change _≤ sourceBound source cutoff T+1+parserBound T (HierarchyBudget.sizeBound source T)+1
    dsimp only [T,R] at paid ⊢
    omega
  · omega

theorem bound_polynomial (cutoff : ℕ) : SourcePoly (bound source cutoff) := by
  have hp:=HierarchyBudget.source_polynomial source
  have hs:=HierarchyBudget.size_polynomial source
  change SourcePoly (fun n=>bound source cutoff n)
  dsimp only [bound,sourceBound,parserBound]
  fast_budget_poly

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
