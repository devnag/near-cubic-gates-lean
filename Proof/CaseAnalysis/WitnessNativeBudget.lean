import Proof.CaseAnalysis.WitnessSupportDock
import Proof.CaseAnalysis.CloseoutWitnessColdOracleBudget

/-! Actual cold native execution has one source-fixed polynomial envelope
in the hierarchy's linear input scale, including malformed and size exits. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def parameterBound (T : ℕ):=HierarchyBudget.sizeBound source T+T+39*(2*T+5)^2+1
def bound (a : PointwisePCPPAlgorithm) (D G copies cutoff : ℕ) (delta : ℚ) (T : ℕ):=
  ColdOracle.bound source cutoff T+1+
    NativePipeline.bound a D G copies delta (ColdFamily.scale source a G D copies delta T) (parameterBound source T)+1

theorem budget_le (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad cutoff D G copies : ℕ) (delta : ℚ) (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad)
    (hcut:2^a.minimumArity≤cutoff) (r : InputRequest) (raw : List Bool) (hraw:16*raw.length≤r.1) :
    budget source a k H.coefficient Cpad cutoff D G copies delta (VerifierEncoding.code H.verifier) r.2 raw hpad≤
      bound source a D G copies cutoff delta (HierarchyBudget.scale source H Cpad r.1) := by
  let T:=HierarchyBudget.scale source H Cpad r.1
  let code:=VerifierEncoding.code H.verifier
  let x:=List.ofFn r.2
  let R:=SelectedOracle.width source k H.coefficient Cpad code x
  let Q:=SelectedStreams.queries source k H.coefficient Cpad code x
  let p:=SelectedStreams.pcp source k H.coefficient Cpad code x
  have hn:r.1≤T:=by have h:=(HierarchyBudget.components source H Cpad r.1).1;omega
  have size:p.word.length+R+Q+1≤HierarchyBudget.sizeBound source T:=
    HierarchyBudget.size_le source H Cpad hcoeff hpad r
  have before:=ColdOracle.budget_le source H Cpad cutoff hcoeff hpad r raw hraw
  unfold budget bound
  split_ifs with live
  · have guards:max 2 cutoff≤r.1 ∧ R≤r.1 ∧ (decodeBooleanCircuit R (value raw)).isSome=true:=by
      simpa only [ColdOracle.passed,GuardedOracle.passed,Bool.and_eq_true,decide_eq_true_eq,List.length_ofFn] using live
    cases hd:decodeBooleanCircuit R (value raw) with
    | none =>
      simp only [Option.elim_none]
      omega
    | some oracle =>
      have core:=ColdFamilyGuards.arity source a k H.coefficient Cpad code r.2 hpad oracle
        (hcut.trans ((Nat.le_max_right 2 cutoff).trans guards.1))
      have hrp:=PCPPNativeHierarchyNodes.width_fits source k H.coefficient Cpad code r.2 hpad
      have hqp:=PCPPNativeHierarchyNodes.queries_fit source k H.coefficient Cpad code r.2 hpad
      have param:=Oracle.parameter_le p R Q r.1 raw oracle (by omega) hraw hd
      have power:=Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left (show R+r.1+5≤2*T+5 by omega) 2)
      have hz:PCPPNativeResourceCost.sourceParameter oracle p Q≤parameterBound source T:=by
        unfold Oracle.parameterBound at param
        unfold parameterBound
        omega
      have tail:=NativePipeline.budget_le a source.coefficient source.degrees.queries D G copies delta
        p R Q hrp hqp r.2 oracle T (parameterBound source T) core (guards.2.1.trans hn)
        (ColdFamilyGuards.query_bound source k H.coefficient Cpad code x) hz
      simp only [Option.elim_some]
      change _+1+NativePipeline.budget a D G copies delta p R Q hrp hqp r.2 oracle+1≤_
      dsimp only [T,ColdFamily.scale] at tail ⊢
      omega
  · omega

theorem bound_polynomial (a : PointwisePCPPAlgorithm) (D G copies cutoff : ℕ) (delta : ℚ) (hD:1≤D) :
    SourcePoly (bound source a D G copies cutoff delta) := by
  have hs:=FamilyResources.source_scale_polynomial a source.coefficient source.degrees.queries G D delta copies
  have size:=HierarchyBudget.size_polynomial source
  have hz:SourcePoly (parameterBound source):=by
    change SourcePoly (fun n=>parameterBound source n)
    dsimp only [parameterBound]
    fast_budget_poly
  have native:=NativePipeline.bound_polynomial a D G copies delta hD hs hz
  have prior:=ColdOracle.bound_polynomial source cutoff
  change SourcePoly (fun n=>bound source a D G copies cutoff delta n)
  dsimp only [bound,ColdFamily.scale]
  fast_budget_poly

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
