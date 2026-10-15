import Proof.CaseAnalysis.WitnessNativeBudget

/-! The actual enclosing cold family pays its already-checked native,
legal-policy and capacity/family continuations. Both powers precede k. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def outerBound (a : PointwisePCPPAlgorithm) (G D copies e E K den : ℕ) (delta : ℚ) (sym : Bool) (N : ℕ):=
  ColdLegal.tailBound source a G D copies e den delta sym N+tailBound source a G D copies E K delta N+4

theorem budget_le (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad cutoff D G copies e E K den : ℕ) (delta : ℚ) (sym : Bool)
    (hcoeff:H.coefficient≤Cpad) (hpad:k+3≤Cpad) (hcut:2^a.minimumArity≤cutoff)
    (hbudget:∀ N,FamilyResources.capacity (scale source a G D copies delta N)≤K*(N+1)^E)
    (r : InputRequest) (raw bits : List Bool) (hraw:16*raw.length≤r.1) (hbits:bits.length≤r.1) :
    budget source a k H.coefficient Cpad cutoff D G copies e E K den delta
      (VerifierEncoding.code H.verifier) sym r.2 raw bits hpad≤
      ColdNative.bound source a D G copies cutoff delta (HierarchyBudget.scale source H Cpad r.1)+
        outerBound source a G D copies e E K den delta sym r.1 := by
  let code:=VerifierEncoding.code H.verifier
  let x:=List.ofFn r.2
  let R:=SelectedOracle.width source k H.coefficient Cpad code x
  have native:=ColdNative.budget_le source a H Cpad cutoff D G copies delta hcoeff hpad hcut r raw hraw
  unfold budget ColdLegal.budget outerBound
  split_ifs with live
  · have guards:=ColdFamilyGuards.live source k H.coefficient Cpad cutoff G code x raw live
    cases hd:decodeBooleanCircuit R (value raw) with
    | none =>
      simp only [Option.elim_none]
      omega
    | some oracle =>
      have hR:R≤r.1:=by simpa only [R,x,List.length_ofFn] using guards.2.1
      have ho:oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R:=by
        obtain ⟨other,decoded,size⟩:=guards.2.2
        have eq:other=oracle:=Option.some.inj (decoded.symm.trans hd)
        exact eq ▸ size
      have core:=ColdFamilyGuards.arity source a k H.coefficient Cpad code r.2 hpad oracle
        (hcut.trans ((Nat.le_max_right 2 cutoff).trans (by simpa only [x,List.length_ofFn] using guards.1)))
      have legal:=ColdLegal.tail_budget_le source a k H.coefficient Cpad D G copies e den delta code sym r.2 hpad oracle core hR ho
      have family:=tail_budget_le source a k H.coefficient Cpad D G copies E K delta code r.2 bits hpad oracle hbudget core hR hbits ho
      simp only [Option.elim_some]
      dsimp only [code] at legal family
      omega
  · omega

theorem outer_polynomial (a : PointwisePCPPAlgorithm) (G D copies e E K den : ℕ) (delta : ℚ) (sym : Bool) :
    SourcePoly (outerBound source a G D copies e E K den delta sym) :=
  ((ColdLegal.tail_polynomial source a G D copies e den delta sym).add
    (tail_polynomial source a G D copies E K delta)).add (polyDominated_const 4)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
