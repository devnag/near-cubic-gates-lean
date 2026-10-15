import Proof.CaseAnalysis.WitnessFamilyResourcesPolicy

/-! Consumer-first closure of the unchanged FamilyCold numerical interface.
The P/H constants depend on the fixed sources and policies, never on a
hierarchy clock. Source/cache/driver production is still physically paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth PaddedRunnerBudgetClosure
open SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem source_fits (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies K E : ℕ)
    (hbudget : ∀ N,capacity (sourceScale a qc qd od D delta copies N) ≤ K*(N+1)^E)
    {n R Q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin Q→Fin n→ProjectedRandomBit R) (formula : ThreeCNF Q)
    (N : ℕ) (bits arity : List Bool) (hR : R ≤ N) (hbits : bits.length ≤ N)
    (harity : arity.length ≤ N+1) (hQ : Q ≤ qc*(R+1)^qd)
    (ho : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound od R) :
    let p:=a.output (PCPPSubstitution.sourceRequest a oracle projections formula)
    Fits (K*(N+1)^E) (p.systematicBits+p.auxiliaryBits)
      (coefficientCap delta copies D R p.clauseBits) (termCap delta copies D R p.clauseBits)
      (CloseoutMassThreshold.literalWidth delta copies) bits arity := by
  obtain ⟨hn,_hv,hc,ht,hk⟩:=source_bounds a qc qd od D delta copies oracle projections formula N hR hQ ho
  exact fits _ _ _ _ _ _ bits arity (hbudget N) (hbits.trans (by omega)) (harity.trans hn) hc ht hk

theorem source_runtime (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies K E : ℕ) :
    ∃ J F,1 ≤ J ∧ ∀ N,
      totalCost (sourceScale a qc qd od D delta copies N) (K*(N+1)^E) ≤ J*(N+1)^F := by
  have hp:SourcePoly (fun N=>K*(N+1)^E) :=
    (sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1)) E).const_mul K
  obtain ⟨F,J,hbound⟩:=(costs_polynomial (source_scale_polynomial a qc qd od D delta copies) hp).2.2
  exact ⟨J+1,F,by omega,fun N=>(hbound N).trans (Nat.mul_le_mul_right _ (by omega))⟩

theorem source_parameters (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) :
    ∃ K E J F,1 ≤ K ∧ 1 ≤ J ∧
      (∀ N,capacity (sourceScale a qc qd od D delta copies N) ≤ K*(N+1)^E) ∧
      (∀ N,totalCost (sourceScale a qc qd od D delta copies N) (K*(N+1)^E) ≤ J*(N+1)^F) := by
  obtain ⟨K,E,hK,hcap⟩:=source_envelope a qc qd od D delta copies
  obtain ⟨J,F,hJ,hrun⟩:=source_runtime a qc qd od D delta copies K E
  exact ⟨K,E,J,F,hK,hJ,hcap,hrun⟩

theorem consumer_run (sym : Bool) (S P V C T core W L k : ℕ) (q : ℚ)
    (bits arity : List Bool) (ambient : Fin 94→List Bool)
    (hf : Fits P V C T k bits arity) (hlen : bits.length ≤ S) (hv : V ≤ S)
    (hC : 0 < C) (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k) :
    ∃ extra r,runFrom (FamilyCold.machine sym k q)
      (FamilyCold.budget P (P+1) V (sumCost S P) bits)
      ⟨(FamilyCold.machine sym k q).start,FamilyPrepare.heads FamilyHeads.heads,
        FamilyCold.input P (P+1) V C T core W L bits arity ambient⟩=some r ∧
      r.steps ≤ totalCost S P ∧ r.final.heads 724=0 ∧
      r.final.tapes 724=[FamilyCold.passed sym V C T core W L q bits arity] ∧
      extra 174=List.replicate V true ∧
      (FamilyCold.passed sym V C T core W L q bits arity=true → ∃ after,
        r.final.heads=FamilyPrepare.heads (FamilyWork.heads
          (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L k q
            (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
            [] [] [] (FamilyMode.native sym core) V after) 1) ∧
        r.final.tapes=FamilyPrepare.tapes (natBitLength C) bits (FamilyWork.tapes (P+1) V
          (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L k q
            (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
            [] [] [] (FamilyMode.native sym core) V after) extra) ∧
        Store (width T (natBitLength C)) zero [] after) := by
  obtain ⟨extra,r,hr,hs,hh,ht,he,hgood⟩:=FamilyCold.family_run sym P (P+1) V C T core W L
    (termCost S P) (sumCost S P) k q bits arity ambient hC le_rfl hf.circuit
    (hf.raw.trans (Nat.le_add_right P 1)) hf.raw (hf.header.trans (Nat.le_add_right P 1))
    (fun field hfield=>(hf.guard field hfield).trans (Nat.le_add_right P 1))
    (fun field hfield _=>(hf.append field hfield).trans (Nat.le_add_right P 1))
    hf.read hf.coefficientWidth hf.mass hf.bits hf.native (term_cost S P V C T k bits arity hf hlen)
    hstore hq hk hp hd hf.check (sum_cost S P V C T k bits arity hf hlen)
  exact ⟨extra,r,hr,hs.trans (total_cost S P V C T k bits arity hf hv),hh,ht,he,hgood⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
