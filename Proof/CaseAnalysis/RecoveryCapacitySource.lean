import Proof.CaseAnalysis.RecoveryCapacityLive

/-! Export the source-length domination already present in the SAME recovery
majorant. This pays the original hierarchy-stream call as well as its graph. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCapacity
open RepairOrdinary ProjectionNormalization SourceInterfaces RecoveryScheduleEnvelope
open CloseoutLanguage CloseoutRecoveryWorkspace SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem actual_capacity_with_source
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad degree : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) :
    ∃ A B0 : ℕ, ∀ (n : ℕ) (r : InputRequest), r.1 ≤ 2^n →
      HierarchyProjection.width source H Cpad r.1 ≤ n →
      let p:=source.output (HierarchyEncode.encode H Cpad r)
      let R:=HierarchyProjection.width source H Cpad r.1
      let Q:=HierarchyProjection.queries source H Cpad r.1
      let B:=oracleSizeBound degree R
      let W:=CloseoutCapacity.capacity A B0 n
      r.1 ≤ W ∧ originalWorkspace R B Q (Codec.clauses p).length ≤ W ∧
        R ≤ W ∧ Q ≤ W ∧ B ≤ W ∧ (DedupBytes.fields p).length ≤ W ∧ 2^R ≤ W:=by
  obtain ⟨A,B0,hW⟩:=exists_capacity source H Cpad degree
  refine ⟨A,B0,?_⟩
  intro n r hn hr
  have hx:2^n ≤ majorant source H Cpad degree (2^n):=by
    unfold majorant
    exact (Nat.le_add_left _ _).trans (Nat.le_succ _)
  obtain ⟨hg,hR,hQ,hB,hbytes,htwo⟩:=actual_bounds source H Cpad degree hcoeff hpad r n hn hr
  exact ⟨hn.trans (hx.trans (hW n)),hg.trans (hW n),hR.trans (hW n),hQ.trans (hW n),
    hB.trans (hW n),hbytes.trans (hW n),htwo.trans (hW n)⟩

theorem selected_source_capacity_run (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (degree copies clauseDegree : ℕ)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies) :
    ∃ A B0 : ℕ, ∀ (n : ℕ) (address : BitInput n),
      ∃ out,ClockJoin.ReadyRun (CloseoutCapacity.machine A B0)
        (CloseoutCapacity.coefficient A B0*(2^n+1)^(A+1))
        (CloseoutCapacity.input (List.ofFn address)) out ∧
      out 24=List.replicate (CloseoutCapacity.capacity A B0 n) true ∧
      out 0=frame (List.ofFn address) ∧
      let source:=fixedProjection sources
      let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
      let Cpad:=padding sources k clock
      let s:=selectedIndex (widthAt sources k clock copies clauseDegree) n
      ∀ input : BitInput (2^s), 1 ≤ s →
        let r:InputRequest:=⟨2^s,input⟩
        let p:=source.output (HierarchyEncode.encode H Cpad r)
        let R:=HierarchyProjection.width source H Cpad (2^s)
        let Q:=HierarchyProjection.queries source H Cpad (2^s)
        let B:=oracleSizeBound degree R
        let W:=CloseoutCapacity.capacity A B0 n
        2^s ≤ W ∧ originalWorkspace R B Q (Codec.clauses p).length ≤ W ∧
          R ≤ W ∧ Q ≤ W ∧ B ≤ W ∧ (DedupBytes.fields p).length ≤ W ∧ 2^R ≤ W:=by
  let source:=fixedProjection sources
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let Cpad:=padding sources k clock
  have hcoeff:H.coefficient ≤ Cpad:=by dsimp only [H,Cpad,padding];omega
  have hpad:k+3 ≤ Cpad:=by dsimp only [H,Cpad,padding];omega
  obtain ⟨A,B0,hactual⟩:=actual_capacity_with_source source H Cpad degree hcoeff hpad
  refine ⟨A,B0,fun n address=>?_⟩
  obtain ⟨out,hr,hW,_ht,haddress⟩:=CloseoutCapacity.capacity_run A B0 (List.ofFn address)
  have hrun:=ClockJoin.enlarge _ _ _ _ _ hr (CloseoutCapacity.budget_bound A B0 (List.ofFn address))
  simp only [List.length_ofFn] at hrun hW
  refine ⟨out,hrun,hW,haddress,?_⟩
  intro source' H' Cpad' s input hs
  have hf:=case_one_live_fits sources k clock degree copies clauseDegree n hcopies input hs
  exact hactual n ⟨_, input⟩ hf.2.1 hf.2.2.1

end
end NearCubicWires.RepairSource.CloseoutRecoveryCapacity
