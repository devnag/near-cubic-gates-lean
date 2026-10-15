import Proof.CaseAnalysis.WitnessNativeLayout

/-! The actual original input and raw oracle guess execute every early
guard, the selected source once, native PCPP/cache, and actual family policy. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem native_run_with_originals (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies : ℕ) (delta : ℚ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad) (hD : 1≤D) (hcap : 16*raw.length ≤ n) :
    ∃ actual,
      (ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true →
        actual.final.tapes (originalTape source a k D G)=frame (List.ofFn x)) ∧
      run (machine source a k CH Cpad cutoff D G copies delta code)
      (budget source a k CH Cpad cutoff D G copies delta code x raw hpad)
      (input source a k D G (List.ofFn x) raw)=some actual ∧
      actual.steps≤budget source a k CH Cpad cutoff D G copies delta code x raw hpad ∧
      actual.final.tapes (lengthSlot source a k D G)=List.replicate n true ∧
      actual.final.heads (lengthSlot source a k D G)=0 ∧
      actual.final.heads (flagSlot source a k D G)=0 ∧
      readTapeBit (actual.final.tapes (flagSlot source a k D G)) 0=
        passed source k CH Cpad cutoff G code (List.ofFn x) raw ∧
      (∀ oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)),
        ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true →
        decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle →
        oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)) →
        let r:=request source a k CH Cpad code x hpad oracle
        (∀ j : Fin 19,actual.final.tapes (cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
            (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
        (∀ j : Fin 19,actual.final.heads (cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryClauseReuse.heads j) ∧
        SourcePolicy.Call.Fields D copies delta (NativePolicy.fields a) r (a.output r)
          (project source a k D G actual.final)):=by
  have priorExists:=ColdOracle.oracle_run source
    k CH Cpad cutoff code (List.ofFn x) raw hpad (by simpa only [List.length_ofFn] using hcap)
  let prior:=Classical.choose priorExists
  have priorFacts:=Classical.choose_spec priorExists
  have hprior:=priorFacts.1
  have priorN:=priorFacts.2.1
  have priorFlag:=priorFacts.2.2.2.1
  have sourceGood:=priorFacts.2.2.2.2.1
  have descriptor:=priorFacts.2.2.2.2.2
  have hfirst : ClockJoin.ReadyRun (first source a k CH Cpad cutoff D G code)
      (ColdOracle.budget source k CH Cpad cutoff code (List.ofFn x) raw)
      (input source a k D G (List.ofFn x) raw) (NativePipeline.Dock.input a D G prior):=
    ClockJoin.lift (Equiv.refl _) (ColdOracle.machine source k CH Cpad cutoff code) _ _ _
      (fun _ : Fin (NativePipeline.Dock.extra a D G)=>[]) hprior
  have gate : readTapeBit (NativePipeline.Dock.input a D G prior (gateSlot source a k D G)) 0=
      ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw:=by
    simpa only [gateSlot,old,NativePipeline.Dock.input,NativePipeline.Dock.old,Fin.addCases_left] using priorFlag
  have midN : NativePipeline.Dock.input a D G prior (lengthSlot source a k D G)=List.replicate n true:=by
    simpa only [lengthSlot,old,NativePipeline.Dock.input,NativePipeline.Dock.old,Fin.addCases_left,List.length_ofFn] using priorN
  by_cases live:ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true
  · have guards : max 2 cutoff ≤ (List.ofFn x).length ∧
        SelectedOracle.width source k CH Cpad code (List.ofFn x) ≤ (List.ofFn x).length ∧
        (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).isSome=true:=by
      simpa only [ColdOracle.passed,GuardedOracle.passed,Bool.and_eq_true,decide_eq_true_eq] using live
    let oracle:=(decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (value raw)).get guards.2.2
    have hd:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle:=
      (Option.some_get guards.2.2).symm
    have five:=retained_fields source k CH Cpad code (List.ofFn x) prior oracle
      (sourceGood guards.1).1 (sourceGood guards.1).2
      (descriptor guards.1 guards.2.1 oracle hd)
    have bExists:=NativePipeline.pipeline_run a D G copies delta
      (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
      (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
      (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle hD
    let b:=Classical.choose bExists
    have bFacts:=Classical.choose_spec bExists
    have hb:=bFacts.1
    have bh:=bFacts.2.2.1
    have bt:=bFacts.2.2.2.1
    have bgood:=bFacts.2.2.2.2
    have lastExists:=RecoveryFocus.dock (slots source a k D G)
      (NativePipeline.Dock.slots_injective a D G (fields source k) (fields_injective source k))
      (NativePipeline.machine a D G copies delta) _ (fun _=>0) (NativePipeline.Dock.input a D G prior)
      (initialConfiguration (NativePipeline.machine a D G copies delta)
        (NativePipeline.input a D G oracle (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
          (SelectedStreams.queries source k CH Cpad code (List.ofFn x))))
      (by intro i;rfl) (NativePipeline.Dock.input_local a D G (fields source k) prior oracle _ _ five) b hb
    let last:=Classical.choose lastExists
    have lastFacts:=Classical.choose_spec lastExists
    have hl:=lastFacts.1
    have lh:=lastFacts.2.2.2.1
    have lt:=lastFacts.2.2.2.2.1
    have away:=lastFacts.2.2.2.2.2
    have hat : CloseoutRowsGatePairHeads.ReadyAt (first source a k CH Cpad cutoff D G code)
        (ColdOracle.budget source k CH Cpad cutoff code (List.ofFn x) raw) (fun _=>0)
        (input source a k D G (List.ofFn x) raw) (NativePipeline.Dock.input a D G prior):=by
      obtain ⟨r,hr,rt,rh,rs⟩:=hfirst
      exact ⟨r,hr,rt,funext rh,rs⟩
    have actualExists:=CloseoutRowsGateSourceCalls.joined
      (first source a k CH Cpad cutoff D G code) (second source a k D G copies delta)
      (fun scanned=>scanned (gateSlot source a k D G))
      (ColdOracle.budget source k CH Cpad cutoff code (List.ofFn x) raw)
      (tailBudget source a k CH Cpad D G copies delta code x hpad oracle) (fun _=>0)
      (input source a k D G (List.ofFn x) raw) (NativePipeline.Dock.input a D G prior) hat last hl
      (by exact gate.trans live)
    let actual:=Classical.choose actualExists
    have actualFacts:=Classical.choose_spec actualExists
    have ha:=actualFacts.1
    have atape:=actualFacts.2.1
    have ahead:=actualFacts.2.2.1
    have asteps:=actualFacts.2.2.2
    have he : budget source a k CH Cpad cutoff D G copies delta code x raw hpad=
        ColdOracle.budget source k CH Cpad cutoff code (List.ofFn x) raw+1+
          tailBudget source a k CH Cpad D G copies delta code x hpad oracle+1:=by
      simp only [budget,if_pos live,hd,Option.elim_some]
    have keep:=away (lengthSlot source a k D G)
      (NativePipeline.Dock.outside a D G (fields source k) _ (fields_ne_length source k))
    refine ⟨actual,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro _
      have saved := away (originalTape source a k D G) (slots_ne_originalTape source a k D G)
      have sourceT := (sourceGood guards.1).1.input
      have retained := saved.2.trans sourceT
      exact (congrFun atape _).trans retained
    · rw [he]
      exact ha
    · rw [he]
      exact asteps
    · rw [atape]
      exact keep.2.trans midN
    · rw [ahead]
      exact keep.1
    · rw [ahead]
      exact (lh _).trans bh
    · rw [atape,flagSlot,lt,bt]
      simp [passed,live,hd,readTapeBit]
    · intro other _ hother sizeGood
      have same:other=oracle:=Option.some.inj (hother.symm.trans hd)
      subst other
      have cacheT:=(bgood sizeGood).1
      have cacheH:=(bgood sizeGood).2.1
      have policy:=(bgood sizeGood).2.2
      have getT (i):actual.final.tapes (slots source a k D G i)=b.final.tapes i:=
        (congrFun atape _).trans (lt i)
      have getH (i):actual.final.heads (slots source a k D G i)=b.final.heads i:=
        (congrFun ahead _).trans (lh i)
      exact ⟨fun j=>(getT _).trans (cacheT j),fun j=>(getH _).trans (cacheH j),
        ⟨(getT _).trans policy.count,(getT _).trans policy.clause,(getT _).trans policy.q0,
          (getT _).trans policy.cap,fun i=>(getH _).trans (policy.cursor i)⟩⟩
  · have stopped:=CloseoutRowsGateColdPair.rejected
      (first source a k CH Cpad cutoff D G code) (second source a k D G copies delta)
      (fun scanned=>scanned (gateSlot source a k D G)) _ _ _ hfirst
      (gate.trans (Bool.eq_false_iff.mpr live))
    have enlarged:=ClockJoin.enlarge (machine source a k CH Cpad cutoff D G copies delta code) _
      (budget source a k CH Cpad cutoff D G copies delta code x raw hpad) _ _ stopped
      (by unfold budget;rw [if_neg live];omega)
    let actual:=Classical.choose enlarged
    have actualFacts:=Classical.choose_spec enlarged
    have ha:=actualFacts.1
    have atape:=actualFacts.2.1
    have ahead:=actualFacts.2.2.1
    have asteps:=actualFacts.2.2.2
    refine ⟨actual,(fun hp=>False.elim (live hp)),ha,asteps,?_,ahead _,ahead _,?_,fun _ hp=>False.elim (live hp)⟩
    · rw [atape]
      exact midN
    · rw [atape,flagSlot,slots,NativePipeline.Dock.initial_flag]
      simp [passed,Bool.eq_false_iff.mpr live,readTapeBit]

theorem native_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies : ℕ) (delta : ℚ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad) (hD : 1≤D) (hcap : 16*raw.length ≤ n) :
    ∃ actual,run (machine source a k CH Cpad cutoff D G copies delta code)
      (budget source a k CH Cpad cutoff D G copies delta code x raw hpad)
      (input source a k D G (List.ofFn x) raw)=some actual ∧
      actual.steps≤budget source a k CH Cpad cutoff D G copies delta code x raw hpad ∧
      actual.final.tapes (lengthSlot source a k D G)=List.replicate n true ∧
      actual.final.heads (lengthSlot source a k D G)=0 ∧
      actual.final.heads (flagSlot source a k D G)=0 ∧
      readTapeBit (actual.final.tapes (flagSlot source a k D G)) 0=
        passed source k CH Cpad cutoff G code (List.ofFn x) raw ∧
      (∀ oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)),
        ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true →
        decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle →
        oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)) →
        let r:=request source a k CH Cpad code x hpad oracle
        (∀ j : Fin 19,actual.final.tapes (cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
            (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
        (∀ j : Fin 19,actual.final.heads (cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryClauseReuse.heads j) ∧
        SourcePolicy.Call.Fields D copies delta (NativePolicy.fields a) r (a.output r)
          (project source a k D G actual.final)) :=by
  obtain ⟨actual, _original, facts⟩ :=
    native_run_with_originals source a k CH Cpad cutoff D G copies delta code x raw hpad hD hcap
  exact ⟨actual, facts⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
