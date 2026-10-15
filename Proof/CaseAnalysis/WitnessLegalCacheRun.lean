import Proof.CaseAnalysis.WitnessLegalCacheFields
import Proof.CaseAnalysis.WitnessFamilyGuards

/-! The already executed legal-policy run retains the SAME prepaid query
cache. Determinism identifies its receipt; no additional source work runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem cache_fields_with_originals (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (hpad : k+3≤Cpad) (hD : 1≤D) (hden : 0<den) (hcap : 16*raw.length≤n)
    (actual : ExecutionReceipt (tapes source a k D G e) _)
    (hrun:run (machine source a k CH Cpad cutoff D G copies e den delta code sym)
      (budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
      (input source a k D G e (List.ofFn x) raw)=some actual)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hdecode:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle)
    (live:ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true) :
    actual.final.tapes (originalTape source a k D G e)=frame (List.ofFn x) ∧
    let r:=ColdNative.request source a k CH Cpad code x hpad oracle
    ∀ j:Fin 19,actual.final.tapes (cache source a k D G e j)=
      PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
        (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j ∧
      actual.final.heads (cache source a k D G e j)=PCPPQueryClauseReuse.heads j:=by
  have guards:ColdOracle.passed source k CH Cpad cutoff code (List.ofFn x) raw=true ∧
      oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)):=
    by simpa only [ColdNative.passed,hdecode,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] using live
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  have priorExists:=ColdNative.native_run_with_originals source a k CH Cpad cutoff D G copies delta code x raw hpad hD hcap
  let prior : ExecutionReceipt (ColdNative.tapes source a k D G) _:=Classical.choose priorExists
  have pf:=(Classical.choose_spec priorExists).2
  have nativeFields:=pf.2.2.2.2.2.2 oracle guards.1 hdecode guards.2
  have inputs:=retained_fields source a k D G copies delta prior.final r (nativeFields.1 13) nativeFields.2.2
  have nextExists:=LegalTemplate.Call.call_run e den delta copies sym (fields source a k D G)
    (fields_injective source a k D G) prior.final.tapes prior.final.heads r.arity (CorePolicy.q0 D r.arity)
    (a.output r).clauseBits (natBitLength (CloseoutXor.cap delta (CorePolicy.q0 D r.arity) copies*
      max 1 (2*2^(a.output r).clauseBits))) hden (core_positive source a k CH Cpad code x hpad oracle) inputs.1 inputs.2
  let last : ExecutionReceipt (tapes source a k D G e) _:=Classical.choose nextExists
  have nf:=Classical.choose_spec nextExists
  let lifted : ExecutionReceipt (tapes source a k D G e) _:=
    TapeEmbedding.receipt (fun _ : Fin (LegalTemplate.Call.extra e)=>0) (fun _=>[]) prior
  have firstRun:=TapeEmbedding.run_embed (ColdNative.machine source a k CH Cpad cutoff D G copies delta code)
    (fun _ : Fin (LegalTemplate.Call.extra e)=>0) (fun _=>[]) _ _ prior pf.1
  rw [StreamPrepare.embed_initial] at firstRun
  have flagH:lifted.final.heads (flagSlot source a k D G e)=0:=
    (TapeEmbedding.receipt_heads_old _ _ prior _).trans pf.2.2.2.2.1
  have flagT:readTapeBit (lifted.final.tapes (flagSlot source a k D G e)) 0=true:=
    (congrArg (fun word=>readTapeBit word 0) (TapeEmbedding.receipt_tapes_old _ _ prior _)).trans
      (pf.2.2.2.2.2.1.trans live)
  have scan:(fun cells=>cells (flagSlot source a k D G e)) lifted.final.scanned=true:=by
    change readTapeBit _ (lifted.final.heads (flagSlot source a k D G e))=true
    rw [flagH];exact flagT
  have joined:=CloseoutRowsCircuitGuarded.accepted
    (first source a k CH Cpad cutoff D G copies e delta code) (second source a k D G e den copies delta sym)
    (fun cells=>cells (flagSlot source a k D G e))
    (ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad)
    (tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle) (fun _=>0)
    (input source a k D G e (List.ofFn x) raw) lifted last firstRun nf.1 scan
  let result : ExecutionReceipt (tapes source a k D G e) _:=Classical.choose joined
  have jf:=Classical.choose_spec joined
  have he:budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad=
      ColdNative.budget source a k CH Cpad cutoff D G copies delta code x raw hpad+1+
        tailBudget source a k CH Cpad D copies e den delta code sym x hpad oracle+1:=by
    rw [budget,if_pos live,hdecode]
    exact (Nat.add_assoc _ _ _).symm
  have full:= (congrArg (fun fuel=>run (machine source a k CH Cpad cutoff D G copies e den delta code sym) fuel
    (input source a k D G e (List.ofFn x) raw)) he).trans jf.1
  have same:actual=result:=Option.some.inj (hrun.symm.trans full)
  have outputH:actual.final.heads=last.final.heads:=
    (congrArg (fun z=>z.final.heads) same).trans jf.2.2.1
  have outputT:actual.final.tapes=last.final.tapes:=
    (congrArg (fun z=>z.final.tapes) same).trans jf.2.2.2
  have saved := nf.2.2.2.2 (ColdNative.originalTape source a k D G)
    (fields_ne_originalTape source a k D G)
  have sourceT := (Classical.choose_spec priorExists).1 guards.1
  have retained := saved.2.trans sourceT
  have originalT := (congrFun outputT _).trans retained
  refine ⟨originalT, ?_⟩
  dsimp only
  intro j
  by_cases hj:j=13
  · subst j
    have ht:actual.final.tapes (slots source a k D G e (LegalTemplate.templateSlots e 0))=UnaryTemplate.tape r.arity:=
      (congrFun outputT _).trans nf.2.2.2.1.domain
    have hh:actual.final.heads (slots source a k D G e (LegalTemplate.templateSlots e 0))=1:=
      (congrFun outputH _).trans (nf.2.2.1 _)
    rw [domain_cache] at ht hh
    exact ⟨ht,hh⟩
  · have keep:=nf.2.2.2.2 (ColdNative.cacheSlots source a k D G (PCPPSourceCache.cacheSlots a j))
      (fields_ne_cache source a k D G j hj)
    exact ⟨(congrFun outputT _).trans (keep.2.trans (nativeFields.1 j)),
      (congrFun outputH _).trans (keep.1.trans (nativeFields.2.1 j))⟩

theorem cache_fields (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (hpad : k+3≤Cpad) (hD : 1≤D) (hden : 0<den) (hcap : 16*raw.length≤n)
    (actual : ExecutionReceipt (tapes source a k D G e) _)
    (hrun:run (machine source a k CH Cpad cutoff D G copies e den delta code sym)
      (budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
      (input source a k D G e (List.ofFn x) raw)=some actual)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hdecode:decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle)
    (live:ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true) :
    let r:=ColdNative.request source a k CH Cpad code x hpad oracle
    ∀ j:Fin 19,actual.final.tapes (cache source a k D G e j)=
      PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
        (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j ∧
      actual.final.heads (cache source a k D G e j)=PCPPQueryClauseReuse.heads j :=by
  exact (cache_fields_with_originals source a k CH Cpad cutoff D G copies e den delta code sym
    x raw hpad hD hden hcap actual hrun oracle hdecode live).2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdLegal
