import Proof.CaseAnalysis.WitnessFamilySupportActual
import Proof.CaseAnalysis.WitnessSupportLiftPorts
import Proof.CaseAnalysis.WitnessFamilySupportLayout
import Proof.CaseAnalysis.WitnessRunFuel
import Proof.CaseAnalysis.WitnessFamilySupportCachePorts

/-! The original cold source and policy enter the actual strengthened
family. All inputs, including rejected branches, use twice the old fuel;
the new support stream is retained only after the same old verdict passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open CompetitorSumFold CompetitorSumWidth RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem transport {α β : Sort*} {P : α→β→Prop} {a c : α} {b d : β}
    (ha:a=c) (hb:b=d) (h:P c d) : P a b := by
  cases ha;cases hb;exact h

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def actualMachine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den km : ℕ)
    (delta q : ℚ) (code : List Bool) (sym : Bool):=
  machine source (FamilySupport.Actual sym km q) a k CH Cpad cutoff D G copies e E K den delta code sym

def originalTape (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :=
  FamilySupportCall.old (FamilyCapacity.Call.old E (ColdFamily.originalTape source a k D G e))

theorem family_run_with_originals (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool)
    (hpad:k+3≤Cpad) (hD:1≤D) (hden:0<den) (hK:0<K) (hcut:2^a.minimumArity≤cutoff)
    (hd:0<delta) (hh:delta<1/2) (hc:1≤copies)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E)
    (hraw:16*raw.length≤n) (hbits:16*bits.length≤n) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    let fuel:=2*ColdFamily.budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad
    ∃ actual,
      (ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=true →
        actual.final.tapes (originalTape source a k D G e E)=frame (List.ofFn x)) ∧
      run (actualMachine source a k CH Cpad cutoff D G copies e E K den km delta q code sym)
      fuel (input source a k D G e E (List.ofFn x) raw bits)=some actual ∧
      actual.steps≤fuel ∧ actual.final.heads (familySlots source a k D G e E 724)=0 ∧
      readTapeBit (actual.final.tapes (familySlots source a k D G e E 724)) 0=
        ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad ∧
      (ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=true→
        ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle ∧
          oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
          let r:=ColdNative.request source a k CH Cpad code x hpad oracle
          let cb:=(a.output r).clauseBits
          let W:=LegalPolicy.W e den r.arity
          FamilySupport.retained sym (FamilyCapacity.value E K n) ((a.output r).systematicBits+(a.output r).auxiliaryBits)
            (FamilyResources.coefficientCap delta copies D r.arity cb) (FamilyResources.termCap delta copies D r.arity cb)
            r.arity W (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) W) km q bits []
            (actual.final.heads ∘ familySlots source a k D G e E)
            (actual.final.tapes ∘ familySlots source a k D G e E) ∧
          ∀ j:Fin 19,actual.final.tapes (cache source a k D G e E j)=
            PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
              (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j ∧
            actual.final.heads (cache source a k D G e E j)=PCPPQueryClauseReuse.heads j) := by
  let km:=CloseoutMassThreshold.literalWidth delta copies
  let q:=CloseoutSampledWitness.massCap delta copies
  let S:=ColdFamily.scale source a G D copies delta n
  have priorExists:=ColdLegal.legal_run source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad hD hden hraw
  let prior : ExecutionReceipt (ColdLegal.tapes source a k D G e) _:=Classical.choose priorExists
  have pf:=Classical.choose_spec priorExists
  let one:=SupportLift.base bits prior
  let lifted:=SupportLift.receipt E bits prior
  have firstRun:=first_run source a k CH Cpad cutoff D G copies e E den
    (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
    delta code sym (List.ofFn x) raw bits prior pf.1
  have flagH:lifted.final.heads (guardSlot source a k D G e E)=0:=
    (SupportLift.heads_old E bits prior _).trans pf.2.2.2.2.1
  have flagT:readTapeBit (lifted.final.tapes (guardSlot source a k D G e E)) 0=
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw:=by
    have kept:=SupportLift.tapes_old E bits prior (ColdLegal.flagSlot source a k D G e)
    exact (congrArg (fun word=>readTapeBit word 0) kept).trans pf.2.2.2.2.2.1
  have oneT (i : Fin (ColdLegal.tapes source a k D G e)) :
      one.final.tapes (ColdFamily.old source a k D G e i)=prior.final.tapes i:=
    SupportLift.base_tapes_old bits prior i
  have oneH (i : Fin (ColdLegal.tapes source a k D G e)) :
      one.final.heads (ColdFamily.old source a k D G e i)=prior.final.heads i:=
    SupportLift.base_heads_old bits prior i
  have onePolicy:one.final.tapes ∘ ColdFamily.policy source a k D G e=
      prior.final.tapes ∘ ColdLegal.slots source a k D G e:=funext (fun i=>oneT _)
  have scan:(fun scanned=>scanned (guardSlot source a k D G e E)) lifted.final.scanned=
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw:=by
    change readTapeBit _ (lifted.final.heads (guardSlot source a k D G e E))=_
    rw [flagH];exact flagT
  by_cases live:ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw=true
  · have guards:=ColdFamilyGuards.live source k CH Cpad cutoff G code (List.ofFn x) raw live
    let oracle:=Classical.choose guards.2.2
    have ho:=Classical.choose_spec guards.2.2
    let r:=ColdNative.request source a k CH Cpad code x hpad oracle
    let cb:=(a.output r).clauseBits
    let V:=(a.output r).systematicBits+(a.output r).auxiliaryBits
    let C:=FamilyResources.coefficientCap delta copies D r.arity cb
    let T:=FamilyResources.termCap delta copies D r.arity cb
    have core:=ColdFamilyGuards.arity source a k CH Cpad code x hpad oracle
      (hcut.trans ((Nat.le_max_right 2 cutoff).trans (by simpa only [List.length_ofFn] using guards.1)))
    have hR:SelectedOracle.width source k CH Cpad code (List.ofFn x)≤n:=by simpa only [List.length_ofFn] using guards.2.1
    have fit:=ColdFamilyResources.native_fits a source.coefficient source.degrees.queries G D delta copies K E hbudget
      (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
      (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
      (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle n bits core hR (by omega)
      (ColdFamilyGuards.query_bound source k CH Cpad code (List.ofFn x)) ho.2
    have legalFields:=pf.2.2.2.2.2.2 oracle ho.1 live
    have hn:n+1≤S:=by dsimp only [S,ColdFamily.scale,FamilyResources.sourceScale,FamilyResources.scale];omega
    have threshold:=CloseoutMassThreshold.threshold_fits delta hd hh copies (CorePolicy.q0 D r.arity) cb hc
    have lastExists:=FamilySupportActual.family_run
      e E K n den copies r.arity (CorePolicy.q0 D r.arity) cb S V C km delta q sym
      (ColdFamily.lengthSlot source a k D G e) (ColdFamily.countSlot source a k D G e) (ColdFamily.rawSlot source a k D G e)
      (ColdFamily.policy source a k D G e) one.final.tapes one.final.heads bits [] hK
      (ColdFamily.policy_injective source a k D G e) (ColdFamily.count_ne_raw source a k D G e)
      (ColdFamily.count_outside source a k D G e) (ColdFamily.raw_outside source a k D G e)
      ((oneT _).trans pf.2.2.1) ((oneH _).trans pf.2.2.2.1)
      ((oneT _).trans legalFields.1) ((oneH _).trans legalFields.2.1)
      (TapeEmbedding.receipt_tapes_new _ _ prior (0 : Fin 1))
      (TapeEmbedding.receipt_heads_new _ _ prior (0 : Fin 1))
      (by rw [onePolicy];exact legalFields.2.2.2) (fun i=>(oneH _).trans (legalFields.2.2.1 i))
      fit.1 (hbudget n) (by omega) fit.2 (core.trans_le (hR.trans (by omega)))
      (FamilyResources.coefficient_positive delta copies D r.arity cb)
      (CloseoutSampledWitness.mass_nonneg delta hd hh copies)
      (CloseoutMassThreshold.shared_fits delta hd hh copies (CorePolicy.q0 D r.arity) cb T hc)
      threshold.2.1 threshold.2.2
    let last:=Classical.choose lastExists
    have lf:=Classical.choose_spec lastExists
    have lr:=lf.1
    have lh:=lf.2.2.1
    have lt:=lf.2.2.2.1
    have good:=lf.2.2.2.2.2
    have nextRun:runFrom (second source (FamilySupport.Actual sym km q) a k D G e E K)
        (2*ColdFamily.tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle)
        (RecoveryCalls.restarted (second source (FamilySupport.Actual sym km q) a k D G e E K) lifted.final.heads lifted.final.tapes)=some last:=by
      rw [show lifted.final.heads=FamilySupportFromPolicy.heads E one.final.heads [] from SupportLift.heads E bits prior,
        show lifted.final.tapes=FamilySupportFromPolicy.input E one.final.tapes [] from SupportLift.tapes E bits prior]
      exact lr
    have acceptedExists:=CloseoutRowsCircuitGuarded.accepted
      (first source a k CH Cpad cutoff D G copies e E den delta code sym)
      (second source (FamilySupport.Actual sym km q) a k D G e E K) (fun scanned=>scanned (guardSlot source a k D G e E))
      (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
      (2*ColdFamily.tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle) (fun _=>0)
      (input source a k D G e E (List.ofFn x) raw bits) lifted last firstRun nextRun (scan.trans live)
    let actual:=Classical.choose acceptedExists
    have af:=Classical.choose_spec acceptedExists
    have ar:=af.1
    have ast:=af.2.1
    have ah:=af.2.2.1
    have atapes:=af.2.2.2
    have bound:ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad+1+
        2*ColdFamily.tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle+1≤
        2*ColdFamily.budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad:=by
      rw [ColdFamily.budget,if_pos live,ho.1]
      simp only [Option.elim_some]
      dsimp only [oracle]
      omega
    have paid:=RunFuel.enlarge ar bound
    have flag:ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=
        ColdFamily.familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad oracle:=by
      rw [ColdFamily.passed,live,ho.1];rfl
    have nativeRich := ColdLegal.cache_fields_with_originals source a k CH Cpad cutoff D G copies e den delta code sym
      x raw hpad hD hden hraw prior pf.1 oracle ho.1 live
    refine ⟨actual,?_,paid,ast.trans bound,(congrFun ah _).trans lh,?_,?_⟩
    · intro _
      have saved := lf.2.2.2.2.1 (ColdFamily.originalTape source a k D G e)
        (ColdFamily.fields_ne_originalTape source a k D G e E)
      have firstT := oneT (ColdLegal.originalTape source a k D G e)
      have retained := saved.2.trans (firstT.trans nativeRich.1)
      exact (congrFun atapes _).trans retained
    · exact (congrArg (fun word=>readTapeBit word 0) ((congrFun atapes _).trans lt)).trans flag.symm
    · intro accepted
      refine ⟨oracle,ho.1,ho.2,?_⟩
      have hret:=good (flag.symm.trans accepted)
      refine ⟨transport (P:=fun heads tapes=>FamilySupport.retained sym (FamilyCapacity.value E K n) V C T
        r.arity (LegalPolicy.W e den r.arity)
        (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) (LegalPolicy.W e den r.arity)) km q bits []
        (heads ∘ familySlots source a k D G e E) (tapes ∘ familySlots source a k D G e E)) ah atapes hret,?_⟩
      have nativeCache := nativeRich.2
      intro j
      by_cases hj:j=13
      · subst j
        have domain:=ColdFamily.retained_domain sym (FamilyCapacity.value E K n) V C T r.arity
          (LegalPolicy.W e den r.arity)
          (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) (LegalPolicy.W e den r.arity))
          km q bits _ _ hret.1
        have lastH:last.final.heads (cache source a k D G e E 13)=1:=
          (congrArg last.final.heads (domain_cache source a k D G e E).symm).trans domain.1
        have lastT:last.final.tapes (cache source a k D G e E 13)=UnaryTemplate.tape r.arity:=
          (congrArg last.final.tapes (domain_cache source a k D G e E).symm).trans domain.2
        exact ⟨(congrFun atapes _).trans lastT,(congrFun ah _).trans lastH⟩
      · have keep:=lf.2.2.2.2.1 (ColdFamily.old source a k D G e (ColdLegal.cache source a k D G e j))
          (ColdFamily.fields_ne_cache source a k D G e E j hj)
        have lastH:= (congrArg last.final.heads (cache_old source a k D G e E j)).trans keep.1
        have lastT:= (congrArg last.final.tapes (cache_old source a k D G e E j)).trans keep.2
        exact ⟨(congrFun atapes _).trans (lastT.trans ((oneT _).trans (nativeCache j).1)),
          (congrFun ah _).trans (lastH.trans ((oneH _).trans (nativeCache j).2))⟩
  · have rejectedExists:=CloseoutRowsCircuitGuarded.rejected
      (first source a k CH Cpad cutoff D G copies e E den delta code sym)
      (second source (FamilySupport.Actual sym km q) a k D G e E K) (fun scanned=>scanned (guardSlot source a k D G e E))
      (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad) (fun _=>0)
      (input source a k D G e E (List.ofFn x) raw bits) lifted firstRun (scan.trans (Bool.eq_false_iff.mpr live))
    let actual:=Classical.choose rejectedExists
    have af:=Classical.choose_spec rejectedExists
    have ar:=af.1
    have ast:=af.2.1
    have ah:=af.2.2.1
    have atapes:=af.2.2.2
    have bound:ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad+1≤
        2*ColdFamily.budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad:=by
      simp only [ColdFamily.budget,if_neg live,Nat.add_zero]
      omega
    have paid:=RunFuel.enlarge ar bound
    have no:ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=false:=by
      simp only [ColdFamily.passed,Bool.eq_false_iff.mpr live,Bool.false_and]
    have fresh:familySlots source a k D G e E 724=
        SupportLift.fresh (t:=ColdLegal.tapes source a k D G e) E 724:=
      (family_old source a k D G e E 724).trans
        (congrArg (fun i=>i.castAdd 1) (ColdFamily.verdict_fresh source a k D G e E))
    have lastH:lifted.final.heads (familySlots source a k D G e E 724)=0:=by
      rw [fresh]
      exact SupportLift.heads_new E bits prior 724
    have lastT:lifted.final.tapes (familySlots source a k D G e E 724)=[]:=by
      rw [fresh]
      exact SupportLift.tapes_new E bits prior 724
    exact ⟨actual,(fun yes=>False.elim (Bool.noConfusion (no.symm.trans yes))),
      paid,ast.trans bound,(congrFun ah _).trans lastH,
      (congrArg (fun word=>readTapeBit word 0) ((congrFun atapes _).trans lastT)).trans no.symm,
      fun yes=>False.elim (Bool.noConfusion (no.symm.trans yes))⟩

theorem family_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool)
    (hpad:k+3≤Cpad) (hD:1≤D) (hden:0<den) (hK:0<K) (hcut:2^a.minimumArity≤cutoff)
    (hd:0<delta) (hh:delta<1/2) (hc:1≤copies)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E)
    (hraw:16*raw.length≤n) (hbits:16*bits.length≤n) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    let fuel:=2*ColdFamily.budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad
    ∃ actual,run (actualMachine source a k CH Cpad cutoff D G copies e E K den km delta q code sym)
      fuel (input source a k D G e E (List.ofFn x) raw bits)=some actual ∧
      actual.steps≤fuel ∧ actual.final.heads (familySlots source a k D G e E 724)=0 ∧
      readTapeBit (actual.final.tapes (familySlots source a k D G e E 724)) 0=
        ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad ∧
      (ColdFamily.passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=true→
        ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle ∧
          oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
          let r:=ColdNative.request source a k CH Cpad code x hpad oracle
          let cb:=(a.output r).clauseBits
          let W:=LegalPolicy.W e den r.arity
          FamilySupport.retained sym (FamilyCapacity.value E K n) ((a.output r).systematicBits+(a.output r).auxiliaryBits)
            (FamilyResources.coefficientCap delta copies D r.arity cb) (FamilyResources.termCap delta copies D r.arity cb)
            r.arity W (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) W) km q bits []
            (actual.final.heads ∘ familySlots source a k D G e E)
            (actual.final.tapes ∘ familySlots source a k D G e E) ∧
          ∀ j:Fin 19,actual.final.tapes (cache source a k D G e E j)=
            PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
              (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j ∧
            actual.final.heads (cache source a k D G e E j)=PCPPQueryClauseReuse.heads j)  := by
  have enriched := family_run_with_originals source a k CH Cpad cutoff D G copies e E K den delta code sym
    x raw bits hpad hD hden hK hcut hd hh hc hbudget hraw hbits
  obtain ⟨actual, _original, facts⟩ := enriched
  exact ⟨actual, facts⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
