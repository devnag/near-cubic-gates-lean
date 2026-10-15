import Proof.CaseAnalysis.WitnessFamilyLiftHandoff

/-! Original source/oracle guards, one source policy, paid P/H, and the
complete actual family machine form one cold all-raw execution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open CompetitorSumFold CompetitorSumWidth RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem family_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E K den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool)
    (hpad : k+3≤Cpad) (hD : 1≤D) (hden : 0<den) (hK : 0<K) (hcut : 2^a.minimumArity≤cutoff)
    (hd : 0<delta) (hh : delta<1/2) (hc : 1≤copies)
    (hbudget : ∀ N,FamilyResources.capacity (scale source a G D copies delta N)≤K*(N+1)^E)
    (hraw : 16*raw.length≤n) (hbits : 16*bits.length≤n) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    ∃ actual,run (machine source a k CH Cpad cutoff D G copies e E K den km delta q code sym)
      (budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad)
      (input source a k D G e E (List.ofFn x) raw bits)=some actual ∧
      actual.steps≤budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad ∧
      actual.final.heads (familySlots source a k D G e E 724)=0 ∧
      readTapeBit (actual.final.tapes (familySlots source a k D G e E 724)) 0=
        passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad ∧
      (passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=true→
        ∃ oracle,decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle ∧
          oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
          let r:=ColdNative.request source a k CH Cpad code x hpad oracle
          let cb:=(a.output r).clauseBits
          let W:=LegalPolicy.W e den r.arity
          retained sym (FamilyCapacity.value E K n) ((a.output r).systematicBits+(a.output r).auxiliaryBits)
            (FamilyResources.coefficientCap delta copies D r.arity cb) (FamilyResources.termCap delta copies D r.arity cb)
            r.arity W (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) W) km q bits
            (actual.final.heads ∘ familySlots source a k D G e E)
            (actual.final.tapes ∘ familySlots source a k D G e E)):=by
  let km:=CloseoutMassThreshold.literalWidth delta copies
  let q:=CloseoutSampledWitness.massCap delta copies
  let P:=FamilyCapacity.value E K n
  let S:=scale source a G D copies delta n
  have priorExists:=ColdLegal.legal_run source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad hD hden hraw
  let prior : ExecutionReceipt (ColdLegal.tapes source a k D G e) _:=Classical.choose priorExists
  have pf:=Classical.choose_spec priorExists
  let one : ExecutionReceipt (base source a k D G e) _:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>frame bits) prior
  let lifted : ExecutionReceipt (base source a k D G e+FamilyCapacity.Call.extra E+FamilyCold.Call.extra) _:=ColdFamilyLift.receipt E bits prior
  have firstRun:=ColdFamilyLift.run_lift E
    (ColdLegal.machine source a k CH Cpad cutoff D G copies e den delta code sym)
    (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
    (ColdLegal.input source a k D G e (List.ofFn x) raw) bits prior pf.1
  have flagH:lifted.final.heads (guardSlot source a k D G e E)=0:=
    (ColdFamilyLift.heads_old E bits prior _).trans pf.2.2.2.2.1
  have flagT:readTapeBit (lifted.final.tapes (guardSlot source a k D G e E)) 0=
      ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw:=by
    have kept:=ColdFamilyLift.tapes_old E bits prior (ColdLegal.flagSlot source a k D G e)
    exact (congrArg (fun word=>readTapeBit word 0) kept).trans pf.2.2.2.2.2.1
  have oneT (i : Fin (ColdLegal.tapes source a k D G e)) :
      one.final.tapes (old source a k D G e i)=prior.final.tapes i:=
    TapeEmbedding.receipt_tapes_old _ _ prior i
  have oneH (i : Fin (ColdLegal.tapes source a k D G e)) :
      one.final.heads (old source a k D G e i)=prior.final.heads i:=
    TapeEmbedding.receipt_heads_old _ _ prior i
  have onePolicy:one.final.tapes ∘ policy source a k D G e=
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
    have fit:=ColdFamilyResources.native_fits a source.coefficient source.degrees.queries G D delta copies K E hbudget
      (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
      (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
      (PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad)
      (PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad) x oracle n bits core
      (by simpa only [List.length_ofFn] using guards.2.1) (by omega)
      (ColdFamilyGuards.query_bound source k CH Cpad code (List.ofFn x)) ho.2
    have legalFields:=pf.2.2.2.2.2.2 oracle ho.1 live
    have hn:n+1≤S:=by dsimp only [S,scale,FamilyResources.sourceScale,FamilyResources.scale];omega
    have threshold:=CloseoutMassThreshold.threshold_fits delta hd hh copies (CorePolicy.q0 D r.arity) cb hc
    have lastExists:=FamilyFromPolicy.family_run e E K n den copies r.arity (CorePolicy.q0 D r.arity) cb S V C km delta q sym
      (lengthSlot source a k D G e) (countSlot source a k D G e) (rawSlot source a k D G e)
      (policy source a k D G e) one.final.tapes one.final.heads bits hK
      (policy_injective source a k D G e) (count_ne_raw source a k D G e)
      (count_outside source a k D G e) (raw_outside source a k D G e)
      ((oneT _).trans pf.2.2.1)
      ((oneH _).trans pf.2.2.2.1)
      ((oneT _).trans legalFields.1)
      ((oneH _).trans legalFields.2.1)
      (TapeEmbedding.receipt_tapes_new _ _ prior (0 : Fin 1))
      (TapeEmbedding.receipt_heads_new _ _ prior (0 : Fin 1))
      (by rw [onePolicy];exact legalFields.2.2.2)
      (fun i=>(oneH _).trans (legalFields.2.2.1 i))
      fit.1 (by omega) fit.2 (FamilyResources.coefficient_positive delta copies D r.arity cb)
      (CloseoutSampledWitness.mass_nonneg delta hd hh copies)
      (CloseoutMassThreshold.shared_fits delta hd hh copies (CorePolicy.q0 D r.arity) cb T hc)
      threshold.2.1 threshold.2.2
    let extra:=Classical.choose lastExists
    let last:=Classical.choose (Classical.choose_spec lastExists)
    have lf:=Classical.choose_spec (Classical.choose_spec lastExists)
    have lh:=ColdFamilyLift.heads E bits prior
    have lt:=ColdFamilyLift.tapes E bits prior
    have nextRun:runFrom (second source a k D G e E K km q sym)
        (tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle)
        (RecoveryCalls.restarted (second source a k D G e E K km q sym) lifted.final.heads lifted.final.tapes)=some last:=by
      rw [lh,lt]
      exact lf.1
    have actualExists:=CloseoutRowsCircuitGuarded.accepted
      (first source a k CH Cpad cutoff D G copies e E den delta code sym)
      (second source a k D G e E K km q sym) (fun scanned=>scanned (guardSlot source a k D G e E))
      (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad)
      (tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle) (fun _=>0)
      (input source a k D G e E (List.ofFn x) raw bits) lifted last firstRun nextRun (scan.trans live)
    let actual:=Classical.choose actualExists
    have af:=Classical.choose_spec actualExists
    have he:budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad=
        ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad+1+
          tailBudget source a k CH Cpad D G copies E K delta code x bits hpad oracle+1:=by
      rw [budget,if_pos live,ho.1]
      exact (Nat.add_assoc _ _ _).symm
    have flag:passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=
        familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad oracle:=by
      rw [passed,live,ho.1]
      rfl
    refine ⟨actual,?_,?_,?_,?_,?_⟩
    · exact (congrArg (fun fuel=>run
        (machine source a k CH Cpad cutoff D G copies e E K den km delta q code sym) fuel
        (input source a k D G e E (List.ofFn x) raw bits)) he).trans af.1
    · exact af.2.1.trans_eq he.symm
    · exact (congrFun af.2.2.1 _).trans lf.2.2.1
    · have tape:=(congrFun af.2.2.2 _).trans lf.2.2.2.1
      exact (congrArg (fun word=>readTapeBit word 0) tape).trans flag.symm
    · intro accepted
      have yes:familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad oracle=true:=flag.symm.trans accepted
      let after:=Classical.choose (lf.2.2.2.2.2.2 yes)
      have good:=Classical.choose_spec (lf.2.2.2.2.2.2 yes)
      refine ⟨oracle,ho.1,ho.2,extra,after,lf.2.2.2.2.1,?_,?_,good.2.2⟩
      · exact (congrArg (fun hs=>hs ∘ familySlots source a k D G e E) af.2.2.1).trans good.1
      · exact (congrArg (fun ts=>ts ∘ familySlots source a k D G e E) af.2.2.2).trans good.2.1
  · have stopped:=CloseoutRowsCircuitGuarded.rejected
      (first source a k CH Cpad cutoff D G copies e E den delta code sym)
      (second source a k D G e E K km q sym) (fun scanned=>scanned (guardSlot source a k D G e E))
      (ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad) (fun _=>0)
      (input source a k D G e E (List.ofFn x) raw bits) lifted firstRun (scan.trans (Bool.eq_false_iff.mpr live))
    let actual:=Classical.choose stopped
    have af:=Classical.choose_spec stopped
    have he:budget source a k CH Cpad cutoff D G copies e E K den delta code sym x raw bits hpad=
        ColdLegal.budget source a k CH Cpad cutoff D G copies e den delta code sym x raw hpad+1:=by
      simp only [budget,if_neg live,Nat.add_zero]
    have no:passed source a k CH Cpad cutoff D G copies e den delta code sym x raw bits hpad=false:=by
      simp only [passed,Bool.eq_false_iff.mpr live,Bool.false_and]
    refine ⟨actual,?_,?_,?_,?_,fun yes=>False.elim (Bool.noConfusion (no.symm.trans yes))⟩
    · exact (congrArg (fun fuel=>run
        (machine source a k CH Cpad cutoff D G copies e E K den km delta q code sym) fuel
        (input source a k D G e E (List.ofFn x) raw bits)) he).trans af.1
    · exact af.2.1.trans_eq he.symm
    · have last:lifted.final.heads (familySlots source a k D G e E 724)=0:=by
        rw [verdict_fresh]
        exact ColdFamilyLift.heads_new E bits prior 724
      exact (congrFun af.2.2.1 _).trans last
    · have last:lifted.final.tapes (familySlots source a k D G e E 724)=[]:=by
        rw [verdict_fresh]
        exact ColdFamilyLift.tapes_new E bits prior 724
      exact (congrArg (fun word=>readTapeBit word 0) ((congrFun af.2.2.2 _).trans last)).trans no.symm

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
