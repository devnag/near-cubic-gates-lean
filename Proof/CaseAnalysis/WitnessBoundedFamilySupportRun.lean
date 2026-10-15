import Proof.CaseAnalysis.WitnessBoundedFamilySupportPorts
import Proof.CaseAnalysis.WitnessFamilySupportRun

/-! One bounded header runs exactly one actual strengthened cold family.
The enclosing receipt retains every selected child field, so subsequent
row consumers use this same source call and its original cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def actualMachine (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen km : ℕ)
    (delta q : ℚ) (code : List Bool):=
  machine source (fun sym=>⟨_,FamilySupport.Actual sym km q⟩) a k CH Cpad cutoff D G copies E K symDen thrDen delta code

def Selected (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen km : ℕ)
    (delta q : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3≤Cpad)
    (sym : Bool) (heads : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→ℕ)
    (data : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→List Bool) : Prop :=
  ∃ child,run (ColdFamilySupport.actualMachine source a k CH Cpad cutoff D G copies (BoundedFamily.exponent sym) E K
      (BoundedFamily.denominator sym symDen thrDen) km delta q code sym)
      (2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym)
      (ColdFamilySupport.input source a k D G (BoundedFamily.exponent sym) E (List.ofFn x)
        (BoundedFields.oracle bits) (BoundedFields.family bits))=some child ∧
    (∀ i,heads (slots source a k D G E sym i)=child.final.heads i) ∧
    ∀ i,data (slots source a k D G E sym i)=child.final.tapes i

private theorem bounded_output_witness (x bits : List Bool) (scratch : ℕ) :
    CompetitorWitnessBounded.output x bits scratch 1 = frame bits := by
  have triple1 : CompetitorWitnessTriple.stage x bits 6 1 = frame bits := by
    rw [CompetitorWitnessTriple.stage_stable x bits 1 5 1 (by decide)]
    rw [CompetitorWitnessTriple.stage, dif_pos (by decide : 0 < 6)]
    change RecoveryRootRound.install (CompetitorWitnessTriple.slots 0) _ _ (CompetitorWitnessTriple.slots 0 0) = _
    rw [RecoveryRootRound.install_slot _ (CompetitorWitnessTriple.slots_injective 0)]
    rfl
  have header1 : CompetitorWitnessHeader.output x bits 1 = frame bits := by
    rw [CompetitorWitnessHeader.output, RecoveryRootRound.install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    rw [CompetitorWitnessHeader.before_other x bits 5 1 (by intro j i; fin_cases j <;> fin_cases i <;> decide)]
    exact triple1
  rw [CompetitorWitnessBounded.output]
  split_ifs
  · exact header1
  · change CompetitorWitnessHeader.input x bits 1 = frame bits
    rw [CompetitorWitnessHeader.input_eq]
    rfl

theorem bounded_run_with_originals (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad:k+3≤Cpad) (hD:1≤D) (hsym:0<symDen) (hthr:0<thrDen) (hK:0<K)
    (hcut:2^a.minimumArity≤cutoff) (hd:0<delta) (hh:delta<1/2) (hc:1≤copies)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    let fuel:=2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad
    ∃ actual,
      (BoundedFamily.headerValid (List.ofFn x) bits=true →
        actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1)=frame bits ∧
        actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)=[BoundedFields.symmetric bits]) ∧
      run (actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
      fuel (input source a k D G E (List.ofFn x) bits)=some actual ∧ actual.steps≤fuel ∧
      actual.final.heads (flag source a k D G E)=0 ∧
      readTapeBit (actual.final.tapes (flag source a k D G E)) 0=
        BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad ∧
      (BoundedFamily.headerValid (List.ofFn x) bits=true→
        Selected source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code x bits hpad
          (BoundedFields.symmetric bits) actual.final.heads actual.final.tapes) := by
  classical
  let km:=CloseoutMassThreshold.literalWidth delta copies
  let q:=CloseoutSampledWitness.massCap delta copies
  let pref:=first source a k D G E
  let yes:=branch source (FamilySupport.Actual true km q) a k CH Cpad cutoff D G copies E K symDen thrDen delta code true
  let no:=branch source (FamilySupport.Actual false km q) a k CH Cpad cutoff D G copies E K symDen thrDen delta code false
  have headerExists:=header_run source a k D G E (List.ofFn x) bits
  let scratch:=Classical.choose headerExists
  let prior:=Classical.choose (Classical.choose_spec headerExists)
  have pf:=Classical.choose_spec (Classical.choose_spec headerExists)
  have priorHeads:=pf.2.1
  have priorTapes:=pf.2.2
  have scan:good source a k D G E prior.final.scanned=BoundedFamily.headerValid (List.ofFn x) bits:=by
    change readTapeBit _ (prior.final.heads ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 147).castAdd 1))=_
    rw [priorHeads,priorTapes,header_old]
    apply Bool.eq_iff_iff.mpr
    exact (CompetitorWitnessBounded.output_valid _ _ _).trans (by simp only [BoundedFamily.headerValid,decide_eq_true_eq])
  by_cases live:BoundedFamily.headerValid (List.ofFn x) bits=true
  · have valid:readTapeBit (CompetitorWitnessBounded.output (List.ofFn x) bits scratch 147) 0=true:=
      (CompetitorWitnessBounded.output_valid _ _ _).mpr (of_decide_eq_true live)
    have fields:=BoundedFields.fields (List.ofFn x) bits scratch valid
    have rawCap:16*(BoundedFields.oracle bits).length≤n:=by simpa only [List.length_ofFn] using fields.1
    have familyCap:16*(BoundedFields.family bits).length≤n:=by simpa only [List.length_ofFn] using fields.2.1
    have modeScan:mode source a k D G E prior.final.scanned=BoundedFields.symmetric bits:=by
      change readTapeBit _ (prior.final.heads ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1))=_
      rw [priorHeads,priorTapes,header_old,fields.2.2.2.2.2]
      rfl
    have finish (sym : Bool) (selected:BoundedFields.symmetric bits=sym) :
        ∃ actual,
          (actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1)=frame bits ∧
            actual.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)=[sym]) ∧
          run (actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
          (CompetitorWitnessBounded.budget (List.ofFn x)+1+
            2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1)
          (input source a k D G E (List.ofFn x) bits)=some actual ∧
          actual.steps≤CompetitorWitnessBounded.budget (List.ofFn x)+1+
            2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1 ∧
          actual.final.heads (flag source a k D G E)=0 ∧
          readTapeBit (actual.final.tapes (flag source a k D G E)) 0=
            ColdFamily.passed source a k CH Cpad cutoff D G copies (BoundedFamily.exponent sym)
              (BoundedFamily.denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits) hpad ∧
          Selected source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code x bits hpad sym
            actual.final.heads actual.final.tapes := by
      have childExists:=ColdFamilySupport.family_run source a k CH Cpad cutoff D G copies (BoundedFamily.exponent sym) E K
        (BoundedFamily.denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits)
        hpad hD (by unfold BoundedFamily.denominator;split_ifs <;> assumption) hK hcut hd hh hc hbudget rawCap familyCap
      let child:=Classical.choose childExists
      have cf:=Classical.choose_spec childExists
      have docked:=RecoveryFocus.dock (slots source a k D G E sym) (slots_injective source a k D G E sym)
        _ _ prior.final.heads prior.final.tapes _
        (fun _=>congrFun priorHeads _) (fun j=>by rw [priorTapes];exact input_data source a k D G E sym _ _ _ valid j)
        child cf.1
      let last:=Classical.choose docked
      have lf:=Classical.choose_spec docked
      have controlled:∃ actual,runFrom (HeaderSwitch.machine pref yes no (good source a k D G E) (mode source a k D G E))
          (CompetitorWitnessBounded.budget (List.ofFn x)+1+
            2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1)
          ⟨(HeaderSwitch.machine pref yes no (good source a k D G E) (mode source a k D G E)).start,
            fun _=>0,input source a k D G E (List.ofFn x) bits⟩=some actual ∧
          actual.steps≤CompetitorWitnessBounded.budget (List.ofFn x)+1+
            2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1 ∧
          actual.final.heads=last.final.heads ∧ actual.final.tapes=last.final.tapes := by
        cases sym
        · exact HeaderSwitch.accepted pref yes no (good source a k D G E) (mode source a k D G E)
            2 (Or.inr rfl) _ _ _ _ prior last pf.1 lf.1 (scan.trans live)
            (congrArg (fun b=>if b then (1:Fin 3) else 2) (modeScan.trans selected)).symm
        · exact HeaderSwitch.accepted pref yes no (good source a k D G E) (mode source a k D G E)
            1 (Or.inl rfl) _ _ _ _ prior last pf.1 lf.1 (scan.trans live)
            (congrArg (fun b=>if b then (1:Fin 3) else 2) (modeScan.trans selected)).symm
      let actual:=Classical.choose controlled
      have af:=Classical.choose_spec controlled
      have heads (i):actual.final.heads (slots source a k D G E sym i)=child.final.heads i:=
        (congrFun af.2.2.1 _).trans (lf.2.2.2.1 i)
      have tapes (i):actual.final.tapes (slots source a k D G E sym i)=child.final.tapes i:=
        (congrFun af.2.2.2 _).trans (lf.2.2.2.2.1 i)
      have hflag:actual.final.heads (flag source a k D G E)=0:=
        (congrArg actual.final.heads (family_flag_slot source a k D G E sym).symm).trans
          ((heads _).trans cf.2.2.1)
      have tflag:=
        (congrArg (fun i=>readTapeBit (actual.final.tapes i) 0) (family_flag_slot source a k D G E sym).symm).trans
          ((congrArg (fun word=>readTapeBit word 0) (tapes _)).trans cf.2.2.2.1)
      have outside (j : Fin 150) (hj : j≠0 ∧ j≠78 ∧ j≠118) :
          ∀ i, slots source a k D G E sym i ≠ (HeaderDock.old (BoundedFamily.workspace source a k D G E) j).castAdd 1 := by
        apply SupportDock.outside
        exact HeaderDock.untouched_header _ _ _ _ _ _ j hj
      have keepWitness := lf.2.2.2.2.2 ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1) (outside 1 (by decide))
      have keepMode := lf.2.2.2.2.2 ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1) (outside 142 (by decide))
      have priorWitness : prior.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1)=frame bits := by
        rw [priorTapes, header_old]
        exact bounded_output_witness (List.ofFn x) bits scratch
      have priorMode : prior.final.tapes ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)=[sym] := by
        rw [priorTapes, header_old]
        exact fields.2.2.2.2.2.trans (congrArg List.singleton selected)
      have witnessT := (congrFun af.2.2.2 ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1)).trans (keepWitness.2.trans priorWitness)
      have modeT := (congrFun af.2.2.2 ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)).trans (keepMode.2.trans priorMode)
      exact ⟨actual,⟨witnessT,modeT⟩,af.1,af.2.1,hflag,tflag,child,cf.1,heads,tapes⟩
    have complete:=finish (BoundedFields.symmetric bits) rfl
    let actual:=Classical.choose complete
    have originals := (Classical.choose_spec complete).1
    have af:=(Classical.choose_spec complete).2
    have bound:CompetitorWitnessBounded.budget (List.ofFn x)+1+
        2*BoundedFamily.childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad (BoundedFields.symmetric bits)+1≤
        2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad:=by
      rw [BoundedFamily.budget,if_pos live]
      omega
    refine ⟨actual,(fun _=>originals),RunFuel.enlarge af.1 bound,af.2.1.trans bound,af.2.2.1,?_,fun _=>af.2.2.2.2⟩
    simpa only [BoundedFamily.passed,live,Bool.true_and] using af.2.2.2.1
  · have stopped:=HeaderSwitch.rejected pref yes no (good source a k D G E) (mode source a k D G E)
      (CompetitorWitnessBounded.budget (List.ofFn x)) (fun _=>0) (input source a k D G E (List.ofFn x) bits)
      prior pf.1 (scan.trans (Bool.eq_false_iff.mpr live))
    let actual:=Classical.choose stopped
    have af:=Classical.choose_spec stopped
    have bound:CompetitorWitnessBounded.budget (List.ofFn x)+1≤
        2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad:=by
      rw [BoundedFamily.budget,if_neg live]
      omega
    have hflag:actual.final.heads (flag source a k D G E)=0:=
      (congrFun af.2.2.1 _).trans (congrFun priorHeads _)
    have tflag:actual.final.tapes (flag source a k D G E)=[]:=
      (congrFun af.2.2.2 _).trans ((congrFun priorTapes _).trans (header_flag source a k D G E _))
    refine ⟨actual,(fun yes=>False.elim (live yes)),RunFuel.enlarge af.1 bound,af.2.1.trans bound,hflag,?_,fun yes=>False.elim (live yes)⟩
    rw [tflag]
    simp only [BoundedFamily.passed,Bool.eq_false_iff.mpr live,Bool.false_and]
    rfl

theorem bounded_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad:k+3≤Cpad) (hD:1≤D) (hsym:0<symDen) (hthr:0<thrDen) (hK:0<K)
    (hcut:2^a.minimumArity≤cutoff) (hd:0<delta) (hh:delta<1/2) (hc:1≤copies)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    let fuel:=2*BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad
    ∃ actual,run (actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
      fuel (input source a k D G E (List.ofFn x) bits)=some actual ∧ actual.steps≤fuel ∧
      actual.final.heads (flag source a k D G E)=0 ∧
      readTapeBit (actual.final.tapes (flag source a k D G E)) 0=
        BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad ∧
      (BoundedFamily.headerValid (List.ofFn x) bits=true→
        Selected source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code x bits hpad
          (BoundedFields.symmetric bits) actual.final.heads actual.final.tapes)  := by
  have enriched := bounded_run_with_originals source a k CH Cpad cutoff D G copies E K symDen thrDen
    delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
  obtain ⟨actual, _originals, facts⟩ := enriched
  exact ⟨actual, facts⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
