import Proof.CaseAnalysis.WitnessBoundedFamilyCall
import Proof.CaseAnalysis.WitnessHeaderVerdict

/-! One original bounded witness enters exactly one actual cold family.
Every malformed header, including the zero-length input, has a paid
rejecting run; successful headers retain the selected family's verdict. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem bounded_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad:k+3 ≤ Cpad) (hD:1 ≤ D) (hsym:0<symDen) (hthr:0<thrDen) (hK:0<K)
    (hcut:2^a.minimumArity ≤ cutoff) (hd:0<delta) (hh:delta<1/2) (hc:1 ≤ copies)
    (hbudget:∀N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N) ≤ K*(N+1)^E) :
    let km:=CloseoutMassThreshold.literalWidth delta copies
    let q:=CloseoutSampledWitness.massCap delta copies
    ∃ actual,run (machine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
      (budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad)
      (input source a k D G E (List.ofFn x) bits)=some actual ∧
      actual.steps ≤ budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad ∧
      actual.final.heads (flag source a k D G E)=0 ∧
      readTapeBit (actual.final.tapes (flag source a k D G E)) 0=
        passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad := by
  classical
  let km:=CloseoutMassThreshold.literalWidth delta copies
  let q:=CloseoutSampledWitness.massCap delta copies
  let pref:=first source a k D G E
  let yes:=branch source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code true
  let no:=branch source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code false
  have headerExists:=header_run source a k D G E (List.ofFn x) bits
  let scratch:=Classical.choose headerExists
  let prior : ExecutionReceipt (150+(workspace source a k D G E+1)) _:=
    Classical.choose (Classical.choose_spec headerExists).2
  have pf:=Classical.choose_spec (Classical.choose_spec headerExists).2
  have priorHeads:prior.final.heads=(fun _=>0):=pf.2.2
  have priorTapes:prior.final.tapes=HeaderDock.input (workspace source a k D G E)
      (CompetitorWitnessBounded.output (List.ofFn x) bits scratch):=pf.2.1
  have scan:good source a k D G E prior.final.scanned=headerValid (List.ofFn x) bits:=by
    change readTapeBit _ (prior.final.heads (HeaderDock.old (workspace source a k D G E) 147))=_
    rw [priorHeads,priorTapes,HeaderDock.input,HeaderDock.old,Fin.addCases_left]
    apply Bool.eq_iff_iff.mpr
    exact (CompetitorWitnessBounded.output_valid _ _ _).trans (by simp only [headerValid,decide_eq_true_eq])
  by_cases live:headerValid (List.ofFn x) bits=true
  · have valid:readTapeBit (CompetitorWitnessBounded.output (List.ofFn x) bits scratch 147) 0=true:=by
      apply (CompetitorWitnessBounded.output_valid _ _ _).mpr
      exact of_decide_eq_true live
    have fields:=BoundedFields.fields (List.ofFn x) bits scratch valid
    have rawCap:16*(BoundedFields.oracle bits).length ≤ n:=by simpa only [List.length_ofFn] using fields.1
    have familyCap:16*(BoundedFields.family bits).length ≤ n:=by simpa only [List.length_ofFn] using fields.2.1
    have modeScan:mode source a k D G E prior.final.scanned=BoundedFields.symmetric bits:=by
      change readTapeBit _ (prior.final.heads (HeaderDock.old (workspace source a k D G E) 142))=_
      rw [priorHeads,priorTapes,HeaderDock.input,HeaderDock.old,Fin.addCases_left,fields.2.2.2.2.2]
      rfl
    have finish (sym : Bool) (selected:BoundedFields.symmetric bits=sym) :
        ∃ actual,runFrom (HeaderSwitch.machine pref yes no (good source a k D G E) (mode source a k D G E))
          (CompetitorWitnessBounded.budget (List.ofFn x)+1+
            childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1)
          ⟨(HeaderSwitch.machine pref yes no (good source a k D G E) (mode source a k D G E)).start,fun _=>0,input source a k D G E (List.ofFn x) bits⟩=some actual ∧
          actual.steps ≤ CompetitorWitnessBounded.budget (List.ofFn x)+1+
            childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad sym+1 ∧
          actual.final.heads (flag source a k D G E)=0 ∧
          readTapeBit (actual.final.tapes (flag source a k D G E)) 0=
            ColdFamily.passed source a k CH Cpad cutoff D G copies (exponent sym)
              (denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits) hpad := by
      have childExists:=ColdFamily.family_run source a k CH Cpad cutoff D G copies (exponent sym) E K
        (denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits)
        hpad hD (by unfold denominator;split_ifs <;> assumption) hK hcut hd hh hc hbudget rawCap familyCap
      let child:=Classical.choose childExists
      have cf:=Classical.choose_spec childExists
      have docked:=RecoveryFocus.dock (slots source a k D G E sym) (slots_injective source a k D G E sym)
        _ _ prior.final.heads prior.final.tapes _
        (fun j=>congrFun priorHeads _) (fun j=>by rw [priorTapes];exact input_data source a k D G E sym _ _ _ valid j)
        child cf.1
      let last : ExecutionReceipt (150+(workspace source a k D G E+1)) _:=Classical.choose docked
      have lf:=Classical.choose_spec docked
      have lastHead:last.final.heads (flag source a k D G E)=0:=
        (congrArg last.final.heads (flag_slot source a k D G E sym).symm).trans
          ((lf.2.2.2.1 _).trans cf.2.2.1)
      have lastFlag:readTapeBit (last.final.tapes (flag source a k D G E)) 0=
          ColdFamily.passed source a k CH Cpad cutoff D G copies (exponent sym)
            (denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits) hpad:=
        (congrArg (fun j=>readTapeBit (last.final.tapes j) 0) (flag_slot source a k D G E sym).symm).trans
          ((congrArg (fun word=>readTapeBit word 0) (lf.2.2.2.2.1 _)).trans cf.2.2.2.1)
      cases sym
      · exact HeaderSwitch.accepted_flag pref yes no (good source a k D G E) (mode source a k D G E)
          2 (Or.inr rfl) _ _ _ _ prior last pf.1 lf.1 (scan.trans live)
          (congrArg (fun b=>if b then (1:Fin 3) else 2) (modeScan.trans selected)).symm
          _ _ lastHead lastFlag
      · exact HeaderSwitch.accepted_flag pref yes no (good source a k D G E) (mode source a k D G E)
          1 (Or.inl rfl) _ _ _ _ prior last pf.1 lf.1 (scan.trans live)
          (congrArg (fun b=>if b then (1:Fin 3) else 2) (modeScan.trans selected)).symm
          _ _ lastHead lastFlag
    have complete:=finish (BoundedFields.symmetric bits) rfl
    let actual : ExecutionReceipt (150+(workspace source a k D G E+1)) _:=Classical.choose complete
    have af:=Classical.choose_spec complete
    have he:budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad=
        CompetitorWitnessBounded.budget (List.ofFn x)+1+
          childBudget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad (BoundedFields.symmetric bits)+1:=by
      rw [budget,live];simp only [if_true,Nat.add_assoc]
    refine ⟨actual,?_,af.2.1.trans_eq he.symm,af.2.2.1,?_⟩
    · exact (congrArg (fun fuel=>run (machine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
        fuel (input source a k D G E (List.ofFn x) bits)) he).trans af.1
    · simpa only [passed,live,Bool.true_and] using af.2.2.2
  · have priorFlag:readTapeBit (prior.final.tapes (flag source a k D G E)) 0=false:=by
      rw [priorTapes]
      rfl
    have stopped:=HeaderSwitch.rejected_flag pref yes no (good source a k D G E) (mode source a k D G E)
      (CompetitorWitnessBounded.budget (List.ofFn x)) (fun _=>0) (input source a k D G E (List.ofFn x) bits)
      prior pf.1 (scan.trans (Bool.eq_false_iff.mpr live)) (flag source a k D G E) false
      (congrFun priorHeads _) priorFlag
    let actual : ExecutionReceipt (150+(workspace source a k D G E+1)) _:=Classical.choose stopped
    have af:=Classical.choose_spec stopped
    have he:budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad=
        CompetitorWitnessBounded.budget (List.ofFn x)+1:=by rw [budget,if_neg live,Nat.add_zero]
    refine ⟨actual,?_,af.2.1.trans_eq he.symm,af.2.2.1,?_⟩
    · exact (congrArg (fun fuel=>run (machine source a k CH Cpad cutoff D G copies E K symDen thrDen km delta q code)
        fuel (input source a k D G E (List.ofFn x) bits)) he).trans af.1
    · simpa only [passed,Bool.eq_false_iff.mpr live,Bool.false_and] using af.2.2.2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
