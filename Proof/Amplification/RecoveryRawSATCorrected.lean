import Proof.Amplification.RecoveryRawSATMeaning

/-! The raw branch combines the actual syntax/index guards with the
executed shared-valuation replay. These guards imply the original raw
well-sized test; they are not new source assumptions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATTable
open RecoveryRawSAT
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem project_bounded (bound : Nat) (view : RawSyntaxCertificate.View)
    (hb : RecoveryRawViewLoop.boundedView bound view=true) :
    (RawSyntaxCertificate.project view).all (fun clause=>clause.all (fun literal=>literal.2<bound))=true := by
  simp only [RawSyntaxCertificate.project,RawSyntaxCertificate.projectClause,List.all_map,
    Function.comp_def,RawSyntaxCertificate.projectLiteral]
  change view.all (fun clause=>clause.all (fun literal=>decide (literal.2<bound)))=true
  exact hb

theorem guarded_wellSized (code : Nat) (view : RawSyntaxCertificate.View)
    (hc : RawSyntaxCertificate.check code view=true) (ht : RawSyntaxCertificate.tagsValid view=true)
    (hb : RecoveryRawViewLoop.boundedView (natBitLength code) view=true)
    (hthree : (decodeCNF code).all (fun clause=>clause.length=3)=true) :
    wellSizedCNFEncoding code (decodeCNF code)=true := by
  have hd : decodeCNF code=RawSyntaxCertificate.project view := by
    rw [RawSyntaxCertificate.certified_default code view hc,ht]
    rfl
  have hlen : (decodeCNF code).length ≤ natBitLength code := by
    rw [hd]
    simpa only [RawSyntaxCertificate.project,List.length_map] using (RawSyntaxCertificate.view_bounds code view hc).1
  have hindices := project_bounded (natBitLength code) view hb
  rw [←hd] at hindices
  simp only [wellSizedCNFEncoding,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hlen,?_⟩
  rw [List.all_eq_true] at hthree hindices ⊢
  intro clause hm
  rw [Bool.and_eq_true]
  exact ⟨hthree clause hm,hindices clause hm⟩

theorem guarded_answer_sound (width cap total code : Nat) (word : List Bool)
    (view : RawSyntaxCertificate.View)
    (hc : RawSyntaxCertificate.check code view=true) (ht : RawSyntaxCertificate.tagsValid view=true)
    (hb : RecoveryRawViewLoop.boundedView (natBitLength code) view=true)
    (ha : answer width cap 0 0 total word code=true) : correctedSat code=true := by
  have hm := accepted_meaning width cap 0 0 total word code ha
  have hw := guarded_wellSized code view hc ht hb hm.1
  rw [correctedSat,if_pos hw,legacySat_wellSized_iff code hw]
  exact ⟨hm.2.choose,hm.2.choose_spec.2⟩

end NearCubicWires.RepairOrdinary.RecoveryRawSATTable
