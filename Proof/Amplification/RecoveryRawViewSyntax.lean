import Proof.Amplification.RecoveryRawViewWhole

/-! Every accepted raw-view run supplies an exact natural-tag syntax
certificate and the two flags accumulated from that same certificate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle
open RecoveryRawViewBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundedView (bound : Nat) (view : RawSyntaxCertificate.View) : Bool :=
  view.all (fun clause=>clause.all (fun literal=>decide (literal.2 < bound)))

theorem out_syntax (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x)
    (ha : (out word total x).1=true) (hz : code (out word total x).2.data=0) :
    ∃ view : RawSyntaxCertificate.View,Encodable.encode view=code x.data ∧
      (out word total x).2.data.inner.tags=(x.data.inner.tags && RawSyntaxCertificate.tagsValid view) ∧
      (out word total x).2.data.inner.bounded=
        (x.data.inner.bounded && boundedView (RadixSemantics.value x.data.inner.bound) view) := by
  induction total generalizing x with
  | zero=>
    refine ⟨[],?_,?_,?_⟩
    · exact hz.symm
    · change x.data.inner.tags=(x.data.inner.tags && true)
      exact (Bool.and_true _).symm
    · change x.data.inner.bounded=(x.data.inner.bounded && true)
      exact (Bool.and_true _).symm
  | succ total ih=>
    have hn : (next word x).1=true := by
      by_cases hn : (next word x).1=true
      · exact hn
      · simp only [out,RepeatMachine.iterate,if_neg hn] at ha
        exact ha
    have hs := accepted x.data word x.pos hn
    obtain ⟨hcode,n,rest,hparse,hcheck⟩ := hs
    have hshape : (RawShape.clause n (headCode x.data)).isSome=true := by
      rw [←prepared_answer x.data n hcode]
      exact hcheck
    obtain ⟨head,hhead⟩ : ∃ head,RawShape.clause n (headCode x.data)=some head := by
      cases hh : RawShape.clause n (headCode x.data) with
      | none=>simp only [hh,Option.isSome_none,Bool.false_eq_true] at hshape
      | some head=>exact ⟨head,rfl⟩
    have hy : (next word x).2.data=output x.data n := body_output_some x.data word x.pos n rest hparse
    have hflags := output_flags x.data n head hcode hhead
    have hbound := (output_stable x.data n).1
    rw [out_succ word total x hn] at ha hz ⊢
    obtain ⟨tail,htail,htags,hbounded⟩ := ih (next word x).2 (next_inv width word x hx hn) ha hz
    have htailCode : Encodable.encode tail=(Nat.unpair (code x.data-1)).2 := by
      rw [hy,output_tail x.data n hcode] at htail
      exact htail
    refine ⟨head::tail,?_,?_,?_⟩
    · rw [Encodable.encode_list_cons,RawShape.clause_sound n (headCode x.data) head hhead,htailCode]
      change Nat.pair (Nat.unpair (code x.data-1)).1 (Nat.unpair (code x.data-1)).2+1=code x.data
      rw [Nat.pair_unpair]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hcode)
    · rw [hy,hflags.1] at htags
      simpa only [RawSyntaxCertificate.tagsValid,List.all_cons,Bool.and_assoc] using htags
    · rw [hy,hflags.2,hbound] at hbounded
      simpa only [boundedView,List.all_cons,Bool.and_assoc] using hbounded

theorem accepted_syntax (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x)
    (ha : RecoveryRawViewWhole.answer word total x=true) :
    ∃ view : RawSyntaxCertificate.View,RawSyntaxCertificate.check (code x.data) view=true ∧
      (out word total x).2.data.inner.tags=(x.data.inner.tags && RawSyntaxCertificate.tagsValid view) ∧
      (out word total x).2.data.inner.bounded=
        (x.data.inner.bounded && boundedView (RadixSemantics.value x.data.inner.bound) view) := by
  rw [RecoveryRawViewWhole.answer,Bool.and_eq_true,decide_eq_true_eq] at ha
  obtain ⟨view,hcode,htags,hbounded⟩ := out_syntax width total word x hx ha.1 ha.2
  exact ⟨view,(RawSyntaxCertificate.check_iff _ _).mpr hcode,htags,hbounded⟩

end NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
