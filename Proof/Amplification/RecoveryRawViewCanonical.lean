import Proof.Amplification.RecoveryRawViewCanonicalStep

/-! Canonical completeness of the actual raw-view controller with its
existing flat clause payload and retained physical cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle
open RecoveryRawViewBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_out (width : Nat) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (x : Cursor) (hx : Inv width word x)
    (hword : word=pre++(view.flatMap (RawSyntaxCertificate.packClause width)++suffix))
    (hpos : x.pos=pre.length) (hcode : code x.data=Encodable.encode view)
    (hcounts : ∀ clause∈view,clause.length ≤ x.data.limit) :
    (out word view.length x).1=true ∧ code (out word view.length x).2.data=0 ∧
      (out word view.length x).2.pos=pre.length+(view.flatMap (RawSyntaxCertificate.packClause width)).length := by
  induction view generalizing pre x with
  | nil=>
    refine ⟨rfl,hcode,?_⟩
    change x.pos=pre.length+0
    omega
  | cons head tail ih=>
    have hwstep : word=pre++(RawSyntaxCertificate.packClause x.data.width head++
        (tail.flatMap (RawSyntaxCertificate.packClause width)++suffix)) := by
      rw [hx.2.1]
      simpa only [List.flatMap_cons,List.append_assoc] using hword
    have hstep := canonical_step word pre (tail.flatMap (RawSyntaxCertificate.packClause width)++suffix)
      head tail x hwstep hpos (hcounts head (by simp)) hcode
    have hv := next_inv width word x hx hstep.1
    have hstable := accepted_invariant x.data word x.pos hx.1 hstep.1
    have hlim : (next word x).2.data.limit=x.data.limit := hstable.2.2.1
    have hwrest : word=(pre++RawSyntaxCertificate.packClause width head)++
        (tail.flatMap (RawSyntaxCertificate.packClause width)++suffix) := by
      simpa only [List.flatMap_cons,List.append_assoc] using hword
    have hprest : (next word x).2.pos=(pre++RawSyntaxCertificate.packClause width head).length := by
      rw [List.length_append]
      have h := hstep.2.1
      rw [hx.2.1] at h
      exact h
    have hcrest : ∀ clause∈tail,clause.length ≤ (next word x).2.data.limit := by
      intro clause hc
      rw [hlim]
      exact hcounts clause (by simp [hc])
    have htail := ih (pre++RawSyntaxCertificate.packClause width head) (next word x).2 hv
      hwrest hprest hstep.2.2 hcrest
    rw [List.length_cons,out_succ word tail.length x hstep.1]
    refine ⟨htail.1,htail.2.1,?_⟩
    rw [htail.2.2,List.length_append,List.flatMap_cons,List.length_append]
    omega

theorem canonical_answer (width : Nat) (word pre suffix : List Bool) (view : RawSyntaxCertificate.View)
    (x : Cursor) (hx : Inv width word x)
    (hword : word=pre++(view.flatMap (RawSyntaxCertificate.packClause width)++suffix))
    (hpos : x.pos=pre.length) (hcode : code x.data=Encodable.encode view)
    (hcounts : ∀ clause∈view,clause.length ≤ x.data.limit) :
    RecoveryRawViewWhole.answer word view.length x=true := by
  have h := canonical_out width word pre suffix view x hx hword hpos hcode hcounts
  simp only [RecoveryRawViewWhole.answer,h.1,h.2.1,decide_true,Bool.and_self]

end NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
