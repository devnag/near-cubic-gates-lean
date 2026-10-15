import Proof.Amplification.RecoveryRawViewCanonical

/-! The physical raw-view answer and retained tag/index cells carry one
exact syntax certificate. This is the boundary used by default/raw/marker
dispatch; no witness scalar-value comparison is assumed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding RepairSource.RecoveryOracle RecoveryRawViewLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem certified_run (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ r,runFrom machine (budget width total) (RecoveryRawViewEnd.cfg x.data total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧ r.final.tapes 28=[answer word total x] ∧
      (answer word total x=true → ∃ view : RawSyntaxCertificate.View,
        RawSyntaxCertificate.check (RecoveryRawViewBody.code x.data) view=true ∧
        r.final.heads 33=0 ∧ r.final.tapes 33=[x.data.inner.tags && RawSyntaxCertificate.tagsValid view] ∧
        r.final.heads 34=0 ∧ r.final.tapes 34=
          [x.data.inner.bounded && boundedView (RadixSemantics.value x.data.inner.bound) view]) := by
  have hrun := view_run width total word x hx
  obtain ⟨r,hr,hb,hh,ht,hf⟩ := hrun
  refine ⟨r,hr,hb,hh,ht,?_⟩
  intro ha
  obtain ⟨view,hcode,htags,hbounded⟩ := accepted_syntax width total word x hx ha
  refine ⟨view,hcode,?_,?_,?_,?_⟩
  · rw [hf ha]; rfl
  · rw [hf ha]
    change [(out word total x).2.data.inner.tags]=_
    exact congrArg (fun bit : Bool=>[bit]) htags
  · rw [hf ha]; rfl
  · rw [hf ha]
    change [(out word total x).2.data.inner.bounded]=_
    exact congrArg (fun bit : Bool=>[bit]) hbounded

end NearCubicWires.RepairOrdinary.RecoveryRawViewWhole
