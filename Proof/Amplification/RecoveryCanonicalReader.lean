import Proof.Amplification.RecoveryCanonicalView

/-! Execute the existing raw grammar reader on its actual canonical cold
bank. The output cursor is the real start of the two table counts. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tableWords (code : Nat) (c : Certificate) :=
  packList (packRow (Serialization.width code)) c.inner++packList (packRow (Serialization.width code)) c.outer
def tablePosition (code : Nat) (c : Certificate) :=
  (valuationPrefix code c).length+(RawSyntaxCertificate.pack (Serialization.width code) c.view).length

theorem native_reader (code : Nat) (c : Certificate) (hc : Fits code c)
    (H : Fin 66→Nat) (A : Fin 66→List Bool)
    (hn : ZeroPadding.config (RecoveryColdView.nativeCaps code.bits)
      ⟨RecoveryRawViewEntry.machine.start,H,A⟩=
      RecoveryRawViewEnd.cfg (view code.bits (TableFirst.pack (Serialization.width code) c)
        (2*(valuationPrefix code c).length)) 0 RecoveryRawViewEntry.machine.start) :
    ∃ r,runFrom RecoveryRawViewEntry.machine
      (RecoveryRawViewEntry.budget (view code.bits (TableFirst.pack (Serialization.width code) c)
        (2*(valuationPrefix code c).length)))
      ⟨RecoveryRawViewEntry.machine.start,H,A⟩=some r ∧
      r.final.heads 28=0 ∧ r.final.tapes 28=[true] ∧
      r.final.heads 29=2*tablePosition code c ∧
      r.final.tapes 29=frame (TableFirst.pack (Serialization.width code) c) := by
  let word := TableFirst.pack (Serialization.width code) c
  let x := view code.bits word (2*(valuationPrefix code c).length)
  have hw : x.width=Serialization.width code := (view_width _ _ _).trans (width_code code)
  have hword : word=valuationPrefix code c++(RawSyntaxCertificate.pack x.width c.view++tableWords code c) := by
    rw [hw]
    exact word_eq code c
  have hcode : RawSyntaxCertificate.check (RecoveryRawViewBody.code x) c.view=true := by
    rw [raw_code]
    exact hc.1
  obtain ⟨hlen,hcounts⟩ := raw_counts code c hc
  obtain ⟨base,hbase,_,hh,ht,hpos,hsource⟩ := RecoveryRawViewEntry.canonical_run_position
    x word (valuationPrefix code c) (tableWords code c) c.view (view_valid _ _ _) rfl rfl
    hword hcode hlen hcounts
  rw [←hn] at hbase
  obtain ⟨r,hr,hfinal,_,_⟩ := ZeroPadding.run_unpad RecoveryRawViewEntry.machine
    (RecoveryColdView.nativeCaps code.bits) (RecoveryRawViewEntry.budget x)
    ⟨RecoveryRawViewEntry.machine.start,H,A⟩ base hbase
  have heh (i : Fin 66) : r.final.heads i=base.final.heads i :=
    congrArg (fun cfg=>cfg.heads i) hfinal
  have het (i : Fin 66) (hi : RecoveryColdView.nativeCaps code.bits i=0) :
      r.final.tapes i=base.final.tapes i := by
    have h := congrArg (fun cfg=>cfg.tapes i) hfinal
    simpa only [ZeroPadding.config,hi,ZeroPadding.pad_zero] using h
  refine ⟨r,hr,(heh 28).trans hh,(het 28 rfl).trans ht,?_,(het 29 rfl).trans hsource⟩
  rw [heh 29,hpos,hw]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
