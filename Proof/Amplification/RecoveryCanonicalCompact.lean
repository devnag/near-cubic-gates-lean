import Proof.Amplification.RecoveryCanonicalValues

/-! Positive execution of the whole493-tape cold materializer on the
canonical witness, retaining its exact broadcast endpoint. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def CompactReady (code : Nat) (c : Certificate) (H : Fin 493→Nat) (A : Fin 493→List Bool) : Prop :=
  ∃ (h : Fin 338→Nat) (a : Fin 338→List Bool),
    RecoveryColdMarker.Ready code.bits (TableFirst.pack (Serialization.width code) c) h a ∧
    (fun j=>a (RecoveryColdCompact.sourceSlots j))=
      RecoveryColdCompact.sourceTapes code.bits (TableFirst.pack (Serialization.width code) c)
        (innerBits code c) (outerBits code c) c.inner.length c.outer.length ∧
    H=RecoveryColdCompact.finishHeads (RecoveryColdCompact.bankHeads h) ∧
    A=RecoveryColdCompact.finishTapes (RecoveryColdCompact.stage34 code.bits
      (TableFirst.pack (Serialization.width code) c) (innerBits code c) (outerBits code c)
      c.inner.length c.outer.length (RecoveryColdCompact.bankInput a))

theorem compact_run (code : Nat) (c : Certificate) (hc : Fits code c) :
    ∃ r,run RecoveryColdCompact.coldProgram
      (RecoveryColdCompact.coldBudget code.bits (TableFirst.pack (Serialization.width code) c))
      (RecoveryColdCompact.input code.bits (TableFirst.pack (Serialization.width code) c))=some r ∧
      r.final.heads 277=0 ∧ r.final.tapes 277=[true] ∧ CompactReady code c r.final.heads r.final.tapes := by
  let word := TableFirst.pack (Serialization.width code) c
  obtain ⟨canonical,hcanonical,hch,hct,hready,htables⟩ := marker_run code c hc
  obtain ⟨bit,base,hbase,first,hfirst,hfh,hft,hh,_,_⟩ := RecoveryColdCompact.prefix_run code.bits word
  have he : canonical=base := Option.some.inj (hcanonical.symm.trans hbase)
  subst base
  have htrue : first.final.tapes 277=[true] := by rw [hft]; exact hct
  obtain ⟨n,ib,m,ob,hn,hm,hsource,last,hlast,hlh,hlt,_⟩ :=
    RecoveryColdCompact.materialize_exact code.bits word canonical.final.heads canonical.final.tapes hready
  obtain ⟨hnc,hib,hmc,hob⟩ := source_values code c canonical.final.tapes n m ib ob htables hsource
  subst n
  subst ib
  subst m
  subst ob
  have hbound : RecoveryColdCompact.materializeBudget code.bits word c.inner.length c.outer.length ≤
      RecoveryColdCompact.materializeBudget code.bits word (RecoveryColdView.limit code.bits)
        (RecoveryColdView.limit code.bits) := by
    unfold RecoveryColdCompact.materializeBudget RecoveryColdCompact.bankBudget
    omega
  have hmore := runFrom_moreFuel RecoveryColdCompact.materializeProgram
    (RecoveryColdCompact.materializeBudget code.bits word c.inner.length c.outer.length)
    (RecoveryColdCompact.materializeBudget code.bits word (RecoveryColdView.limit code.bits)
      (RecoveryColdView.limit code.bits)-
      RecoveryColdCompact.materializeBudget code.bits word c.inner.length c.outer.length) _ last hlast
  rw [Nat.add_sub_of_le hbound,←hfh,←hft] at hmore
  obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept RecoveryColdCompact.prefixProgram RecoveryColdCompact.materializeProgram 277
    (RecoveryColdMarker.coldBudget code.bits word)
    (RecoveryColdCompact.materializeBudget code.bits word (RecoveryColdView.limit code.bits)
      (RecoveryColdView.limit code.bits)) _ first last hfirst hh htrue hmore
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [hrh,hlh]
    exact hch
  · rw [hrt,hlt]
    change RecoveryColdCompact.finishTapes (RecoveryColdCompact.stage34 code.bits word
      (innerBits code c) (outerBits code c) c.inner.length c.outer.length
      (RecoveryColdCompact.bankInput canonical.final.tapes)) ((277 : Fin 336).castAdd 157)=[true]
    rw [RecoveryColdCompact.retained]
    exact hct
  · exact ⟨canonical.final.heads,canonical.final.tapes,hready,hsource,hrh.trans hlh,hrt.trans hlt⟩

theorem compact_ready (code : Nat) (c : Certificate) (hc : Fits code c)
    (H : Fin 493→Nat) (A : Fin 493→List Bool) (h : CompactReady code c H A) :
    RecoveryColdCompact.Ready code.bits (TableFirst.pack (Serialization.width code) c) H A := by
  obtain ⟨g,b,hm,hs,hh,ht⟩ := h
  refine ⟨g,b,c.inner.length,innerBits code c,c.outer.length,outerBits code c,hm,?_,?_,hs,hh,ht⟩
  · rw [limit_code]
    exact hc.2.2.2.1.trans (TableFirst.counts_fit code).2.1
  · rw [limit_code]
    exact hc.2.2.2.2.1.trans (TableFirst.counts_fit code).2.2

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
