import Proof.Amplification.RecoveryCanonicalProduced

/-! The canonical cold-front success executes the existing marker bank.
The physical row/count tapes survive that complete338-tape run. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def markerTableSlots (i : Fin 4) : Fin 338 := (frontTableSlots i).castAdd 59

theorem marker_run (code : Nat) (c : Certificate) (hc : Fits code c) :
    ∃ r,run RecoveryColdMarker.coldProgram
      (RecoveryColdMarker.coldBudget code.bits (TableFirst.pack (Serialization.width code) c))
      (RecoveryColdMarker.input code.bits (TableFirst.pack (Serialization.width code) c))=some r ∧
      r.final.heads 277=0 ∧ r.final.tapes 277=[true] ∧
      RecoveryColdMarker.Ready code.bits (TableFirst.pack (Serialization.width code) c)
        r.final.heads r.final.tapes ∧ TableTapes markerTableSlots code c r.final.tapes := by
  let word := TableFirst.pack (Serialization.width code) c
  obtain ⟨canonical,hcanonical,hch,hct,hready,g,b,_,hproduced⟩ := front_run code c hc
  obtain ⟨bit,base,hbase,first,hfirst,hfh,hft,hh,ht,_⟩ := RecoveryColdMarker.prefix_run code.bits word
  have he : canonical=base := Option.some.inj (hcanonical.symm.trans hbase)
  subst base
  have htrue : first.final.tapes 277=[true] := by
    rw [hft]
    exact hct
  obtain ⟨last,hlast,hlh,hlt,_⟩ := RecoveryColdMarker.bank_run code.bits canonical.final.heads canonical.final.tapes
    (RecoveryColdMarker.sources code.bits word canonical.final.heads canonical.final.tapes hready)
  rw [←hfh,←hft] at hlast
  obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept RecoveryColdMarker.prefixProgram RecoveryColdMarker.bankProgram 277
    (RecoveryColdFront.budget code.bits word) (RecoveryColdMarker.bankBudget code.bits)
    _ first last hfirst hh htrue hlast
  refine ⟨r,hr,?_,?_,?_,?_⟩
  · rw [hrh,hlh]
    exact hch
  · rw [hrt,hlt]
    change RecoveryColdMarker.stage6 code.bits canonical.final.tapes ((277 : Fin 279).castAdd 59)=[true]
    rw [RecoveryColdMarker.retained]
    exact hct
  · exact ⟨canonical.final.heads,canonical.final.tapes,hready,hrh.trans hlh,hrt.trans hlt⟩
  · have htable := produced_tables code c hc g b canonical.final.heads canonical.final.tapes hproduced
    rw [hrt,hlt]
    simpa only [TableTapes,markerTableSlots,RecoveryColdMarker.retained] using htable

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
