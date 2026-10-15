import Proof.CaseAnalysis.RecoveryCountPacketBank

/-! The paid original grammar-to-row packet transition in the shared bank.
The same raw candidate advances once and all projector/driver tapes survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketBank
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedCountBank
open RecoveryBoundedRowPacketAppend (values)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine packetSlots RecoveryBoundedCountRowEntry.machine

theorem run (q bound C D L count Q clauses B P node total : ℕ) (current : Fin 78→List Bool)
    (out stack oldPacket source : List Bool) (proj : Fin 37→List Bool) (extra : Fin 12→List Bool)
    (bd cd : List Bool) (bp cp : ℕ)
    (hcount : extra 1=RecoveryBoundedGrammarScalarAdd.unary B count)
    (hQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary B Q)
    (hclauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary B clauses)
    (hR : extra 5=RecoveryBoundedGrammarScalarAdd.unary B (q+1))
    (hb : ∀ j,2*values C (OuterPCPRecovery.boundedCircuitFieldLimit q bound) q count Q clauses j+4≤B)
    (hn : 2*(count+1)+4≤B) (hfit : 6+OuterPCPRecovery.boundedCircuitFieldLimit q bound≤C)
    (hp : oldPacket.length≤B) (hc : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D (OuterPCPRecovery.boundedCircuitFieldLimit q bound) L q (count+1) Q clauses j).length≤B)
    (hpacket : (RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields C D (OuterPCPRecovery.boundedCircuitFieldLimit q bound) L q (count+1) Q clauses)).length≤B) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit q bound
    let fuel:=RecoveryBoundedCountRowEntry.budget C D F L q count Q clauses B
    let nextFields:=RecoveryBoundedRowPrototype.fields C D F L q (count+1) Q clauses
    let nextPacket:=RecoveryBoundedCountPacketCanonical.packet C D F L q (count+1) Q clauses B
    ∃ r,runFrom machine fuel
      ⟨machine.start,heads out stack bp cp,
        data B P (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) proj total
          (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra) bd cd⟩=some r ∧
      r.steps≤fuel ∧ r.final.heads=heads out stack bp cp ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready nextFields node B out stack nextPacket source) proj total
        (RecoveryBoundedGrammarCold.metadata q bound 0 C B (nextExtra B count extra)) bd cd := by
  dsimp only
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit q bound
  let A:=data B P (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) proj total
    (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra) bd cd
  let H:=heads out stack bp cp
  let nextFields:=RecoveryBoundedRowPrototype.fields C D F L q (count+1) Q clauses
  let nextPacket:=RecoveryBoundedCountPacketCanonical.packet C D F L q (count+1) Q clauses B
  have ph:=projection_heads out stack bp cp
  have pt:=projection q bound C count Q clauses B P node total current out stack oldPacket source proj extra bd cd
    hcount hQ hclauses hR
  obtain ⟨p,pr,ps,pheads,ptapes⟩:=RecoveryBoundedCountPacketCanonical.padded_run C D F L q count Q clauses B P node
    current out stack oldPacket source hb hn hfit hp hc hf hpacket
  obtain ⟨r,rr,rf,rs⟩:=RecoveryFocus.run_config packetSlots packet_injective RecoveryBoundedCountRowEntry.machine H A _ _ p pr
  have start : RecoveryFocus.config packetSlots H A
      ⟨RecoveryBoundedCountRowEntry.machine.start,RecoveryBoundedCountPacketCanonical.heads out stack,
        RecoveryBoundedCountPacketCanonical.padded B P
          (RecoveryBoundedGrammarBank.ready current node B out stack oldPacket source) (values C F q count Q clauses)⟩=
      (⟨machine.start,H,A⟩ : Configuration 152 _) := by
    apply WilliamsSourceCrop.focus_same packetSlots ⟨machine.start,H,A⟩ _
    · intro j;exact congrFun ph j
    · intro j;exact congrFun pt j
  rw [start] at rr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    cases hpick : RecoveryFocus.pick packetSlots i with
    | none => simp only [rf,RecoveryFocus.config,hpick,H]
    | some j =>
      have he:=RecoveryFocus.slot_of_pick packetSlots hpick
      simpa only [rf,RecoveryFocus.config,hpick,pheads] using
        (congrFun ph j).symm.trans (congrArg H he)
  · rw [rf]
    change install packetSlots A p.final.tapes=_
    rw [ptapes,metadata_next]
    apply install_bank
    intro j
    have nextProjection:=projection q bound C (count+1) Q clauses B P node total nextFields
      out stack nextPacket source proj (nextExtra B count extra) bd cd rfl
      (by simpa only [nextExtra,Function.update_of_ne (by decide : (3 : Fin 12)≠1)] using hQ)
      (by simpa only [nextExtra,Function.update_of_ne (by decide : (4 : Fin 12)≠1)] using hclauses)
      (by simpa only [nextExtra,Function.update_of_ne (by decide : (5 : Fin 12)≠1)] using hR)
    rw [metadata_next] at nextProjection
    exact congrFun nextProjection j

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketBank
