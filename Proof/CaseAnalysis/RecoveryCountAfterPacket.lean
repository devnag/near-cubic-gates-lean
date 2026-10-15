import Proof.CaseAnalysis.RecoveryCountDriverDock

/-! The complete paid grammar-to-row scalar/packet transition. Existing
Room and Allocation discharge all temporary margins of both original workers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline
open LocalBitMultitape Composition
open RecoveryBoundedCountBank
open RecoveryBoundedGrammarCold (Room Allocation selectedFields selectedWord foldRows metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Join
variable {s t : ℕ}
def machine (first : Machine 152 s) (last : Machine 152 t):=Composition.machine first last
theorem run (first : Machine 152 s) (last : Machine 152 t) (u v : ℕ)
    (H : Fin 152→ℕ) (A : Fin 152→List Bool) (p : ExecutionReceipt 152 s) (q : ExecutionReceipt 152 t)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom last v (restart p.final last.start)=some q) :
    ∃ r,runFrom (machine first last) (u+1+v) ⟨(machine first last).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes :=
  ⟨joinedReceipt p q,Composition.run_join first last _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Join

noncomputable def afterPacket:=Join.machine RecoveryBoundedCountScalarDock.machine RecoveryBoundedCountPacketBank.machine
def afterPacketBudget (C D F L R count Q clauses B : ℕ):=
  RecoveryBoundedCountScalarReset.budget B+1+RecoveryBoundedCountRowEntry.budget C D F L R count Q clauses B

theorem afterPacket_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W) (count : Fin bound)
    (Q clauses node total : ℕ) (out stack source : List Bool) (proj : Fin 37→List Bool)
    (extra : Fin 12→List Bool) (bd cd : List Bool)
    (hQ : Q≤W) (hclauses : clauses≤W)
    (rawCount : extra 1=RecoveryBoundedGrammarScalarAdd.unary B count.val)
    (rawQ : extra 3=RecoveryBoundedGrammarScalarAdd.unary B Q)
    (rawClauses : extra 4=RecoveryBoundedGrammarScalarAdd.unary B clauses)
    (rawR : extra 5=RecoveryBoundedGrammarScalarAdd.unary B (q+1))
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D (OuterPCPRecovery.boundedCircuitFieldLimit q bound) L q (count.val+1) Q clauses j).length≤B)
    (hp : (RecoveryBoundedRowReload.word
      (RecoveryBoundedRowPrototype.fields C D (OuterPCPRecovery.boundedCircuitFieldLimit q bound) L q (count.val+1) Q clauses)).length≤B) :
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit q bound
    let nextFields:=RecoveryBoundedRowPrototype.fields C D F L q (count.val+1) Q clauses
    let nextPacket:=RecoveryBoundedCountPacketCanonical.packet C D F L q (count.val+1) Q clauses B
    ∃ r,runFrom afterPacket (afterPacketBudget C D F L q count.val Q clauses B)
      ⟨afterPacket.start,heads out stack 1 1,
        data B P (RecoveryBoundedGrammarBank.ready (selectedFields foldRows q bound (bound+1) C)
          node B out stack (ZeroPadding.pad B (selectedWord foldRows q bound (bound+1) C)) source)
          proj total (metadata q bound (bound+1) C B extra) bd cd⟩=some r ∧
      r.steps≤afterPacketBudget C D F L q count.val Q clauses B ∧ r.final.heads=heads out stack 1 1 ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready nextFields node B out stack nextPacket source)
        proj total (metadata q bound 0 C B (RecoveryBoundedCountPacketBank.nextExtra B count.val extra)) bd cd := by
  dsimp only
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit q bound
  let fields:=selectedFields foldRows q bound (bound+1) C
  let packet:=ZeroPadding.pad B (selectedWord foldRows q bound (bound+1) C)
  have scalars:=(alloc.next_scalars (⟨bound,by omega⟩ : Fin (bound+1))).2.2
  have margins:=RecoveryBoundedCounts.reset_inputs room alloc
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedCountScalarDock.run q bound (bound+1) C B P node total extra
    fields out stack packet source proj bd cd 1 1 margins.1 margins.2.1 margins.2.2
  have inputs:=RecoveryBoundedCounts.packet_inputs room alloc count Q clauses hQ hclauses
  obtain ⟨b,br,bs,bh,bt⟩:=RecoveryBoundedCountPacketBank.run q bound C D L count.val Q clauses B P node total fields
    out stack packet source proj extra bd cd 1 1 rawCount rawQ rawClauses rawR inputs.1 inputs.2.1 inputs.2.2
    (room.pad_packet_length scalars foldRows) (room.packet_fits scalars foldRows).2.2.2.2.2.2 hf hp
  have br' : runFrom RecoveryBoundedCountPacketBank.machine
      (RecoveryBoundedCountRowEntry.budget C D F L q count.val Q clauses B)
      (restart a.final RecoveryBoundedCountPacketBank.machine.start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  obtain ⟨r,rr,rs,rh,rt⟩:=Join.run RecoveryBoundedCountScalarDock.machine RecoveryBoundedCountPacketBank.machine
    _ _ _ _ a b ar br'
  refine ⟨r,rr,?_,rh.trans bh,rt.trans bt⟩
  rw [rs]
  exact Nat.add_le_add (Nat.add_le_add_right as 1) bs

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPipeline
