import Proof.CaseAnalysis.RecoveryLiteralCalls

/-! Complete original literal consumer: lookup its actual query reference,
read the actual sign and append precisely one NOT only on the negative branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run (second negative : Bool) (H : Fin 61→ℕ) (A : Fin 61→List Bool)
    (before : List ℕ) (ref node W C L : ℕ) (out tail : List Bool)
    (hLookup : ∀ j,H (RecoveryBoundedClauseSelect.lookupSlots j)=0)
    (aLookup : ∀ j,A (RecoveryBoundedClauseSelect.lookupSlots j)=RecoveryBoundedClauseLookup.input before ref C L tail j)
    (hGate : ∀ j,H (RecoveryBoundedClauseGate.slots (kind second) j)=PCPPNativeClauseBank.heads out j)
    (aGate : ∀ j,A (RecoveryBoundedClauseGate.slots (kind second) j)=RecoveryBoundedUniversalGates.data 0 0 C out j)
    (hReplace : ∀ j,H (RecoveryBoundedClauseReplace.slots second j)=0)
    (aReplace : ∀ j,A (RecoveryBoundedClauseReplace.slots second j)=RecoveryBoundedClauseReplace.data node 0 C 0 j)
    (hSign : readTapeBit (A 48) (H 48)=negative)
    (hL : RecoveryBoundedClauseLookup.rawBudget before ref ≤ L)
    (href : ref ≤ W) (hC : 16384*(W+1)^2 ≤ C) (hn : node+1 ≤ C) :
    ∃ r,runFrom (machine second) (budget second before ref node C) ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ budget second before ref node C ∧ r.final.heads=heads second negative H ref out ∧
      r.final.tapes=output second negative A before ref node C out := by
  obtain ⟨p,pr,_,ph,pt⟩:=RecoveryBoundedClauseSelect.select_run second H A before ref C L tail
    hLookup (hReplace 1) aLookup (aReplace 1) hL
  have hscan : readTapeBit (p.final.tapes 48) (p.final.heads 48)=negative := by
    rw [pt,ph,selected_flag]
    exact hSign
  cases negative
  · obtain ⟨r,rr,rs,rh,rt⟩:=Calls.positive_receipt (RecoveryBoundedClauseSelect.machine second)
      (RecoveryBoundedLiteralNode.machine (kind second)) H A _ p pr hscan
    have hb : RecoveryBoundedClauseSelect.budget before ref+1 ≤ budget second before ref node C := by
      unfold budget;omega
    have more:=runFrom_moreFuel (machine second) (RecoveryBoundedClauseSelect.budget before ref+1)
      (budget second before ref node C-(RecoveryBoundedClauseSelect.budget before ref+1)) _ r rr
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨r,more,rs.trans hb,rh.trans ph,rt.trans pt⟩
  · obtain ⟨q,qr,_,qh,qt⟩:=RecoveryBoundedLiteralNode.node_run (kind second) H
      (RecoveryBoundedClauseSelect.output A second before ref C) ref 0 node W C out
      hGate (selected_gate second A before ref C out aGate)
      (by simpa only [kind_second] using hReplace)
      (by simpa only [kind_second] using selected_replace second A before ref node C aReplace)
      href (by omega) hC hn
    have qr' : runFrom (RecoveryBoundedLiteralNode.machine (kind second))
        (RecoveryBoundedLiteralNode.budget (kind second) ref 0 node C)
        (RecoveryCalls.restarted (RecoveryBoundedLiteralNode.machine (kind second)) p.final.heads p.final.tapes)=some q := by
      change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
      rw [ph,pt]
      exact qr
    obtain ⟨r,rr,rs,rh,rt⟩:=Calls.negative_receipt (RecoveryBoundedClauseSelect.machine second)
      (RecoveryBoundedLiteralNode.machine (kind second)) H A _ _ p q pr qr' hscan
    exact ⟨r,rr,rs,rh.trans qh,rt.trans qt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
