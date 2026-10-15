import Proof.CaseAnalysis.RecoveryLiteralBank

/-! Opaque receipt boundaries for the literal's existing lookup/sign/node
controller. Both branches retain the complete enclosing physical bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b : ℕ} (firstProgram : Machine 61 a) (lastProgram : Machine 61 b)
noncomputable def sizes : Fin 2→ℕ:=![a,b]
noncomputable def programs : (j : Fin 2)→Machine 61 (sizes (a:=a) (b:=b) j)
  | ⟨0,_⟩=>firstProgram
  | ⟨1,_⟩=>lastProgram
  | ⟨j+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes (a:=a) (b:=b) j)) (bits : Fin 61→Bool) : Option (Fin 2):=
  if j.val=0 then if bits 48 then some 1 else none else none
noncomputable def machine:=RecoveryCalls.machine (sizes (a:=a) (b:=b))
  (programs firstProgram lastProgram) 0 (next (a:=a) (b:=b))

theorem positive_receipt (H : Fin 61→ℕ) (A : Fin 61→List Bool) (fuel : ℕ)
    (p : ExecutionReceipt 61 a)
    (pr : runFrom firstProgram fuel ⟨firstProgram.start,H,A⟩=some p)
    (hflag : readTapeBit (p.final.tapes 48) (p.final.heads 48)=false) :
    ∃ r,runFrom (machine firstProgram lastProgram) (fuel+1) ⟨(machine firstProgram lastProgram).start,H,A⟩=some r ∧
      r.steps ≤ fuel+1 ∧ r.final.heads=p.final.heads ∧ r.final.tapes=p.final.tapes := by
  have hn : next (a:=a) (b:=b) 0 p.final.control p.final.scanned=none := by
    change (if readTapeBit (p.final.tapes 48) (p.final.heads 48) then some (1 : Fin 2) else none)=none
    rw [hflag]
    rfl
  obtain ⟨k,hk,ht⟩:=stop_receipt (sizes (a:=a) (b:=b)) (programs firstProgram lastProgram) 0 (next (a:=a) (b:=b)) 0 fuel _ p pr hn
  obtain ⟨r,rr,rf,rs⟩:=ht.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  change runFrom (machine firstProgram lastProgram) k ⟨(machine firstProgram lastProgram).start,H,A⟩=some r at rr
  have more:=runFrom_moreFuel (machine firstProgram lastProgram) k (fuel+1-k) _ r rr
  rw [Nat.add_sub_of_le hk] at more
  refine ⟨r,more,rs.le.trans hk,?_,?_⟩ <;> rw [rf] <;> rfl

theorem negative_receipt (H : Fin 61→ℕ) (A : Fin 61→List Bool) (first last : ℕ)
    (p : ExecutionReceipt 61 a) (q : ExecutionReceipt 61 b)
    (pr : runFrom firstProgram first ⟨firstProgram.start,H,A⟩=some p)
    (qr : runFrom lastProgram last
      (RecoveryCalls.restarted lastProgram p.final.heads p.final.tapes)=some q)
    (hflag : readTapeBit (p.final.tapes 48) (p.final.heads 48)=true) :
    ∃ r,runFrom (machine firstProgram lastProgram) (first+last+2) ⟨(machine firstProgram lastProgram).start,H,A⟩=some r ∧
      r.steps ≤ first+last+2 ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  have hn : next (a:=a) (b:=b) 0 p.final.control p.final.scanned=some 1 := by
    change (if readTapeBit (p.final.tapes 48) (p.final.heads 48) then some (1 : Fin 2) else none)=some 1
    rw [hflag]
    rfl
  obtain ⟨k,hk,ht⟩:=call_receipt (sizes (a:=a) (b:=b)) (programs firstProgram lastProgram) 0 (next (a:=a) (b:=b)) 0 1 first _ p pr hn
  obtain ⟨l,hl,hu⟩:=stop_receipt (sizes (a:=a) (b:=b)) (programs firstProgram lastProgram) 0 (next (a:=a) (b:=b)) 1 last _ q qr (by rfl)
  obtain ⟨r,rr,rf,rs⟩:=(ht.trans hu).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  change runFrom (machine firstProgram lastProgram) (k+l) ⟨(machine firstProgram lastProgram).start,H,A⟩=some r at rr
  have hb : k+l ≤ first+last+2 := by omega
  have more:=runFrom_moreFuel (machine firstProgram lastProgram) (k+l) (first+last+2-(k+l)) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩ <;> rw [rf] <;> rfl

end Calls

noncomputable def machine (second : Bool):=Calls.machine (RecoveryBoundedClauseSelect.machine second)
  (RecoveryBoundedLiteralNode.machine (kind second))
def budget (second : Bool) (before : List ℕ) (ref node C : ℕ):=
  RecoveryBoundedClauseSelect.budget before ref+RecoveryBoundedLiteralNode.budget (kind second) ref 0 node C+2
end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
