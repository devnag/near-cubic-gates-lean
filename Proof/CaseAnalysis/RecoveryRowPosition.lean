import Proof.CaseAnalysis.RecoveryRowAddressMeaning

/-! A single paid positioning step starts the original row from a bank
whose only nonzero cursor is the retained graph append cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
open LocalBitMultitape RecoveryExecution Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) (i : Fin 73):=if i=20 then out.length else 0
def driver (i : Fin 73):=decide (RecoveryBoundedRow.heads [] [] [] i=1)
def position : Machine 73 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun i=>if driver i then .right else .stay⟩ else none

theorem position_step (out : List Bool) (A : Fin 73→List Bool) :
    step position ⟨0,heads out,A⟩=some ⟨1,RecoveryBoundedRow.heads out [] [],A⟩ := by
  change some (applyAction (⟨0,heads out,A⟩ : Configuration 73 2)
    ⟨1,fun _=>none,fun i=>if driver i then .right else .stay⟩)=_
  congr 1
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem position_run (out : List Bool) (A : Fin 73→List Bool) :
    ∃ r,runFrom position 1 ⟨position.start,heads out,A⟩=some r ∧ r.steps=1 ∧
      r.final.heads=RecoveryBoundedRow.heads out [] [] ∧ r.final.tapes=A := by
  obtain ⟨r,rr,rf,rs⟩:=(Timed.single (by rfl) (position_step out A)).run (by rfl)
  exact ⟨r,rr,rs,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

noncomputable def prepare:=RecoveryBoundedRow.Calls.machine position RecoveryBoundedRow.machine

theorem enter (out : List Bool) (A : Fin 73→List Bool) (u : ℕ)
    (r : ExecutionReceipt 73 _)
    (hr : runFrom RecoveryBoundedRow.machine u ⟨RecoveryBoundedRow.machine.start,RecoveryBoundedRow.heads out [] [],A⟩=some r)
    (hs : r.steps ≤ u) :
    ∃ q,runFrom prepare (u+2) ⟨prepare.start,heads out,A⟩=some q ∧
      q.steps ≤ u+2 ∧ q.final.heads=r.final.heads ∧ q.final.tapes=r.final.tapes := by
  obtain ⟨p,pr,ps,ph,pt⟩:=position_run out A
  have hr' : runFrom RecoveryBoundedRow.machine u (restart p.final RecoveryBoundedRow.machine.start)=some r := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some r
    rw [ph,pt]
    exact hr
  obtain ⟨q,qr,qs,qh,qt⟩:=RecoveryBoundedRow.Calls.join position RecoveryBoundedRow.machine
    (heads out) A 1 u p r pr hr'
  have hb : 1+1+u=u+2:=by omega
  rw [hb] at qr
  refine ⟨q,qr,?_,qh,qt⟩
  rw [qs,ps]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowReuse
