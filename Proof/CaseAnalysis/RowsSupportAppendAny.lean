import Proof.CaseAnalysis.RowsSupportAppendBank

/-! The ambient-bank adapter also exposes an arbitrary actual return, so
rejected returns need no invented normal form for their private fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lift_eta {t : ℕ} {α : Type} (values : Fin (t+1)→α) :
    lift (fun i=>values (i.castAdd 1)) (values ((0 : Fin 1).natAdd t))=values:=by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j;simp only [lift,Fin.addCases_left]
  · intro j
    have h:j=(0 : Fin 1):=Subsingleton.elim _ _
    subst j
    simp only [lift,Fin.addCases_right]

def push {t e : ℕ} {α : Type} (values : Fin (t+1)→α) (extra : Fin e→α) : Fin (t+e+1)→α:=
  fields (fun i=>values (i.castAdd 1)) extra (values ((0 : Fin 1).natAdd t))

theorem push_lift {t e : ℕ} {α : Type} (values : Fin t→α) (extra : Fin e→α) (last : α) :
    push (lift values last) extra=fields values extra last:=by
  simp only [push,lift,Fin.addCases_left,Fin.addCases_right]

theorem run_any {t e s : ℕ} (p : Machine (t+1) s) (fuel : ℕ)
    (source : Configuration (t+1) s) (eh : Fin e→ℕ) (ed : Fin e→List Bool)
    (base : ExecutionReceipt (t+1) s) (hr : runFrom p fuel source=some base) :
    ∃ r,runFrom (machine (e:=e) p) fuel
      ⟨source.control,push source.heads eh,push source.tapes ed⟩=some r ∧
      r.steps=base.steps ∧ r.final.heads=push base.final.heads eh ∧ r.final.tapes=push base.final.tapes ed:=by
  have h:runFrom p fuel ⟨source.control,
      lift (fun i=>source.heads (i.castAdd 1)) (source.heads ((0 : Fin 1).natAdd t)),
      lift (fun i=>source.tapes (i.castAdd 1)) (source.tapes ((0 : Fin 1).natAdd t))⟩=some base:=by
    rw [lift_eta,lift_eta]
    exact hr
  exact run p fuel source.control _ _ _ _ eh ed _ _ _ _ base h
    (lift_eta base.final.heads).symm (lift_eta base.final.tapes).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
