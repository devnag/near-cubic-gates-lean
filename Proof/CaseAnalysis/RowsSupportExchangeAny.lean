import Proof.CaseAnalysis.RowsSupportExchange
import Proof.CaseAnalysis.RowsSupportAppendAny

/-! The existing last-label exchange applies to an arbitrary source
configuration, with its actual support cursor retained as part of that source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem exchange_any {t : ℕ} {α : Type} (values : Fin (t+1)→α) (driver : α) :
    lift values driver ∘ (layout t).symm=
      lift (lift (fun i=>values (i.castAdd 1)) driver) (values ((0 : Fin 1).natAdd t)):=by
  have h:=exchange (fun i=>values (i.castAdd 1)) (values ((0 : Fin 1).natAdd t)) driver
  rw [AppendBank.lift_eta] at h
  exact h

theorem exchange_push {t e : ℕ} {α : Type} (values : Fin (t+1)→α) (driver : α) (extra : Fin e→α) :
    AppendBank.push (lift values driver ∘ (layout t).symm) extra=
      AppendBank.fields (lift (fun i=>values (i.castAdd 1)) driver) extra (values ((0 : Fin 1).natAdd t)):=by
  rw [exchange_any,AppendBank.push_lift]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Exchange
