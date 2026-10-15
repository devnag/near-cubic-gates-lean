import Proof.CaseAnalysis.RowsTouchingDrivers

/-! The fixed Pascal preparation calls each update one owned output and
retain their driver/log fields. This is a projection of the existing Step
focus receipt, keeping their seven joins symbolic in the ambient size. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem single_dock {t u s n : ℕ} (p : Machine t s) (slots : Fin t→Fin u)
    (hi:Function.Injective slots) (A : Fin u→List Bool) (out : Fin t→List Bool)
    (j : Fin t) (value : List Bool)
    (h:Step p n (fun _=>0) (fun k=>A (slots k)) (fun _=>0) out)
    (ho:∀ k,out k=if k=j then value else A (slots k)):
    Step (RecoveryFocus.machine slots p) n (fun _=>0) A (fun _=>0) (Function.update A (slots j) value):=by
  have focused:=h.focus slots hi (fun _=>0) A
  have heads:dockH slots (fun _=>0) (fun _=>0)=(fun _=>0):=by
    funext i;unfold dockH;split <;> rfl
  refine focused.congr_in heads (install_existing slots A _ (by intro k;rfl)) |>.congr heads ?_
  funext i
  cases hp:RecoveryFocus.pick slots i with
  | none=>
    have hn:slots j≠i:=by
      intro he
      have hj:=RecoveryFocus.pick_slot slots hi j
      rw [he,hp] at hj
      contradiction
    simp [install,hp,Ne.symm hn]
  | some k=>
    have he:=RecoveryFocus.slot_of_pick slots hp
    rw [←he,install_slot slots hi,ho]
    simp only [Function.update_apply,hi.eq_iff]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching
