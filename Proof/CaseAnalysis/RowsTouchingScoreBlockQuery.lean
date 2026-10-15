import Proof.CaseAnalysis.RowsTouchingScoreBlockLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem query_run (q m k w P C : ℕ) (hit cur : Bool) (st : Store) (hm:m≤q) (hk:k≤q)
    (hb:st.narrow.length≤2*(q+1)+1) (hC:Lookup.budget (PascalReady.width q) (q+1) m k+2≤C):
    Step query (LookupReady.budget q m k) (fun _=>0) (data q m k w P C hit cur st)
      (fun _=>0) (data q m k w P C hit cur (queried st q m k)):=by
  have actual:=(LookupCounted.lookup_run q m k P C st.narrow hm hk hb hC).embed
    (fun _ : Fin 9=>0) (extra w P hit cur st)
  refine actual.congr_in ?_ rfl |>.congr ?_ rfl
  all_goals funext i;fin_cases i <;> rfl

theorem widen_run (q m k w P C : ℕ) (hit cur : Bool) (st : Store) (hm:m≤q) (hw:q+1≤w)
    (hb:st.wide.length≤2*w+1) (hC:2*w+3≤C):
    Step widen (8*w+15) (fun _=>0) (data q m k w P C hit cur (queried st q m k))
      (fun _=>0) (data q m k w P C hit cur (widened (queried st q m k) w (Nat.choose m k))):=by
  let A:=data q m k w P C hit cur (queried st q m k)
  let value:=frame (binary w (Nat.choose m k))
  have actual:=ScoreWiden.widen_run (q+1) w C (Nat.choose m k) st.wide hw
    (RepairSource.CloseoutTouchingArithmetic.binomial_fits q m k hm) hb hC
  have innerStep:Step ScoreWiden.machine (8*w+15) (fun _=>0) (fun j=>A (wideSlots j))
      (fun _=>0) (ScoreWiden.input (q+1) w C (Nat.choose m k) value):=by
    refine actual.congr_in rfl ?_
    funext j;fin_cases j <;> rfl
  have focused:=single_dock ScoreWiden.machine wideSlots wide_injective A _ 1 value innerStep (by
    intro j;fin_cases j <;> rfl)
  refine focused.congr rfl ?_
  funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
