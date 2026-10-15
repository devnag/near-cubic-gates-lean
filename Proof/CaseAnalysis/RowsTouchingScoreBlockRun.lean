import Proof.CaseAnalysis.RowsTouchingScoreBlockQuery

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem add_run (q m k w P C x : ℕ) (withCandidate hit cur : Bool) (st : Store)
    (hb:st.scratch.length≤2*w+1)
    (hfit:ScoreAdd.skip withCandidate hit cur=false→x+st.accumulator<2^w):
    Step (add withCandidate) (12*w+15) (fun _=>0) (data q m k w P C hit cur (widened st w x))
      (fun _=>0) (data q m k w P C hit cur (updated (widened st w x) w x withCandidate hit cur)):=by
  let A:=data q m k w P C hit cur (widened st w x)
  have actual:=ScoreAdd.add_run withCandidate hit cur w x st.accumulator P st.scratch hb hfit
  have focused:=actual.focus addSlots add_injective (fun _=>0) A
  have hz:dockH addSlots (fun _=>0) (fun _=>0)=(fun _=>0):=by
    funext i;unfold dockH;split <;> rfl
  refine focused.congr_in hz (install_existing addSlots A _ ?_) |>.congr hz ?_
  · intro j;fin_cases j <;> rfl
  · cases hs:ScoreAdd.skip withCandidate hit cur
    all_goals
      simp only [hs,updated]
      funext i;fin_cases i <;> first
        | exact install_other addSlots A _ _ (by decide)
        | exact install_slot addSlots add_injective A _ 0
        | exact install_slot addSlots add_injective A _ 1
        | exact install_slot addSlots add_injective A _ 2
        | exact install_slot addSlots add_injective A _ 3
        | exact install_slot addSlots add_injective A _ 4
        | exact install_slot addSlots add_injective A _ 5
        | exact install_slot addSlots add_injective A _ 6

def after (st : Store) (q m k w : ℕ) (withCandidate hit cur : Bool):Store:=
  updated (widened (queried st q m k) w (Nat.choose m k)) w (Nat.choose m k) withCandidate hit cur

theorem block_run (q m k w P C : ℕ) (withCandidate hit cur : Bool) (st : Store)
    (hm:m≤q) (hk:k≤q) (hw:q+1≤w) (hn:st.narrow.length≤2*(q+1)+1)
    (hb:st.wide.length≤2*w+1) (hs:st.scratch.length≤2*w+1)
    (hC:Lookup.budget (PascalReady.width q) (q+1) m k+2≤C) (hW:2*w+3≤C)
    (hfit:ScoreAdd.skip withCandidate hit cur=false→Nat.choose m k+st.accumulator<2^w):
    Step (machine withCandidate) (budget q m k w) (fun _=>0) (data q m k w P C hit cur st)
      (fun _=>0) (data q m k w P C hit cur (after st q m k w withCandidate hit cur)):=by
  have first:=query_run q m k w P C hit cur st hm hk hn hC
  have second:=widen_run q m k w P C hit cur st hm hw hb hW
  have third:=add_run q m k w P C (Nat.choose m k) withCandidate hit cur (queried st q m k) hs hfit
  exact ((first.seq second).seq third).enlarge (by unfold budget;omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
