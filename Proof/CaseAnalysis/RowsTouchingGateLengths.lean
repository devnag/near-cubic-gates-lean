import Proof.CaseAnalysis.RowsTouchingGateLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open LocalBitMultitape SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Valid (q w P : ℕ) (st : Store):Prop:=
  (∀ j,(st.summary j).length≤P) ∧ st.narrow.length≤2*(q+1)+1 ∧
    st.wide.length≤2*w+1 ∧ st.scratch.length≤2*w+1

theorem summarized_valid (q w P : ℕ) (xs : List Cell) (st : Store)
    (h:Valid q w P st) (hp:xs.length+1≤P):Valid q w P (summarized st P xs):=by
  refine ⟨?_,h.2⟩
  intro j
  exact (GateSummary.result_length P xs hp j).le

theorem scored_summary (st : Store) (q m k w : ℕ) (withCandidate hit cur : Bool):
    (scored st q m k w withCandidate hit cur).summary=st.summary:=rfl

theorem scored_bounds (q m k w : ℕ) (withCandidate hit cur : Bool) (st : Store)
    (h:st.scratch.length≤2*w+1):
    (scored st q m k w withCandidate hit cur).narrow.length≤2*(q+1)+1 ∧
    (scored st q m k w withCandidate hit cur).wide.length≤2*w+1 ∧
    (scored st q m k w withCandidate hit cur).scratch.length≤2*w+1:=by
  cases hs:ScoreAdd.skip withCandidate hit cur <;>
    simp [scored,installScore,ScoreBlock.after,ScoreBlock.updated,ScoreBlock.widened,ScoreBlock.queried,scoreStore,hs,h]

theorem scored_valid (q m k w P : ℕ) (withCandidate hit cur : Bool) (st : Store)
    (h:Valid q w P st):Valid q w P (scored st q m k w withCandidate hit cur):=
  ⟨h.1,scored_bounds q m k w withCandidate hit cur st h.2.2.2⟩

theorem excluded_preserves_included (st : Store) (q m k w : ℕ) (hit cur : Bool):
    (scored st q m k w false hit cur).included=st.included:=rfl

theorem after_valid (q k w P : ℕ) (xs : List Cell) (st : Store)
    (h:Valid q w P st) (hp:xs.length+1≤P):Valid q w P (after st q k w P xs):=
  scored_valid q (count xs) k w P true (xs.any touched) (xs.any current) _
    (scored_valid q (count xs) k w P false (xs.any touched) (xs.any current) _
      (summarized_valid q w P xs st h hp))

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
