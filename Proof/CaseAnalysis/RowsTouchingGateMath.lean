import Proof.CaseAnalysis.RowsTouchingGateLengths

/-! The two physical accumulators contain exact complementary gate counts.
A unary width q+G+1 bounds their whole ordered G-gate fold. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def contribution (withCandidate : Bool) (xs : List Cell) (k : ℕ):ℕ:=
  if ScoreAdd.skip withCandidate (xs.any touched) (xs.any current) then 0
  else Nat.choose (count xs) (key withCandidate k)

theorem after_excluded (st : Store) (q k w P : ℕ) (xs : List Cell):
    (after st q k w P xs).excluded=st.excluded+contribution false xs k:=by
  cases ht:xs.any touched <;> cases hc:xs.any current <;>
    simp [after,scored,installScore,ScoreBlock.after,ScoreBlock.updated,ScoreBlock.widened,
      ScoreBlock.queried,scoreStore,summarized,contribution,ScoreAdd.skip,ht,hc,Nat.add_comm]

theorem after_included (st : Store) (q k w P : ℕ) (xs : List Cell):
    (after st q k w P xs).included=st.included+contribution true xs k:=by
  cases ht:xs.any touched <;> cases hc:xs.any current <;>
    simp [after,scored,installScore,ScoreBlock.after,ScoreBlock.updated,ScoreBlock.widened,
      ScoreBlock.queried,scoreStore,summarized,contribution,ScoreAdd.skip,ht,hc,Nat.add_comm]

theorem contribution_le (q k : ℕ) (withCandidate : Bool) (xs : List Cell) (hq:xs.length=q):
    contribution withCandidate xs k≤2^q:=by
  have hm:count xs≤q:=(GateSummary.count_le xs).trans (by omega)
  have hc:Nat.choose (count xs) (key withCandidate k)≤2^q:=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide : 0<2) hm)
  unfold contribution
  split <;> omega

def states (q k w P : ℕ) (records : List (List Cell)) (initial : Store):ℕ→Store
  | 0=>initial
  | j+1=>after (states q k w P records initial j) q k w P (records.getD j [])

theorem states_valid (q k w P : ℕ) (records : List (List Cell)) (initial : Store)
    (hq:∀ xs∈records,xs.length=q) (hP:q+1≤P) (valid:Valid q w P initial)
    (j : ℕ) (hj:j≤records.length):Valid q w P (states q k w P records initial j):=by
  induction j with
  | zero=>exact valid
  | succ j ih=>
    have hj':j<records.length:=by omega
    have he:records.getD j []∈records:=by
      rw [List.getD_eq_getElem records [] hj'];exact List.getElem_mem hj'
    exact after_valid q k w P _ _ (ih (by omega)) (by rw [hq _ he];exact hP)

theorem states_scores (q k w P : ℕ) (records : List (List Cell)) (initial : Store)
    (hq:∀ xs∈records,xs.length=q) (j : ℕ) (hj:j≤records.length):
    (states q k w P records initial j).excluded≤ initial.excluded+j*2^q ∧
    (states q k w P records initial j).included≤ initial.included+j*2^q:=by
  induction j with
  | zero=>simp [states]
  | succ j ih=>
    have hj':j<records.length:=by omega
    have he:records.getD j []∈records:=by
      rw [List.getD_eq_getElem records [] hj'];exact List.getElem_mem hj'
    have hfalse:=contribution_le q k false (records.getD j []) (hq _ he)
    have htrue:=contribution_le q k true (records.getD j []) (hq _ he)
    have old:=ih (by omega)
    simp only [states,after_excluded,after_included,Nat.add_mul,Nat.one_mul]
    omega

theorem fold_fits (q G j a : ℕ) (hj:j<G) (ha:a≤j*2^q):2^q+a<2^(q+G+1):=by
  have hg:G<2^G:=Nat.lt_two_pow_self
  have hp:0<2^q:=by positivity
  have hb:G*2^q<2^G*2^q:=Nat.mul_lt_mul_of_pos_right hg hp
  rw [←Nat.pow_add] at hb
  have he:2^(G+q)≤2^(q+G+1):=Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hs:2^q+a≤G*2^q:=by nlinarith
  exact hs.trans_lt (hb.trans_le he)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
