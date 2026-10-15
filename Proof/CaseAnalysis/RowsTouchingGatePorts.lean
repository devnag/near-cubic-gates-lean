import Proof.CaseAnalysis.RowsTouchingGateLayout

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem summary_heads (pos : ℕ):
    (fun i=>Fin.addCases (m:=9) (n:=15) (motive:=fun _=>ℕ) (GateSummary.heads pos) (fun _=>0) i)=heads pos:=by
  funext i;fin_cases i <;> rfl

theorem block_heads (withCandidate : Bool) (pos : ℕ) (j : Fin 17):
    heads pos (blockSlots withCandidate j)=0:=by
  cases withCandidate <;> fin_cases j <;> rfl

theorem block_data (q k w P C : ℕ) (source : List Bool) (xs : List Cell) (st : Store)
    (withCandidate : Bool) (hs:st.summary=GateSummary.result P xs):
    (fun j=>data q k w P C source xs st (blockSlots withCandidate j))=
      ScoreBlock.data q (count xs) (key withCandidate k) w P C (xs.any touched) (xs.any current)
        (scoreStore st withCandidate):=by
  rcases st with ⟨summary,narrow,wide,scratch,excluded,included⟩
  change summary=GateSummary.result P xs at hs
  subst summary
  cases withCandidate <;> funext j
  all_goals fin_cases j <;> rfl

theorem score_restored (st : Store) (withCandidate : Bool) (score : ScoreBlock.Store):
    scoreStore (installScore st withCandidate score) withCandidate=score:=by
  cases withCandidate <;> cases score <;> rfl

theorem vector_outside {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    narrow wide scratch acc : α) (mode : Bool) (i : Fin 15)
    (h3:i≠3) (h6:i≠6) (h11:i≠11) (hacc:i≠if mode then 10 else 9):
    (![a0,a1,a2,narrow,a4,a5,wide,a7,a8,if mode then a9 else acc,
      if mode then acc else a10,scratch,a12,a13,a14] : Fin 15→α) i=
      (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14] : Fin 15→α) i:=by
  cases mode <;> fin_cases i <;> simp_all

theorem outside_same (q k w P C : ℕ) (source : List Bool) (xs : List Cell) (st : Store)
    (withCandidate : Bool) (score : ScoreBlock.Store) (i : Fin 24)
    (hi:∀ j,blockSlots withCandidate j≠i):
    data q k w P C source xs (installScore st withCandidate score) i=data q k w P C source xs st i:=by
  revert hi
  refine Fin.addCases (m:=9) (n:=15) ?_ ?_ i
  · intro j hj
    simp only [data,Fin.addCases_left,installScore]
  · intro j hj
    simp only [data,Fin.addCases_right]
    have hn:j≠3:=by intro he;subst j;exact hj (⟨4,by decide⟩ : Fin 17) rfl
    have hw:j≠6:=by intro he;subst j;exact hj (⟨8,by decide⟩ : Fin 17) rfl
    have hs:j≠11:=by intro he;subst j;exact hj (⟨12,by decide⟩ : Fin 17) rfl
    have ha:j≠if withCandidate then 10 else 9:=by
      intro he
      cases withCandidate <;> subst j <;> exact hj (⟨11,by decide⟩ : Fin 17) rfl
    cases withCandidate
    · exact vector_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false j hn hw hs ha
    · exact vector_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ true j hn hw hs ha

theorem replace_data (q k w P C : ℕ) (source : List Bool) (xs : List Cell) (st : Store)
    (withCandidate : Bool) (score : ScoreBlock.Store) (hs:st.summary=GateSummary.result P xs):
    install (blockSlots withCandidate) (data q k w P C source xs st)
      (ScoreBlock.data q (count xs) (key withCandidate k) w P C (xs.any touched) (xs.any current) score)=
      data q k w P C source xs (installScore st withCandidate score):=by
  apply HierarchyWidth.install_eq (blockSlots withCandidate) (block_injective withCandidate)
  · intro j
    have hs' : (installScore st withCandidate score).summary=GateSummary.result P xs := hs
    have projected := congrFun (block_data q k w P C source xs
      (installScore st withCandidate score) withCandidate hs') j
    rw [score_restored] at projected
    exact projected
  · exact outside_same q k w P C source xs st withCandidate score

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
