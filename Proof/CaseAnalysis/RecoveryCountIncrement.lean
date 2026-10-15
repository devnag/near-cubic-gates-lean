import Proof.CaseAnalysis.RecoveryRowPacketInstall

/-! The original grammar's candidate k becomes the row count k+1 and the
next grammar candidate on the same raw tape. The existing increment pays
its rewind and preserves the complete enclosing scalar bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountIncrement
open LocalBitMultitape RecoveryRootRound RepairSource
open RecoveryBoundedRowPacketAppend (Loaded values scalarPort)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 88:=![81,73]
noncomputable def machine:=RecoveryFocus.machine slots RecoveryTseitinRawIncrement.machine
def next (A : Fin 88→List Bool) (count : ℕ):=Function.update A 81 (List.replicate (count+1) true)

theorem run (count B : ℕ) (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (hH : H 81=0) (hL : H 73=0) (hA : A 81=List.replicate count true)
    (hLog : A 73=List.replicate B false) (hB : count+1≤B) :
    ∃ r,runFrom machine (2*count+4) ⟨machine.start,H,A⟩=some r ∧ r.steps≤2*count+4 ∧
      r.final.heads=H ∧ r.final.tapes=next A count := by
  obtain ⟨r,rr,rh,rt,rs⟩:=(RecoveryTseitinRawIncrement.increment_ready count B hB).focus_at
    slots (by decide) H A (by intro j;fin_cases j;exact hA;exact hLog)
    (by intro j;fin_cases j;exact hH;exact hL)
  refine ⟨r,rr,rs.le,rh,?_⟩
  rw [rt]
  apply HierarchyWidth.install_eq slots (by decide)
  · intro j;fin_cases j
    · rfl
    · change A 73=List.replicate B false
      exact hLog
  · intro i hi
    have h81 : i≠81:=fun he=>hi 0 he.symm
    exact Function.update_of_ne h81 _ _

theorem values_other (C F R count Q clauses : ℕ) (j : Fin 10) (hj : j≠3) :
    values C F R (count+1) Q clauses j=values C F R count Q clauses j := by
  fin_cases j <;> first | rfl | exact False.elim (hj rfl)

theorem loaded_next {C F R count Q clauses B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded (values C F R count Q clauses) B H A) (hB : 2*(count+1)+4≤B) :
    Loaded (values C F R (count+1) Q clauses) B H (next A count) := by
  refine ⟨h.heads,?_,h.scratch_head,?_,?_⟩
  · intro j
    by_cases hj : j=3
    · subst j;rfl
    · rw [values_other C F R count Q clauses j hj]
      have hp : scalarPort j≠81:=by
        intro he
        have hval:=congrArg Fin.val he
        change 78+j.val=81 at hval
        exact hj (Fin.ext (by omega))
      change Function.update A 81 _ (scalarPort j)=_
      rw [Function.update_of_ne hp]
      exact h.tapes j
  · change Function.update A 81 _ 73=List.replicate B false
    rw [Function.update_of_ne (by decide)]
    exact h.scratch_tape
  · intro j
    by_cases hj : j=3
    · subst j;exact hB
    · rw [values_other C F R count Q clauses j hj]
      exact h.bounds j

theorem loaded_run {C F R count Q clauses B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded (values C F R count Q clauses) B H A) :
    ∃ r,runFrom machine (2*count+4) ⟨machine.start,H,A⟩=some r ∧ r.steps≤2*count+4 ∧
      r.final.heads=H ∧ r.final.tapes=next A count :=
  run count B H A (h.heads 3) h.scratch_head (h.tapes 3) h.scratch_tape
    (by have hb:=h.bounds 3;change 2*count+4≤B at hb;omega)

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountIncrement
