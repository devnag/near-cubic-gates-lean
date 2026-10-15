import Proof.CaseAnalysis.RecoveryRowLoopRun

/-! Clear only the consumed projected batch, using the existing retained
row backing. Its source, randomness and every graph/stack cursor survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 3→Fin 115:=![109,76,77]
noncomputable def clearMachine:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)

theorem clear_run (B : ℕ) (H : Fin 115→ℕ) (A : Fin 115→List Bool)
    (hh : ∀ j,H (clearSlots j)=0) (hw : (A 109).length≤B)
    (hd : A 76=List.replicate B true) (hl : A 77=List.replicate (B+1) false) :
    ∃ r,runFrom clearMachine (2*B+4) ⟨clearMachine.start,H,A⟩=some r ∧
      r.steps≤2*B+4 ∧ r.final.heads=H ∧ r.final.tapes=Function.update A 109 (List.replicate B false) := by
  have base:=RecoveryScratchErase.erase_ready B (B+1) (fun _ : Fin 1=>A 109) (fun _=>hw)
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at clearSlots (by decide) H A
    (by intro j;fin_cases j; rfl;exact hd;exact hl) hh
  refine ⟨r,rr,rs.le,rh,?_⟩
  rw [rt]
  funext i
  by_cases h : ∃ j,clearSlots j=i
  · obtain ⟨j,rfl⟩:=h
    rw [install_slot _ (by decide : Function.Injective clearSlots)]
    fin_cases j
    · change List.replicate B false=Function.update A 109 (List.replicate B false) 109
      exact (Function.update_self (109 : Fin 115) (List.replicate B false) A).symm
    · change List.replicate B true=Function.update A 109 (List.replicate B false) 76
      rw [Function.update_of_ne (by decide)]
      exact hd.symm
    · change List.replicate (max (B+1) (B+1)) false=Function.update A 109 (List.replicate B false) 77
      rw [Nat.max_self,Function.update_of_ne (by decide)]
      exact hl.symm
  · rw [install_other _ _ _ _ (by intro j hj;exact h ⟨j,hj⟩)]
    exact (Function.update_of_ne (fun he=>h ⟨0,he.symm⟩) _ _).symm

theorem projection_update (A : Fin 78→List Bool) (P : Fin 37→List Bool) (i : Fin 37) (word : List Bool) :
    data A (Function.update P i word)=Function.update (data A P) (projectionSlots i) word :=
  bank_update_right A P i word

theorem clear_data (A : Fin 78→List Bool) (P : Fin 37→List Bool) (word : List Bool) (B : ℕ)
    (hp : P 31=List.replicate B false) :
    Function.update (data A (Function.update P 31 word)) 109 (List.replicate B false)=data A P := by
  change Function.update (data A (Function.update P 31 word)) (projectionSlots 31) (List.replicate B false)=_
  rw [←projection_update,Function.update_idem]
  apply congrArg (data A)
  simpa only [hp] using Function.update_eq_self 31 P

theorem clear_row_run (H : Fin 78→ℕ) (A : Fin 78→List Bool) (P : Fin 37→List Bool)
    (word : List Bool) (B : ℕ) (h76 : H 76=0) (h77 : H 77=0)
    (d76 : A 76=List.replicate B true) (d77 : A 77=List.replicate (B+1) false)
    (hp : P 31=List.replicate B false) (hw : word.length≤B) :
    ∃ r,runFrom clearMachine (2*B+4)
      ⟨clearMachine.start,heads H,data A (Function.update P 31 word)⟩=some r ∧
      r.steps≤2*B+4 ∧ r.final.heads=heads H ∧ r.final.tapes=data A P := by
  obtain ⟨r,rr,rs,rh,rt⟩:=clear_run B (heads H) (data A (Function.update P 31 word))
    (by
      intro j;fin_cases j
      · exact heads_projection H 31
      · exact (heads_row H 76).trans h76
      · exact (heads_row H 77).trans h77)
    (by change (data A (Function.update P 31 word) (projectionSlots 31)).length≤B
        rw [data_projection,Function.update_self]
        exact hw)
    ((data_row A _ 76).trans d76) ((data_row A _ 77).trans d77)
  exact ⟨r,rr,rs,rh,rt.trans (clear_data A P word B hp)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
