import Proof.CaseAnalysis.RecoveryClauseFoldState

/-! Existing paid copy/increment returns the fold accumulator as the live
clause-list output and advances the actual graph count, on the same bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseResult
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedClauseFold (old old_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 73:=![25,45,32,22,23]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedClauseReplace.localMachine
def data (A : Fin 73→List Bool) (node C : ℕ):=
  Function.update (Function.update A 45 (ZeroPadding.pad C (List.replicate node true))) 25 (List.replicate (node+1) true)

theorem project_data (A : Fin 73→List Bool) (node C : ℕ) (out : List Bool) (hA : A 20=out) :
    data A node C∘old=RecoveryBoundedClauseOr.data (A∘old) node C out := by
  change Function.update (Function.update A (old 45) (ZeroPadding.pad C (List.replicate node true)))
    (old 25) (List.replicate (node+1) true)∘old=_
  rw [Function.update_comp_eq_of_injective _ old_injective 25,Function.update_comp_eq_of_injective _ old_injective 45]
  unfold RecoveryBoundedClauseOr.data
  have he : (A∘old) 20=out:=hA
  rw [←he,Function.update_eq_self]

theorem result_state (H : Fin 73→ℕ) (A : Fin 73→List Bool) (node right C L : ℕ)
    (out pre source refs : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) node 0 right C L out pre source refs) :
    RecoveryBoundedClauseState.State (H∘old) (data A node C∘old) (node+1) node right C L out pre source refs := by
  have hg : A 20=out := by
    have ha:=h.gateA 20
    change A 20=ZeroPadding.pad 0 out at ha
    simpa only [ZeroPadding.pad_zero] using ha
  have hh : RecoveryBoundedClauseOr.heads (H∘old) out=H∘old := by
    have ht : (H∘old) 20=out.length:=h.gateH 20
    unfold RecoveryBoundedClauseOr.heads
    rw [←ht,Function.update_eq_self]
  have hs:=RecoveryBoundedClauseOr.node_state (H∘old) (A∘old) node 0 right C L out pre source refs out h
  rw [hh,←project_data A node C out hg] at hs
  exact hs

theorem result_run (H : Fin 73→ℕ) (A : Fin 73→List Bool) (node right W C L : ℕ)
    (out pre source refs : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) node 0 right C L out pre source refs)
    (hn : node ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom machine (RecoveryBoundedClauseReplace.budget node C) ⟨machine.start,H,A⟩=some r ∧
      r.steps=RecoveryBoundedClauseReplace.budget node C ∧ r.final.heads=H ∧ r.final.tapes=data A node C ∧
      RecoveryBoundedClauseState.State (r.final.heads∘old) (r.final.tapes∘old) (node+1) node right C L out pre source refs := by
  have hc : node+1 ≤ C:=by nlinarith [Nat.zero_le (W^2)]
  have hH : ∀ j,H (slots j)=0:=by intro j;fin_cases j <;> first
    | exact h.restoreH 0 | exact h.restoreH 1 | exact h.restoreH 2 | exact h.restoreH 3 | exact h.restoreH 4
  have hA : ∀ j,A (slots j)=RecoveryBoundedClauseReplace.data node 0 C 0 j:=by intro j;fin_cases j <;> first
    | exact h.restoreA 0 | exact h.restoreA 1 | exact h.restoreA 2 | exact h.restoreA 3 | exact h.restoreA 4
  obtain ⟨r,rr,rh,rt,rs⟩:=(RecoveryBoundedClauseReplace.replace_ready node 0 C (Nat.zero_le C) hc).focus_at
    slots slots_injective H A hA hH
  have he : install slots A (RecoveryBoundedClauseReplace.data node 0 C 3)=data A node C := by
    apply HierarchyWidth.install_eq slots slots_injective
    · intro j
      fin_cases j <;> first | rfl | exact hA 2 | exact hA 3 | exact hA 4
    · intro i hi
      have h25 : i≠25:=fun he=>hi 0 he.symm
      have h45 : i≠45:=fun he=>hi 1 he.symm
      simp only [data,Function.update_of_ne h25,Function.update_of_ne h45]
  rw [he] at rt
  refine ⟨r,rr,rs,rh,rt,?_⟩
  rw [rh,rt]
  exact result_state H A node right C L out pre source refs h

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseResult
