import Proof.CaseAnalysis.RecoveryRowPadding

/-! Preserve each original row output on the outer reversed AND stack.
The already-reset row log supplies the paid reusable push workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowCollect
open LocalBitMultitape RecoveryRootRound RecoveryBoundedClauseCollect
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 78:=![45,74,73]
noncomputable def machine:=RecoveryFocus.machine slots PCPUnaryStackPush.machine
def heads (H : Fin 78→ℕ) (stack : List Bool):=Function.update H 74 stack.length
def data (A : Fin 78→List Bool) (stack : List Bool):=Function.update A 74 stack

theorem collect_run (H : Fin 78→ℕ) (A : Fin 78→List Bool) (ref B : ℕ) (stack : List Bool)
    (hH : ∀ j,H (slots j)=(![0,stack.length,0] : Fin 3→ℕ) j)
    (hA : ∀ j,A (slots j)=(![ZeroPadding.pad B (List.replicate ref true),stack,List.replicate B false] : Fin 3→List Bool) j)
    (hB : 2*ref+2 ≤ B) :
    ∃ r,runFrom machine (4*ref+6) ⟨machine.start,H,A⟩=some r ∧ r.steps ≤ 4*ref+6 ∧
      r.final.heads=heads H (pushed ref stack) ∧ r.final.tapes=data A (pushed ref stack) := by
  obtain ⟨p,pr,ph,pt,ps⟩:=padded_run ref B stack hB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots (by decide) PCPUnaryStackPush.machine _ H A
    ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
      ![ZeroPadding.pad B (List.replicate ref true),stack,List.replicate B false]⟩ hH hA p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · change 0=Function.update H 74 (pushed ref stack).length 45
        rw [Function.update_of_ne (by decide)]
        exact (hH 0).symm
      · rfl
      · change 0=Function.update H 74 (pushed ref stack).length 73
        rw [Function.update_of_ne (by decide)]
        exact (hH 2).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      exact (Function.update_of_ne (fun he=>hi ⟨1,he.symm⟩) _ _).symm
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · change ZeroPadding.pad B (List.replicate ref true)=Function.update A 74 (pushed ref stack) 45
        rw [Function.update_of_ne (by decide)]
        exact (hA 0).symm
      · rfl
      · change List.replicate B false=Function.update A 74 (pushed ref stack) 73
        rw [Function.update_of_ne (by decide)]
        exact (hA 2).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      exact (Function.update_of_ne (fun he=>hi ⟨1,he.symm⟩) _ _).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowCollect
