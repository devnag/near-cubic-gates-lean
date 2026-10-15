import Proof.CaseAnalysis.RecoveryClauseRun

/-! Push the actual retained clause output directly in the reversed-frame
format consumed by the existing AND fold. Only the extra stack tape changes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseCollect
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryBoundedClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 72:=![45,71,34]
def old (j : Fin 71) : Fin 72:=j.castAdd 1
def pushed (ref : ℕ) (stack : List Bool):=stack++(frame (List.replicate ref true)).reverse
noncomputable def machine:=RecoveryFocus.machine slots PCPUnaryStackPush.machine
def heads (H : Fin 72→ℕ) (stack : List Bool):=Function.update H 71 stack.length
def data (A : Fin 72→List Bool) (stack : List Bool):=Function.update A 71 stack

theorem padded_run (ref C : ℕ) (stack : List Bool) (hC : 2*ref+2 ≤ C) :
    ∃ r,runFrom PCPUnaryStackPush.machine (4*ref+6)
      ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
        ![ZeroPadding.pad C (List.replicate ref true),stack,List.replicate C false]⟩=some r ∧
      r.final.heads=![0,(pushed ref stack).length,0] ∧
      r.final.tapes=![ZeroPadding.pad C (List.replicate ref true),pushed ref stack,List.replicate C false] ∧
      r.steps ≤ 4*ref+6 := by
  obtain ⟨p,pr,pt,ph,ps⟩:=RecoveryBoundedNativeReference.push_run ref C stack hC
  let caps : Fin 3→ℕ:=![C,0,0]
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config PCPUnaryStackPush.machine caps _ _ p pr
  have hi : ZeroPadding.config caps
      (⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
        ![List.replicate ref true,stack,List.replicate C false]⟩ : Configuration 3 6)=
      ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
        ![ZeroPadding.pad C (List.replicate ref true),stack,List.replicate C false]⟩ := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _
  rw [hi] at rr
  refine ⟨r,rr,?_,?_,rs.le.trans ps⟩
  · rw [rf]
    change p.final.heads=_
    rw [ph]
    simp only [pushed,List.length_append,List.length_reverse,frame_length,List.length_replicate,Nat.add_assoc]
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps i) (p.final.tapes i))=_
    rw [pt]
    funext i;fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _

theorem collect_run (H : Fin 72→ℕ) (A : Fin 72→List Bool) (ref C : ℕ) (stack : List Bool)
    (hH : ∀ j,H (slots j)=(![0,stack.length,0] : Fin 3→ℕ) j)
    (hA : ∀ j,A (slots j)=(![ZeroPadding.pad C (List.replicate ref true),stack,List.replicate C false] : Fin 3→List Bool) j)
    (hC : 2*ref+2 ≤ C) :
    ∃ r,runFrom machine (4*ref+6) ⟨machine.start,H,A⟩=some r ∧ r.steps ≤ 4*ref+6 ∧
      r.final.heads=heads H (pushed ref stack) ∧ r.final.tapes=data A (pushed ref stack) := by
  obtain ⟨p,pr,ph,pt,ps⟩:=padded_run ref C stack hC
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots (by decide) PCPUnaryStackPush.machine _ H A
    ⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
      ![ZeroPadding.pad C (List.replicate ref true),stack,List.replicate C false]⟩ hH hA p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · change 0=Function.update H 71 (pushed ref stack).length 45
        rw [Function.update_of_ne (by decide)]
        exact (hH 0).symm
      · rfl
      · change 0=Function.update H 71 (pushed ref stack).length 34
        rw [Function.update_of_ne (by decide)]
        exact (hH 2).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      exact (Function.update_of_ne (fun he=>hi ⟨1,he.symm⟩) _ _).symm
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · change ZeroPadding.pad C (List.replicate ref true)=Function.update A 71 (pushed ref stack) 45
        rw [Function.update_of_ne (by decide)]
        exact (hA 0).symm
      · rfl
      · change List.replicate C false=Function.update A 71 (pushed ref stack) 34
        rw [Function.update_of_ne (by decide)]
        exact (hA 2).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      exact (Function.update_of_ne (fun he=>hi ⟨1,he.symm⟩) _ _).symm

theorem old_heads (H : Fin 72→ℕ) (stack : List Bool) : heads H stack∘old=H∘old := by
  funext j
  have hj : old j≠71:=by intro h;have hv:=congrArg (fun k : Fin 72=>k.val) h;change j.val=71 at hv;omega
  exact Function.update_of_ne hj _ _
theorem old_data (A : Fin 72→List Bool) (stack : List Bool) : data A stack∘old=A∘old := by
  funext j
  have hj : old j≠71:=by intro h;have hv:=congrArg (fun k : Fin 72=>k.val) h;change j.val=71 at hv;omega
  exact Function.update_of_ne hj _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseCollect
