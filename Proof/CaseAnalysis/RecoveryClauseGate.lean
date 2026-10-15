import Proof.CaseAnalysis.RecoveryClauseNative

/-! Append a single original clause node while retaining the full query bank.
The four fixed calls are NOT(left), NOT(right), AND and OR. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseGate
open LocalBitMultitape RepairRepresentation RecoveryRootRound
open RecoveryBoundedUniversalGates (data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeKind : Fin 4→Fin 3:=![0,0,1,2]
def leftPort (kind : Fin 4) : Fin 61:=if kind=1 then 47 else 45
def rightPort (kind : Fin 4) : Fin 61:=if kind.val<2 then 34 else 47
def slots (kind : Fin 4) (j : Fin 29) : Fin 61:=
  if j=1 then leftPort kind else if j=25 then rightPort kind else j.castAdd 32
theorem slots_injective (kind : Fin 4) : Function.Injective (slots kind) := by fin_cases kind <;> decide
theorem slots_twenty (kind : Fin 4) : slots kind 20=20 := by rfl
noncomputable def machine (kind : Fin 4):=RecoveryFocus.machine (slots kind) (RecoveryBoundedClauseNative.machine (nativeKind kind))
def heads (H : Fin 61→ℕ) (result : List Bool):=Function.update H 20 result.length
def output (A : Fin 61→List Bool) (result : List Bool):=Function.update A 20 result

theorem local_output (left right C : ℕ) (out result : List Bool) (j : Fin 29) :
    data left right C result j=if j=20 then result else data left right C out j := by
  fin_cases j <;> first | rfl | exact ZeroPadding.pad_zero _
theorem local_heads (out result : List Bool) (j : Fin 29) :
    PCPPNativeClauseBank.heads result j=if j=20 then result.length else PCPPNativeClauseBank.heads out j := by
  fin_cases j <;> rfl

theorem install_output (kind : Fin 4) (A : Fin 61→List Bool) (left right C : ℕ) (out result : List Bool)
    (hA : ∀ j,A (slots kind j)=data left right C out j) :
    install (slots kind) A (data left right C result)=output A result := by
  apply HierarchyWidth.install_eq (slots kind) (slots_injective kind)
  · intro j
    by_cases hj : j=20
    · subst j
      rw [slots_twenty]
      change result=ZeroPadding.pad 0 result
      exact (ZeroPadding.pad_zero _).symm
    · have hs : slots kind j≠20:=fun h=>hj (slots_injective kind (h.trans (slots_twenty kind).symm))
      rw [local_output left right C out result j,if_neg hj]
      simp only [output,Function.update_of_ne hs]
      exact hA j
  · intro i hi
    have h20 : i≠20:=fun h=>hi 20 ((slots_twenty kind).trans h.symm)
    simp only [output,Function.update_of_ne h20]

theorem gate_run (kind : Fin 4) (H : Fin 61→ℕ) (A : Fin 61→List Bool)
    (left right W C : ℕ) (out : List Bool)
    (hH : ∀ j,H (slots kind j)=PCPPNativeClauseBank.heads out j)
    (hA : ∀ j,A (slots kind j)=data left right C out j)
    (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let result:=out++RecoveryBoundedClauseNative.emitted (nativeKind kind) left right
    ∃ r,runFrom (machine kind) (RecoveryBoundedClauseNative.budget (nativeKind kind) left right C)
      ⟨(machine kind).start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedClauseNative.budget (nativeKind kind) left right C ∧
      r.final.heads=heads H result ∧ r.final.tapes=output A result := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedClauseNative.padded_run (nativeKind kind) left right W C out hl hr hC
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (slots kind) (slots_injective kind)
    (RecoveryBoundedClauseNative.machine (nativeKind kind)) _ H A
    ⟨(RecoveryBoundedClauseNative.machine (nativeKind kind)).start,PCPPNativeClauseBank.heads out,data left right C out⟩
    hH hA p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots kind j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph,local_heads out _ j]
      by_cases hj : j=20
      · subst j
        rw [slots_twenty]
        simp only [↓reduceIte,heads,Function.update_self]
      · have hs : slots kind j≠20:=fun h=>hj (slots_injective kind (h.trans (slots_twenty kind).symm))
        simp only [if_neg hj,heads,Function.update_of_ne hs]
        exact (hH j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h20 : i≠20:=fun h=>hi ⟨20,(slots_twenty kind).trans h.symm⟩
      simp only [heads,Function.update_of_ne h20]
  · have he:=HierarchyWidth.install_eq (slots kind) (slots_injective kind) A r.final.tapes
      (data left right C (out++RecoveryBoundedClauseNative.emitted (nativeKind kind) left right))
      (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    exact install_output kind A left right C out _ hA

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseGate
