import Proof.Amplification.RecoveryBoundedNativeUnaryOriginalRun

/-! The original unary compiler returns its complete reusable configuration.
The retained value is the sole tape outside the reverse-fold bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def completeState {n bound : ℕ} (row : Fin (bound+1))
    (start base C value limit : ℕ) (out pre : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  RecoveryFocus.config foldSlots (fun _=>limit) (fun _=>List.replicate value true)
    (finalState row start base C value limit out pre hblock)

private theorem fold_other (i : Fin 36) (hi : ∀ j,foldSlots j≠i) : i=34 := by
  by_contra hn
  by_cases hs : i.val<34
  · let j : Fin 34 := ⟨i.val,hs⟩
    apply hi (j.castAdd 1)
    simp only [foldSlots,Fin.addCases_left]
    exact Fin.ext rfl
  · have hv : i.val=35 := by
      have hb:=i.isLt
      have hne : i.val≠34 := fun h=>hn (Fin.ext h)
      omega
    have he : i=35 := Fin.ext hv
    subst i
    exact hi 34 rfl

theorem complete_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C : ℕ) (out pre : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom machine (budget limit C)
      (entry (n:=n) row start b.nodes.length C value limit out pre)=some r ∧
      r.steps ≤ budget limit C ∧
      r.final.heads=(completeState row start b.nodes.length C value limit out pre hblock).heads ∧
      r.final.tapes=(completeState row start b.nodes.length C value limit out pre hblock).tapes := by
  obtain ⟨r,hr,rs,_ro,_ra,_rh,rv,_rg,_rb,rstate,rvalue⟩ :=
    original_run b row start limit value W C out pre hblock hi hp hC
  refine ⟨r,hr,rs,?_,?_⟩
  · funext i
    cases hpick : RecoveryFocus.pick foldSlots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick foldSlots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots (by decide)]
      exact (rstate j).1
    | none=>
      have hi : ∀ j,foldSlots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot foldSlots (by decide) j
        rw [he,hpick] at h
        contradiction
      have he:=fold_other i hi
      subst i
      simpa only [completeState,RecoveryFocus.config,hpick] using rv
  · funext i
    cases hpick : RecoveryFocus.pick foldSlots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick foldSlots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot foldSlots (by decide)]
      exact (rstate j).2
    | none=>
      have hi : ∀ j,foldSlots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot foldSlots (by decide) j
        rw [he,hpick] at h
        contradiction
      have he:=fold_other i hi
      subst i
      simpa only [completeState,RecoveryFocus.config,hpick] using rvalue

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
