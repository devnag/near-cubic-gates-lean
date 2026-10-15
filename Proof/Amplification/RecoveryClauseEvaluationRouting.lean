import Proof.Amplification.RecoveryClauseEvaluationTapes

/-! Pure routing facts keep the large stored-data expressions opaque while
checking the exact clause return. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem routing_extra_slot (which : Fin 3) (j : Fin 13) :
    ∃ k,assignmentSlots which k=(j.castAdd 1).natAdd 28 := by
  fin_cases j
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩
  · exact ⟨10,rfl⟩
  · exact ⟨11,rfl⟩
  · exact ⟨12,rfl⟩
  · exact ⟨13,rfl⟩

theorem routing_outside (which : Fin 3) (input output : Fin 42→List Bool)
    (hcore : ∀ j : Fin 28,j≠savedSlot which → input (j.castAdd 14)=output (j.castAdd 14))
    (hlast : input 41=output 41) (i : Fin 42) (hi : ∀ j,assignmentSlots which j≠i) :
    input i=output i := by
  by_cases hlo : i.val<28
  · let j : Fin 28 := ⟨i.val,hlo⟩
    have he : j.castAdd 14=i := Fin.ext rfl
    rw [← he]
    apply hcore
    intro hj
    apply hi 3
    change (savedSlot which).castAdd 14=i
    rw [← hj,he]
  · have htop : 41 ≤ i.val := by
      by_contra hn
      let j : Fin 13 := ⟨i.val-28,by omega⟩
      obtain ⟨k,hk⟩ := routing_extra_slot which j
      apply hi k
      apply hk.trans
      apply Fin.ext
      simp only [Fin.val_natAdd,Fin.val_castAdd]
      dsimp [j]
      omega
    have he : i=41 := Fin.ext (by omega)
    subst i
    exact hlast

@[simp] theorem tapes_aggregate (s : State) (e : Extra) : tapes s e 41=[e.aggregate] := rfl

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
