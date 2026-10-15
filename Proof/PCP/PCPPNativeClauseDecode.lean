import Proof.PCP.PCPPNativeClauseFieldLayout
import Proof.Amplification.RecoveryProjectionDimensionUnary

/-! Decode the copied original binary literal field and pay the sentinel
cursor retreat. The live source cursor and native parameters are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseField
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
open RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decodeMachine :=
  RecoveryFocus.machine unarySlots RecoveryProjectionDimension.parsedMachine

theorem unary_away (j : Fin 13) (hj : j ≠ 0) :
    ∀ k, unarySlots k ≠ refSlots j := by
  intro k
  have hz : j.val ≠ 0 := by intro h; exact hj (Fin.ext h)
  fin_cases k <;> simp [unarySlots,refSlots,Fin.ext_iff] <;> omega

theorem decode_run (source bits : List Bool) (pos index : ℕ) (sign : Bool)
    (stride p n : ℕ) (hv : value bits=2*index+sign.toNat) : ∃ r,
    runFrom decodeMachine (Unary.budget bits+2)
      (entry decodeMachine pos (copied source bits stride p n))=some r ∧
      r.final.heads=heads pos ∧
      (∀ j : Fin 13,r.final.tapes (refSlots j)=
        PCPPNativeClauseReference.wordInput index sign stride p n j) ∧
      r.final.tapes 13=source ∧ r.steps ≤ Unary.budget bits+2 := by
  obtain ⟨out,⟨base,hb,bt,bh,bs⟩,hword⟩ := RecoveryProjectionDimension.parsed_ready bits
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩ := RecoveryFocus.dock unarySlots unary_injective
    RecoveryProjectionDimension.parsedMachine _ (heads pos) (copied source bits stride p n)
    (initialConfiguration RecoveryProjectionDimension.parsedMachine (Unary.input bits))
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl) base hb
  refine ⟨r,hr,?_,?_,?_,rs.le.trans bs⟩
  · funext i
    by_cases hi : ∃ j,unarySlots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [rh j,bh j]
      fin_cases j <;> rfl
    · exact (keep i (by intro j hj; exact hi ⟨j,hj⟩)).1
  · intro j
    by_cases hj : j=0
    · subst j
      exact (rt 3).trans (by rw [bt,hword,hv]; rfl)
    · rw [(keep (refSlots j) (unary_away j hj)).2]
      have h14 : refSlots j ≠ 14 := by simp [refSlots,Fin.ext_iff]; omega
      have h15 : refSlots j ≠ 15 := by simp [refSlots,Fin.ext_iff]; omega
      have h13 : refSlots j ≠ 13 := by simp [refSlots,Fin.ext_iff]; omega
      simp only [copied,h14,h15,ite_false,input,h13,
        PCPPNativeClauseReference.wordInput,hj,PCPPNativeClauseReference.input]
      simp only [refSlots,Fin.ext_iff]
      rfl
  · rw [(keep 13 (by intro j; fin_cases j <;> decide)).2]
    rfl

end NearCubicWires.RepairOrdinary.PCPPNativeClauseField
