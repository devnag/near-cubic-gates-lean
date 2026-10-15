import Proof.Hierarchy.CompetitorFinalTableLayout

/-! The first actual ambient stage consumes the grouped same bank and
restores the native context. Physical Q/U/parity remain unselected. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneTable
open CompetitorPlaneStream (oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Native {n : ℕ} (b w : ℕ) (state : State n) (tapes : Fin 159 → List Bool) : Prop :=
  TableContext b w state (fun i : Fin 34 => tapes (i.castAdd 125))

theorem merge_run {n : ℕ} (b w pos : ℕ) (cross same : State n) (ambient : Fin 159 → List Bool)
    (hc : Native b w cross ambient)
    (h35 : ambient 35=oldWords w (canonical same))
    (fresh : ∀ i : Fin 159,39 ≤ i.val → ambient i=[])
    (hfit : ∀ i,cross.positive i+same.positive i<2^w ∧ cross.negative i+same.negative i<2^w) :
    ∃ r,runFrom mergeProgram (CompetitorBankMergeDock.budget w n)
      (RecoveryCalls.restarted mergeProgram (heads pos) ambient)=some r ∧
      r.steps≤500000*(n+1)*(w+1)^2 ∧ r.final.heads=heads pos ∧
      Native b w (CompetitorBankMergeDock.stateAdd cross same) r.final.tapes ∧
      (∀ i : Fin 39,i≠19 → r.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)) ∧
      (∀ i : Fin 159,90 ≤ i.val → r.final.tapes i=[]) := by
  let native : Fin 35 → List Bool := fun i => ambient (i.castAdd 124)
  obtain ⟨base,hb,bs,bh,bc,b19,b35,bkeep⟩ := CompetitorBankMergeDock.context_run b w pos cross same native
    (by simpa [Native,native,Fin.castAdd] using hc) hfit
  have hi : ∀ i,ambient (mergeSlots i)=CompetitorBankMergeDock.input native (oldWords w (canonical same)) i := by
    intro i
    fin_cases i
    all_goals simp only [mergeSlots,CompetitorBankMergeDock.input,Fin.addCases,native]
    all_goals first | exact h35 | rfl | exact fresh _ (by decide)
  obtain ⟨actual,hr,hh,ht,hs⟩ := focus_run mergeSlots merge_injective _ _ _ (heads pos) ambient base hb bh
    (merge_heads pos) hi
  have localT (i : Fin 87) : actual.final.tapes (mergeSlots i)=base.final.tapes i := by
    rw [ht]
    exact install_slot mergeSlots merge_injective _ _ i
  refine ⟨actual,hr,hs.le.trans bs,hh,?_,?_,?_⟩
  · have he : (fun i : Fin 34 => actual.final.tapes (i.castAdd 125))=
        (fun i : Fin 34 => base.final.tapes (i.castAdd 53)) := by
      funext i
      have hs : mergeSlots (i.castAdd 53)=i.castAdd 125 := by
        apply Fin.ext
        simp [mergeSlots,show i.val<36 by omega]
      rw [← hs]
      exact localT _
    unfold Native
    rw [he]
    exact bc
  · intro i h19
    by_cases hi : i.val<35
    · let j : Fin 35 := ⟨i.val,hi⟩
      have hj : j≠19 := fun h => h19 (Fin.ext (congrArg (fun z : Fin 35 => z.val) h))
      have hs : mergeSlots (j.castAdd 52)=i.castAdd 120 := by
        apply Fin.ext
        simp [mergeSlots,j,show i.val<36 by omega]
      have hx := (localT _).trans (bkeep j hj)
      rw [hs] at hx
      exact hx
    · by_cases h35' : i=35
      · subst i
        exact (localT 35).trans (b35.trans h35.symm)
      · have hv : 36 ≤ i.val ∧ i.val<39 := by have := i.isLt; constructor <;> omega
        rw [ht]
        apply install_other
        intro j hj
        have hjv := congrArg Fin.val hj
        simp only [mergeSlots] at hjv
        split at hjv <;> simp only [Fin.val_castAdd] at hjv <;> omega
  · intro i hi
    rw [ht]
    apply (install_other mergeSlots ambient base.final.tapes i ?_).trans (fresh i (by omega))
    intro j hj
    have hv := congrArg Fin.val hj
    simp only [mergeSlots] at hv
    split at hv <;> dsimp only at hv <;> have := j.isLt <;> omega

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
