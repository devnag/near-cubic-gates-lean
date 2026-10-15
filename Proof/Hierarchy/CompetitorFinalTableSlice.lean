import Proof.Hierarchy.CompetitorFinalTableResidue

/-! The accepted odd projection is physically docked to temporary99 and
retained Q36/U37. The common output141 is the only selected count result. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable
open CompetitorOddRowSlice
open SourceInterfaces WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem slice_run {u : ℕ} (q pos : ℕ) (f : Fin u → Fin u → ℕ) (he : u/2+u/2=u)
    (ambient : Fin 159 → List Bool)
    (h99 : ambient 99=(rowMajorNatMatrix f).flatMap (binary q))
    (h36 : ambient 36=List.replicate q true) (h37 : ambient 37=UnaryTemplate.tape u)
    (fresh : ∀ i : Fin 159,140 ≤ i.val → ambient i=[]) :
    ∃ r,runFrom sliceProgram (CompetitorOddRowSliceDock.budget u q)
      (RecoveryCalls.restarted sliceProgram (heads pos) ambient)=some r ∧
      r.steps≤256*(u*u+1)*(q+1) ∧ r.final.heads=heads pos ∧
      r.final.tapes 141=(rowMajorNatMatrix (fun i j => f i (firstColumn he j))).flatMap (binary q) ∧
      (∀ i : Fin 140,r.final.tapes (i.castAdd 19)=ambient (i.castAdd 19)) := by
  let native : Fin 86 → List Bool := fun i => ambient (residueSlots true i)
  obtain ⟨base,hb,bs,bh,b88,b86,bkeep⟩ := matrix_dock_run q pos f he [] native
    (by simpa [native,residueSlots] using h99) h36
  have hi : ∀ i,ambient (sliceSlots i)=CompetitorOddRowSliceDock.input native u i := by
    intro i
    fin_cases i
    all_goals simp only [sliceSlots,CompetitorOddRowSliceDock.input,Fin.addCases,native]
    all_goals first | exact h37 | rfl | exact fresh _ (by decide)
  obtain ⟨actual,hr,hh,ht,hs⟩ := focus_run sliceSlots slice_injective _ _ _ (heads pos) ambient base hb bh
    (slice_heads pos) hi
  have localT (i : Fin 106) : actual.final.tapes (sliceSlots i)=base.final.tapes i := by
    rw [ht]
    exact install_slot sliceSlots slice_injective _ _ i
  refine ⟨actual,hr,hs.le.trans bs,hh,(localT 88).trans b88,?_⟩
  intro i
  classical
  by_cases hex : ∃ j,sliceSlots j=i.castAdd 19
  · obtain ⟨j,hj⟩ := hex
    by_cases hj86 : j.val<86
    · let k : Fin 86 := ⟨j.val,hj86⟩
      have hcast : k.castAdd 20=j := by apply Fin.ext; rfl
      have heq : sliceSlots j=residueSlots true k := by simp [sliceSlots,hj86,k]
      have hk := (localT j).trans (by simpa only [hcast] using bkeep k)
      change actual.final.tapes (sliceSlots j)=ambient (residueSlots true k) at hk
      rw [← heq,hj] at hk
      exact hk
    · by_cases hj' : j=86
      · subst j
        have hk := (localT 86).trans (b86.trans h37.symm)
        change actual.final.tapes (sliceSlots 86)=ambient (sliceSlots 86) at hk
        rw [hj] at hk
        exact hk
      · have hv := congrArg Fin.val hj
        simp only [sliceSlots,dif_neg hj86,if_neg hj',Fin.val_castAdd] at hv
        have := i.isLt
        omega
  · rw [ht]
    exact install_other sliceSlots _ _ (i.castAdd 19) (by intro j h; exact hex ⟨j,h⟩)

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
