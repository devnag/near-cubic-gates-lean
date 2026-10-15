import Proof.Hierarchy.CompetitorFinalTableMerge

/-! The actual residue machine writes either the common even output141
or the odd temporary99. Both consume the full merged signed P/N bank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneTable
open CompetitorPlaneStream (oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def residueOutput (odd : Bool) : Fin 159 := if odd then 99 else 141

theorem residue_run {n : ℕ} (b w q pos : ℕ) (odd : Bool) (state : State n) (ambient : Fin 159 → List Bool)
    (hc : Native b w state ambient) (hq : q≤w) (h36 : ambient 36=List.replicate q true)
    (fresh : ∀ i : Fin 159,90 ≤ i.val → ambient i=[])
    (hfit : ∀ i,state.positive i<2^w ∧ state.negative i<2^w) :
    ∃ r,runFrom (residueProgram odd) (CompetitorResidueTableDock.budget w q n)
      (RecoveryCalls.restarted (residueProgram odd) (heads pos) ambient)=some r ∧
      r.steps≤121000*(n+1)*(w+1)^2 ∧ r.final.heads=heads pos ∧
      r.final.tapes (residueOutput odd)=CompetitorResidueTable.residueWords w q (canonical state) ∧
      (∀ i : Fin 39,r.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)) ∧
      (∀ i : Fin 159,140 ≤ i.val → i≠residueOutput odd → r.final.tapes i=[]) := by
  let native : Fin 35 → List Bool := fun i => ambient (i.castAdd 124)
  let d := CompetitorPlanePacketPass.capacity w n
  have hv : ∀ a∈canonical state,CompetitorResidueTable.Valid w a := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hfit i
  have hlen : (canonical state).length=n := by simp [canonical]
  obtain ⟨base,hb,bs,bh,b45,b35,b36,bkeep⟩ := CompetitorResidueTableDock.dock_run d w q pos (canonical state)
    (List.replicate (d-(oldWords w (canonical state)).length) false) native
    (by simpa [Native,native,Fin.castAdd,hlen,d] using hc.width)
    (by simpa [Native,native,Fin.castAdd,hlen,d] using hc.count)
    (by simpa [Native,native,Fin.castAdd,hlen,d,ZeroPadding.pad] using hc.old) hq hv
  rw [hlen] at hb bs
  have hi : ∀ i,ambient (residueSlots odd i)=CompetitorResidueTableDock.input native q i := by
    intro i
    cases odd <;> fin_cases i
    all_goals simp only [residueSlots,CompetitorResidueTableDock.input,Fin.addCases,native]
    all_goals first | exact h36 | rfl | exact fresh _ (by decide)
  obtain ⟨actual,hr,hh,ht,hs⟩ := focus_run (residueSlots odd) (residue_injective odd) _ _ _ (heads pos) ambient base hb bh
    (residue_heads pos odd) hi
  have localT (i : Fin 86) : actual.final.tapes (residueSlots odd i)=base.final.tapes i := by
    rw [ht]
    exact install_slot (residueSlots odd) (residue_injective odd) _ _ i
  refine ⟨actual,hr,hs.le.trans (bs.trans (CompetitorResidueTableDock.budget_bound w q n hq)),hh,?_,?_,?_⟩
  · have he : residueSlots odd 45=residueOutput odd := by cases odd <;> rfl
    rw [← he]
    exact (localT 45).trans b45
  · intro i
    by_cases hi : i.val<35
    · let j : Fin 35 := ⟨i.val,hi⟩
      have he : residueSlots odd (j.castAdd 51)=i.castAdd 120 := by
        apply Fin.ext
        simp [residueSlots,j,hi]
      have hx := (localT _).trans (bkeep j)
      rw [he] at hx
      exact hx
    · by_cases h36' : i=36
      · subst i
        have he : residueSlots odd 35=36 := by cases odd <;> rfl
        have hx := (localT 35).trans (b35.trans h36.symm)
        rw [he] at hx
        exact hx
      · rw [ht]
        apply install_other
        exact (show ∀ odd : Bool,∀ i : Fin 39,35 ≤ i.val → i≠36 → ∀ j,residueSlots odd j≠i.castAdd 120 by decide) odd i (by omega) h36'
  · intro i hi hout
    rw [ht]
    apply (install_other (residueSlots odd) ambient base.final.tapes i ?_).trans (fresh i (by omega))
    intro j hj
    have hmax : (residueSlots odd j).val<140 ∨ residueSlots odd j=residueOutput odd :=
      (show ∀ odd : Bool,∀ j,(residueSlots odd j).val<140 ∨ residueSlots odd j=residueOutput odd by decide) odd j
    rcases hmax with hlt|he
    · rw [hj] at hlt; omega
    · exact hout (hj.symm.trans he)

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
