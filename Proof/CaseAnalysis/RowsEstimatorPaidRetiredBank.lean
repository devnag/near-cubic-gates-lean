import Proof.CaseAnalysis.RowsEstimatorPaidDriverFalse

/-! Project the actual two-word retirement onto retained and reusable bank ports. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retiredBank (a : WilliamsAlgorithm) (p : Program) (D : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool):=
  install (retireSlots a p) (Fin.addCases A extra) (fun _=>List.replicate D false)

theorem retired_public (a : WilliamsAlgorithm) (p : Program) (D : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool)
    (i : Fin (WarmPrepare.tapes p)) (hi : i≠WarmPrepare.driver p) :
    retiredBank a p D A extra (old a p i)=A i := by
  rw [retiredBank,install_other]
  · exact Fin.addCases_left i
  · intro j he
    have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
    fin_cases j
    · apply hi
      exact Fin.ext (by simpa [retireSlots,old] using hv.symm)
    · have h:=i.isLt
      simp [retireSlots,old] at hv
      omega

theorem retired_driver (a : WilliamsAlgorithm) (p : Program) (D : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool) :
    retiredBank a p D A extra (old a p (WarmPrepare.driver p))=List.replicate D false :=
  install_slot (retireSlots a p) (retire_injective a p) _ _ 0

theorem retired_private (a : WilliamsAlgorithm) (p : Program) (D : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool)
    (hextra : ∀ i,i≠ScannedClean.fresh a 1 → ∃ n,extra i=List.replicate n false)
    (i : Fin (ScannedClean.tapes a)) :
    ∃ n,retiredBank a p D A extra (i.natAdd (WarmPrepare.tapes p))=List.replicate n false := by
  by_cases hi : i=ScannedClean.fresh a 1
  · subst i
    exact ⟨D,install_slot (retireSlots a p) (retire_injective a p) _ _ 1⟩
  · obtain ⟨n,hn⟩:=hextra i hi
    refine ⟨n,?_⟩
    rw [retiredBank,install_other]
    · simpa only [Fin.addCases_right] using hn
    · intro j he
      have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
      fin_cases j
      · have h:=(WarmPrepare.driver p).isLt
        simp [retireSlots,old] at hv
        omega
      · apply hi
        apply Fin.ext
        simp [retireSlots] at hv
        omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
