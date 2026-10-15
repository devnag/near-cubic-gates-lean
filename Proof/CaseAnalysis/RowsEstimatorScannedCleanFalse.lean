import Proof.CaseAnalysis.RowsEstimatorScannedCleanRun

/-! Every private driver word except the retained D copy is already false. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem work_cover (a : WilliamsAlgorithm) (i : Fin (tapes a))
    (hlo : 70 ≤ i.val) (hhi : i.val<ScannedDriver.tapes a) (hd : i≠driver a) : ∃ j,work a j=i := by
  have hdi : i.val≠70+97+2*DriverLayout.e a := by
    intro he
    apply hd
    apply Fin.ext
    simpa only [driver,old,Fin.val_castAdd,ScannedDriver.driver_val,Nat.add_assoc] using he
  let j : Fin (count a):=⟨if i.val<70+97+2*DriverLayout.e a then i.val-70 else i.val-71,by
    dsimp [count,ScannedDriver.tapes,DriverLayout.tapes] at *
    split_ifs <;> omega⟩
  refine ⟨j,Fin.ext ?_⟩
  rw [work_val]
  dsimp [j]
  split_ifs <;> omega

theorem private_false (a : WilliamsAlgorithm) (D K : ℕ) (A : Fin (tapes a) → List Bool)
    (hzero : A (fresh a 0)=[]) (hlog : A (fresh a 2)=List.replicate (D+2) false)
    (hwork : ∀ i,A (work a i)=List.replicate (K*D) false)
    (i : Fin (tapes a)) (h70 : 70 ≤ i.val) (hd : i≠driver a) (hc : i≠fresh a 1) :
    ∃ n,A i=List.replicate n false := by
  by_cases hi : i.val<ScannedDriver.tapes a
  · obtain ⟨j,rfl⟩:=work_cover a i h70 hi hd
    exact ⟨K*D,hwork j⟩
  · have hib:=i.isLt
    have hcval : i.val≠ScannedDriver.tapes a+1:=by
      intro he
      apply hc
      exact Fin.ext (by simpa [fresh] using he)
    have hcases : i.val=ScannedDriver.tapes a ∨ i.val=ScannedDriver.tapes a+2 := by
      unfold tapes at hib
      omega
    rcases hcases with h | h
    · have he : i=fresh a 0:=Fin.ext (by simpa [fresh] using h)
      exact ⟨0,by rw [he,hzero,List.replicate_zero]⟩
    · have he : i=fresh a 2:=Fin.ext (by simpa [fresh] using h)
      exact ⟨D+2,by rw [he,hlog]⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
