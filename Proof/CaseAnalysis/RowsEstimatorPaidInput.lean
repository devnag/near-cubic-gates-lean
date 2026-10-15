import Proof.CaseAnalysis.RowsEstimatorPaidFields

/-! Actual physical entry projections for the aliased driver call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def publicInput (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :=
  WarmPrepare.live p (WarmPrepare.data p (WarmFields.bare p row C) D 0 fields) out
noncomputable def input (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) : Fin (tapes a p) → List Bool :=
  Fin.addCases (publicInput p row C 0 fields out) (fun _ : Fin (ScannedClean.tapes a)=>[])
noncomputable def heads (a : WilliamsAlgorithm) (p : Program) (out : List Bool) : Fin (tapes a p) → ℕ :=
  Fin.addCases (WarmPrepare.heads p out) (fun _ : Fin (ScannedClean.tapes a)=>0)

theorem public_old (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (i : Fin 70) :
    publicInput p row C D fields out (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p)))=
      Scanned.output row C i := by
  unfold publicInput WarmPrepare.live
  rw [Function.update_of_ne (WarmPrepared.old_ne p _),WarmPrepare.at_old,bare_old]

theorem public_driver (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :
    publicInput p row C D fields out (WarmPrepare.driver p)=List.replicate D true := by
  unfold publicInput WarmPrepare.live
  rw [Function.update_of_ne (WarmPrepared.driver_ne p),WarmPrepare.at_driver]

theorem old_val (a : WilliamsAlgorithm) (p : Program) (i : Fin (WarmPrepare.tapes p)) :
    (old a p i).val=i.val := rfl

theorem projected (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (i : Fin (ScannedClean.tapes a)) :
    input a p row C fields out (slots a p i)=ScannedClean.input a row C i := by
  by_cases h70 : i.val<70
  · let j : Fin 70:=⟨i.val,h70⟩
    have he : i=ScannedClean.old a (j.castAdd (DriverLayout.tapes a)):=Fin.ext rfl
    rw [he,at_old,input_old]
    simp only [input,old,Fin.addCases_left,public_old]
  · rw [input_blank a row C i (by omega)]
    by_cases hd : i=ScannedClean.driver a
    · subst i
      rw [at_driver]
      simp only [input,old,Fin.addCases_left,public_driver,List.replicate_zero]
    · simp only [slots,h70,hd,dite_false,ite_false,input,Fin.addCases_right]

theorem slot_heads (a : WilliamsAlgorithm) (p : Program) (out : List Bool)
    (i : Fin (ScannedClean.tapes a)) : heads a p out (slots a p i)=0 := by
  by_cases h70 : i.val<70
  · let j : Fin 70:=⟨i.val,h70⟩
    have he : i=ScannedClean.old a (j.castAdd (DriverLayout.tapes a)):=Fin.ext rfl
    rw [he,at_old]
    simp only [heads,old,Fin.addCases_left,WarmPrepare.heads,WarmPrepared.old_ne,ite_false]
  · by_cases hd : i=ScannedClean.driver a
    · subst i
      rw [at_driver]
      simp only [heads,old,Fin.addCases_left,WarmPrepare.heads,WarmPrepared.driver_ne,ite_false]
    · simp only [slots,h70,hd,dite_false,ite_false,heads,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
