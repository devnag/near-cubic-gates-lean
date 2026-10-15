import Proof.CaseAnalysis.RowsEstimatorPaidInput

/-! Execute the actual allocated-and-cleaned driver at its shared consumer ports. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem at_fresh (a : WilliamsAlgorithm) (p : Program) (i : Fin 3) :
    slots a p (ScannedClean.fresh a i)=(ScannedClean.fresh a i).natAdd (WarmPrepare.tapes p) := by
  have hs : 70 ≤ ScannedDriver.tapes a:=by unfold ScannedDriver.tapes;omega
  have h70 : ¬(ScannedClean.fresh a i).val<70:=by
    simp only [ScannedClean.fresh,Fin.val_natAdd]
    omega
  have hd : ScannedClean.fresh a i≠ScannedClean.driver a:=by
    intro he
    have hv:=congrArg (fun z : Fin (ScannedClean.tapes a)=>z.val) he
    have hb:=(ScannedDriver.driver a).isLt
    simp only [ScannedClean.fresh,ScannedClean.driver,ScannedClean.old,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp only [slots,h70,hd,dite_false,ite_false]

theorem public_same (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (i : Fin (WarmPrepare.tapes p))
    (hi : i≠WarmPrepare.driver p) : publicInput p row C D fields out i=publicInput p row C 0 fields out i := by
  have h:=live_D p (WarmFields.bare p row C) D 0 fields out
  change Function.update (publicInput p row C 0 fields out) (WarmPrepare.driver p) (List.replicate D true)=
    publicInput p row C D fields out at h
  rw [←h,Function.update_of_ne hi]

theorem driver_generic {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C D fuel : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) (worker : Machine (ScannedClean.tapes a) s)
    (localOut : Fin (ScannedClean.tapes a) → List Bool)
    (source : ClockJoin.ReadyRun worker fuel (ScannedClean.input a row C) localOut)
    (oldWords : ∀ i : Fin 70,localOut (ScannedClean.old a (i.castAdd (DriverLayout.tapes a)))=Scanned.output row C i)
    (dword : localOut (ScannedClean.driver a)=List.replicate D true)
    (dcopy : localOut (ScannedClean.fresh a 1)=List.replicate D true) : ∃ extra r,
    runFrom (RecoveryFocus.machine (slots a p) worker) fuel
      ⟨worker.start,heads a p out,input a p row C fields out⟩=some r ∧
      r.final.heads=heads a p out ∧
      r.final.tapes=Fin.addCases (publicInput p row C D fields out) extra ∧ r.steps ≤ fuel ∧
      extra (ScannedClean.fresh a 1)=List.replicate D true := by
  classical
  obtain ⟨base,hb,bt,bh,bs⟩:=source
  obtain ⟨r,hr,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock (slots a p) (injective a p) worker fuel
    (heads a p out) (input a p row C fields out) (initialConfiguration worker (ScannedClean.input a row C))
    (slot_heads a p out) (projected a p row C fields out) base hb
  have pub (i : Fin (WarmPrepare.tapes p)) :
      r.final.tapes (old a p i)=publicInput p row C D fields out i := by
    by_cases hd : i=WarmPrepare.driver p
    · subst i
      rw [←at_driver,rt,bt,dword,public_driver]
    · rw [public_same p row C D fields out i hd]
      by_cases h70 : i.val<70
      · let j : Fin 70:=⟨i.val,h70⟩
        have he : i=WarmPrepare.old p (j.castAdd (CloseoutRowsRawRecord.tapes p)):=Fin.ext rfl
        rw [he,←at_old,rt,bt,oldWords,public_old]
      · rw [(keep _ (avoids_old a p i (by omega) hd)).2]
        simp only [input,old,Fin.addCases_left]
  let extra:=fun i : Fin (ScannedClean.tapes a)=>r.final.tapes (i.natAdd (WarmPrepare.tapes p))
  refine ⟨extra,r,hr,?_,?_,rs.le.trans bs,?_⟩
  · funext i
    by_cases hit : ∃ j,slots a p j=i
    · obtain ⟨j,rfl⟩:=hit
      rw [rh,bh,slot_heads]
    · exact (keep i (by simpa using hit)).1
  · funext i
    refine Fin.addCases (m:=WarmPrepare.tapes p) (n:=ScannedClean.tapes a) (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.addCases_left,old] using pub j
    · simp only [Fin.addCases_right,extra]
  · change r.final.tapes ((ScannedClean.fresh a 1).natAdd (WarmPrepare.tapes p))=_
    rw [←at_fresh,rt,bt,dcopy]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
