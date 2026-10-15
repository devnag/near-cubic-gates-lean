import Proof.CaseAnalysis.RowsEstimatorScannedCleanPorts

/-! Symbolic finite-control join of the actual driver and cleanup donors.
Keeping callee controls abstract prevents unfolding thousands of fixed passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def project (a : WilliamsAlgorithm) (i : Fin (count a)) : Fin (ScannedDriver.tapes a) :=
  ⟨(work a i).val,(work_bounds a i).2.1⟩
theorem work_old (a : WilliamsAlgorithm) (i : Fin (count a)) : old a (project a i)=work a i := Fin.ext rfl
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) : Fin (tapes a) → List Bool :=
  Fin.addCases (ScannedDriver.input a row C) (fun _ : Fin 3=>[])
noncomputable def cleanBudget (a : WilliamsAlgorithm) (D : ℕ) :=
  2*D+6+1+(DriverLayout.sweepCount a*(5*D+10)+1)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) :=
  DriverLayout.budget a row.d row.p row.cuts.length C+1+
    cleanBudget a (Driver.value a row.d row.p row.cuts.length C)

theorem join_generic {s₁ s₂ : ℕ} (a : WilliamsAlgorithm)
    (p : Machine (ScannedDriver.tapes a) s₁) (q : Machine (4+count a) s₂)
    (fp fq D K : ℕ) (A before : Fin (ScannedDriver.tapes a) → List Bool)
    (hb : ClockJoin.ReadyRun p fp A before)
    (hd : before (ScannedDriver.driver a)=List.replicate D true)
    (hc : ClockJoin.ReadyRun q fq (DriverCleanBank.input D (fun i=>before (project a i)))
      (DriverCleanBank.middle D (fun _ : Fin (count a)=>List.replicate (K*D) false))) : ∃ out,
    ClockJoin.ReadyRun (Composition.machine (ClockJoin.lifted (Equiv.refl (Fin (tapes a))) p)
      (RecoveryFocus.machine (slots a) q)) (fp+1+fq)
      (Fin.addCases A (fun _ : Fin 3=>[])) out ∧
      (∀ i : Fin 70,out (old a (i.castAdd (DriverLayout.tapes a)))=before (i.castAdd (DriverLayout.tapes a))) ∧
      out (driver a)=List.replicate D true ∧ out (fresh a 0)=[] ∧
      out (fresh a 1)=List.replicate D true ∧ out (fresh a 2)=List.replicate (D+2) false ∧
      (∀ i,out (work a i)=List.replicate (K*D) false) := by
  classical
  let data:=fun i : Fin (count a)=>before (project a i)
  let middle : Fin (tapes a) → List Bool:=Fin.addCases before (fun _ : Fin 3=>[])
  have firstRun : ClockJoin.ReadyRun (ClockJoin.lifted (Equiv.refl (Fin (tapes a))) p)
      fp (Fin.addCases A (fun _ : Fin 3=>[])) middle := by
    have h:=ClockJoin.lift (Equiv.refl (Fin (tapes a))) p fp A before (fun _ : Fin 3=>[]) hb
    exact h
  obtain ⟨base,hr,bt,bh,bs⟩:=hc
  obtain ⟨after,ha,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock (slots a) (injective a)
    q fq (fun _=>0) middle _
    (by intro i;rfl)
    (by
      intro i
      refine Fin.addCases (m:=4) (n:=count a) (fun j=>?_) (fun j=>?_) i
      · fin_cases j
        · simpa [slots,driver,old,fresh,middle,DriverCleanBank.input,initialConfiguration] using hd
        · simp [slots,driver,old,fresh,middle,DriverCleanBank.input,initialConfiguration]
        · simp [slots,driver,old,fresh,middle,DriverCleanBank.input,initialConfiguration]
        · simp [slots,driver,old,fresh,middle,DriverCleanBank.input,initialConfiguration]
      · simp only [slots,Fin.addCases_right]
        rw [← work_old]
        simp [middle,old,DriverCleanBank.input,initialConfiguration]) base hr
  have lastRun : ClockJoin.ReadyRun (RecoveryFocus.machine (slots a) q) fq middle after.final.tapes := by
    refine ⟨after,ha,rfl,?_,rs.trans_le bs⟩
    intro i
    by_cases hit : ∃ j,slots a j=i
    · obtain ⟨j,rfl⟩:=hit
      exact (rh j).trans (bh j)
    · exact (keep i (by simpa using hit)).1
  refine ⟨after.final.tapes,ClockJoin.join _ _ _ _ _ _ _ firstRun lastRun,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [(keep _ (avoids_old a i)).2]
    simp [middle,old]
  · simpa [slots,bt,DriverCleanBank.middle] using rt ((0 : Fin 4).castAdd (count a))
  · simpa [slots,bt,DriverCleanBank.middle] using rt ((1 : Fin 4).castAdd (count a))
  · simpa [slots,bt,DriverCleanBank.middle] using rt ((2 : Fin 4).castAdd (count a))
  · simpa [slots,bt,DriverCleanBank.middle] using rt ((3 : Fin 4).castAdd (count a))
  · intro i
    simpa [slots,bt,DriverCleanBank.middle] using rt (i.natAdd 4)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
