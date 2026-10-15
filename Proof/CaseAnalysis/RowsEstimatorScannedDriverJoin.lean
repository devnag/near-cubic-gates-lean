import Proof.CaseAnalysis.RowsEstimatorScannedDriver

/-! The actual native append cursor reaches the paid driver in one run.
Only the original mandatory scanner precedes unary driver production. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (N : ℕ) := TapeEmbedding.machine N Scanned.machine
noncomputable def core {N s : ℕ} (worker : Machine (70+N) s) := Composition.machine (first N) worker
noncomputable def coldEntry {N s : ℕ} (_worker : Machine (70+N) s) (row : EquationRow.Input) (C : ℕ) :=
  Composition.leftConfig s (TapeEmbedding.config (fun _ : Fin N => 0) (fun _ : Fin N => []) (Scanned.entry row C))

theorem join {N s : ℕ} (worker : Machine (70+N) s) (row : EquationRow.Input) (C fuel : ℕ)
    (out : Fin (70+N) → List Bool) (hC : (Header.stream row).length ≤ C)
    (hc : ClockJoin.ReadyRun worker fuel (Fin.addCases (Scanned.output row C) (fun _ : Fin N => [])) out) :
    ∃ r,runFrom (core worker) (Scanned.budget row C+1+fuel) (coldEntry worker row C)=some r ∧
      r.final.tapes=out ∧ (∀ i,r.final.heads i=0) ∧ r.steps ≤ Scanned.budget row C+1+fuel := by
  obtain ⟨source,hs,st,sh,ss⟩ := Scanned.run row C hC
  let before := TapeEmbedding.receipt (fun _ : Fin N => 0) (fun _ : Fin N => []) source
  have hb := TapeEmbedding.run_embed Scanned.machine (fun _ : Fin N => 0) (fun _ : Fin N => []) _ _ source hs
  obtain ⟨after,ha,atapes,aheads,asteps⟩ := hc
  have hi : initialConfiguration worker (Fin.addCases (Scanned.output row C) (fun _ : Fin N => []))=
      Composition.restart before.final worker.start := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=70) (n:=N) (fun j => ?_) (fun j => ?_) i
      · simp [before,TapeEmbedding.receipt,TapeEmbedding.config,initialConfiguration,Composition.restart,sh]
      · simp [before,TapeEmbedding.receipt,TapeEmbedding.config,initialConfiguration,Composition.restart]
    · funext i
      refine Fin.addCases (m:=70) (n:=N) (fun j => ?_) (fun j => ?_) i
      · simpa only [before,TapeEmbedding.receipt,TapeEmbedding.config,initialConfiguration,Composition.restart,Fin.addCases_left] using (congrFun st j).symm
      · simp [before,TapeEmbedding.receipt,TapeEmbedding.config,initialConfiguration,Composition.restart]
  change runFrom worker fuel (initialConfiguration worker _)=some after at ha
  rw [hi] at ha
  have h := Composition.run_join (first N) worker _ _ _ before after hb ha
  refine ⟨Composition.joinedReceipt before after,h,atapes,aheads,?_⟩
  change source.steps+1+after.steps ≤ _
  omega

noncomputable def coldMachine (a : WilliamsAlgorithm) := core (machine a)
noncomputable def coldBudget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) :=
  Scanned.budget row C+1+DriverLayout.budget a row.d row.p row.cuts.length C

theorem cold_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (hC : (Header.stream row).length ≤ C) : ∃ r,
    runFrom (coldMachine a) (coldBudget a row C) (coldEntry (machine a) row C)=some r ∧
      (∀ i : Fin 70,r.final.tapes (i.castAdd (DriverLayout.tapes a))=Scanned.output row C i) ∧
      r.final.tapes (driver a)=List.replicate (Driver.value a row.d row.p row.cuts.length C) true ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ coldBudget a row C := by
  obtain ⟨out,hr,hkeep,hd⟩ := ready a row C
  obtain ⟨r,run,rt,rh,rs⟩ := join (machine a) row C _ out hC hr
  exact ⟨r,run,fun i => (congrFun rt _).trans (hkeep i),(congrFun rt _).trans hd,rh,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
