import Proof.MachineModel.OrdinaryMemoryChecker

/-! Preserve the existing raw checker's physical result-head endpoint.
The same sort/reset/prepare/check composition already supplies it through
MemoryPrepared.sorted_run; this theorem retains that lower-level conclusion. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog MemorySort StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_run_endpoint (req : Request) :
    ∃ r : ExecutionReceipt 21 138,
      run machine (rawBudget req) (SourceHandoff.sourceTapes req.input) = some r ∧
      r.final.tapes 19 = [req.result] ∧ r.final.heads 19 = 0 := by
  obtain ⟨source, _, _, hsource, hout, hsteps, _⟩ :=
    Classical.choose_spec (SortCarrier.raw_sort req.sortRequest.records req.sortRequest.uniform)
  obtain ⟨reset, hreset, hresetOut, hresetHeads, _, _⟩ :=
    Rewind.reset_run SortCarrier.machine (SortCarrier.budget req.sortRequest.records) _ source hsource
  have hresetInput : initialConfiguration (Rewind.machine SortCarrier.machine)
      (Fin.addCases (SourceHandoff.sourceTapes req.input) (fun _ : Fin 1 => [])) =
      initialConfiguration (Rewind.machine SortCarrier.machine) (SourceHandoff.sourceTapes req.input) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [initialConfiguration, SourceHandoff.sourceTapes, Fin.addCases]
  have hs0 : runFrom (Rewind.machine SortCarrier.machine) (2*source.steps+2)
      (initialConfiguration (Rewind.machine SortCarrier.machine) (SourceHandoff.sourceTapes req.input)) =
        some reset := by
    rw [← hresetInput]
    exact hreset
  have hfirst := TapeEmbedding.run_embed (Rewind.machine SortCarrier.machine)
    (fun _ : Fin 14 => 0) (fun _ : Fin 14 => []) _ _ reset hs0
  let first := TapeEmbedding.receipt (fun _ : Fin 14 => 0) (fun _ : Fin 14 => []) reset
  have hfirstInput : TapeEmbedding.config (fun _ : Fin 14 => 0) (fun _ : Fin 14 => [])
      (initialConfiguration (Rewind.machine SortCarrier.machine) (SourceHandoff.sourceTapes req.input)) =
      initialConfiguration sortMachine (SourceHandoff.sourceTapes req.input) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration,
        SourceHandoff.sourceTapes, Fin.addCases]
  rw [hfirstInput] at hfirst
  obtain ⟨checked, hchecked, hcheckedOut, hcheckedHeads⟩ := MemoryPrepared.sorted_run
    req.indexBits req.addressBits req.events req.positive req.indicesFit req.cellsFit req.addressesFit
  let extra : Fin 6 → List Bool := fun i => reset.final.tapes i.succ
  have he := TapeEmbedding.run_embed MemoryPrepared.machine (fun _ : Fin 6 => 0) extra _ _ checked hchecked
  have hsecond := TapeRenaming.run_rename layout (TapeEmbedding.machine 6 MemoryPrepared.machine) _ _ _ he
  let second := TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 6 => 0) extra checked)
  have hmid : Composition.restart first.final checkMachine.start =
      TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 6 => 0) extra
        (initialConfiguration MemoryPrepared.machine
          (MemoryPrepared.sourceInput (stream (SortCarrier.sorted req.sortRequest))))) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, initialConfiguration, Fin.addCases, hresetHeads]
    · have hzero := (hresetOut (0 : Fin 6)).trans hout
      change reset.final.tapes 0 = stream (SortCarrier.sorted req.sortRequest) at hzero
      funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, initialConfiguration, MemoryPrepared.sourceInput, Fin.addCases, extra, hzero]
  have hnext : runFrom checkMachine (checkBudget req)
      (Composition.restart first.final checkMachine.start) = some second := by
    rw [hmid]
    exact hsecond
  have hj := Composition.run_join sortMachine checkMachine (2*source.steps+2) (checkBudget req)
    (initialConfiguration sortMachine (SourceHandoff.sourceTapes req.input)) first second hfirst hnext
  have hbound : (2*source.steps+2)+1+checkBudget req ≤ rawBudget req := by
    unfold rawBudget
    omega
  have hmore := runFrom_moreFuel machine ((2*source.steps+2)+1+checkBudget req)
    (rawBudget req-((2*source.steps+2)+1+checkBudget req)) _ _ hj
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨Composition.joinedReceipt first second, hmore, ?_, ?_⟩
  · simpa [Composition.joinedReceipt, Composition.rightConfig, second, TapeRenaming.receipt,
      TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, Fin.addCases,
      Request.result] using hcheckedOut

  · simpa [Composition.joinedReceipt, Composition.rightConfig, second, TapeRenaming.receipt,
      TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, Fin.addCases] using hcheckedHeads

end NearCubicWires.RepairOrdinary.MemoryChecker
