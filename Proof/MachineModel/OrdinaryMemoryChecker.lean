import Proof.MachineModel.OrdinaryMemoryPrepared

/-! The entire actual chronological-memory checker: sort, paid reset,
generate the initial key, paid reset, and sequential validation. All scratch
starts blank, and all retained sorter/reset tapes remain present. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog MemorySort StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Request where
  count : ℕ
  indexBits : ℕ
  addressBits : ℕ
  events : Fin count → Event
  positive : 0 < count
  indicesFit : count ≤ 2^indexBits
  cellsFit : ∀ i, cellCode addressBits (events i).cell < 2^(indexBits+2)
  addressesFit : ∀ i, (events i).cell.2 < 2^addressBits
def Request.sortRequest (r : Request) : SortCarrier.Request :=
  request r.indexBits (r.indexBits+2) r.addressBits r.events
def Request.input (r : Request) : List Bool := stream r.sortRequest.records
def Request.result (r : Request) : Bool :=
  (MemoryLog.run (fun _ => false) ((List.finRange r.count).map r.events)).isSome
def layout : Fin 21 ≃ Fin 21 where
  toFun := ![7,8,9,10,11,12,13,0,14,15,16,17,18,19,20,1,2,3,4,5,6]
  invFun := ![7,15,16,17,18,19,20,0,1,2,3,4,5,6,8,9,10,11,12,13,14]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 21 → Fin 21) =
    ![7,15,16,17,18,19,20,0,1,2,3,4,5,6,8,9,10,11,12,13,14] := rfl
def sortMachine : Machine 21 88 := TapeEmbedding.machine 14 (Rewind.machine SortCarrier.machine)
def checkMachine : Machine 21 50 :=
  TapeRenaming.machine layout (TapeEmbedding.machine 6 MemoryPrepared.machine)
def machine : Machine 21 138 := Composition.machine sortMachine checkMachine
def checkBudget (req : Request) : ℕ :=
  8*(req.indexBits+2)+4+1+(req.count*(240*(req.indexBits+2)+182)+1)
def rawBudget (req : Request) : ℕ :=
  2*SortCarrier.budget req.sortRequest.records+3+checkBudget req

theorem raw_run (req : Request) :
    ∃ r : ExecutionReceipt 21 138,
      run machine (rawBudget req) (SourceHandoff.sourceTapes req.input) = some r ∧
      r.final.tapes 19 = [req.result] := by
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
  obtain ⟨checked, hchecked, hcheckedOut, _⟩ := MemoryPrepared.sorted_run
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
  refine ⟨Composition.joinedReceipt first second, hmore, ?_⟩
  simpa [Composition.joinedReceipt, Composition.rightConfig, second, TapeRenaming.receipt,
    TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, Fin.addCases,
    Request.result] using hcheckedOut

noncomputable def carrier : WordFunction Request Request.input (fun req => [req.result])
    (fun req => 4*req.input.length+3+rawBudget req) :=
  FramedSource.ofRaw (by decide) machine 19 Request.input (fun req => [req.result]) rawBudget raw_run

end NearCubicWires.RepairOrdinary.MemoryChecker
