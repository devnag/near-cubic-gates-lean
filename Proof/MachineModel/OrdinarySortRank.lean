import Proof.MachineModel.OrdinaryRankMeaning
import Proof.MachineModel.OrdinaryDominanceRanks

/-! The actual ordinary sorter followed by the actual rank scan. A paid
reset exposes the sorted stream at head zero; four fresh rank-scan tapes
run beside all retained sorter storage. -/
namespace NearCubicWires.RepairOrdinary.SortRank
open LocalBitMultitape StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Request where
  width : ℕ
  records : List Record
  uniform : ∀ r ∈ records, (word r).length = width
  fits : records.length < 2 ^ width

def Request.sortRequest (req : Request) : SortCarrier.Request :=
  DominanceSort.fixedRequest req.records req.width req.uniform
noncomputable def Request.sortedWords (req : Request) : List (List Bool) :=
  (SortCarrier.sorted req.sortRequest).map word

theorem stream_words (rs : List Record) : RankLoop.stream (rs.map word) = stream rs := by
  unfold RankLoop.stream stream recordsBits
  rw [List.flatMap_map]
  rfl

theorem sorted_length (req : Request) : req.sortedWords.length = req.records.length := by
  simpa [Request.sortedWords, Request.sortRequest, DominanceSort.fixedRequest] using
    (SortCarrier.sorted_perm req.sortRequest).length_eq

theorem sorted_uniform (req : Request) : ∀ w ∈ req.sortedWords, w.length = req.width := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  exact req.uniform r ((SortCarrier.sorted_perm req.sortRequest).mem_iff.mp hr)

def rankLayout : Fin 11 ≃ Fin 11 where
  toFun := ![0, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6]
  invFun := ![0, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] theorem layout_inverse : (rankLayout.symm : Fin 11 → Fin 11) = ![0, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4] := rfl

def sortMachine : Machine 11 88 := TapeEmbedding.machine 4 (Rewind.machine SortCarrier.machine)
def rankMachine : Machine 11 20 := TapeRenaming.machine rankLayout (TapeEmbedding.machine 6 RankLoop.machine)
def machine : Machine 11 108 := Composition.machine sortMachine rankMachine
def rawBudget (req : Request) : ℕ :=
  2 * SortCarrier.budget req.records + 3 + (req.records.length * (7 * req.width + 14) + 1)

theorem raw_run (req : Request) :
    ∃ r : ExecutionReceipt 11 108,
      run machine (rawBudget req) (SourceHandoff.sourceTapes (stream req.records)) = some r ∧
      r.final.tapes 7 = RankLoop.labels req.width 0 req.sortedWords ++ [false] ∧
      r.steps ≤ rawBudget req := by
  obtain ⟨source, _, _, hsource, hout, hsteps, _⟩ :=
    Classical.choose_spec (SortCarrier.raw_sort req.sortRequest.records req.sortRequest.uniform)
  have hsource' : run SortCarrier.machine (SortCarrier.budget req.records)
      (SourceHandoff.sourceTapes (stream req.records)) = some source := hsource
  have hout' : source.final.tapes 0 = RankLoop.stream req.sortedWords := by
    rw [Request.sortedWords, stream_words]
    exact hout
  obtain ⟨reset, hreset, hresetOut, hresetHeads, hresetSteps, _⟩ :=
    Rewind.reset_run SortCarrier.machine (SortCarrier.budget req.records) _ source hsource'
  have hresetInput : initialConfiguration (Rewind.machine SortCarrier.machine)
      (Fin.addCases (SourceHandoff.sourceTapes (stream req.records)) (fun _ : Fin 1 => [])) =
      initialConfiguration (Rewind.machine SortCarrier.machine)
        (SourceHandoff.sourceTapes (stream req.records)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [initialConfiguration, SourceHandoff.sourceTapes, Fin.addCases]
  have hs0 : runFrom (Rewind.machine SortCarrier.machine) (2 * source.steps + 2)
      (initialConfiguration (Rewind.machine SortCarrier.machine)
        (SourceHandoff.sourceTapes (stream req.records))) = some reset := by
    rw [← hresetInput]
    exact hreset
  have hfirst := TapeEmbedding.run_embed (Rewind.machine SortCarrier.machine) (fun _ : Fin 4 => 0)
    (fun _ : Fin 4 => []) _ _ reset hs0
  let first := TapeEmbedding.receipt (fun _ : Fin 4 => 0) (fun _ : Fin 4 => []) reset
  have hfirstInput : TapeEmbedding.config (fun _ : Fin 4 => 0) (fun _ : Fin 4 => [])
      (initialConfiguration (Rewind.machine SortCarrier.machine) (SourceHandoff.sourceTapes (stream req.records))) =
      initialConfiguration sortMachine (SourceHandoff.sourceTapes (stream req.records)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, SourceHandoff.sourceTapes, Fin.addCases]
  rw [hfirstInput] at hfirst
  obtain ⟨ranked, hranked, hrankedOut, hrankedSteps, _⟩ :=
    RankCarrier.raw_run req.width req.sortedWords (sorted_uniform req) (by rw [sorted_length]; exact req.fits)
  let extra : Fin 6 → List Bool := fun i => reset.final.tapes i.succ
  have he := TapeEmbedding.run_embed RankLoop.machine (fun _ : Fin 6 => 0) extra _ _ ranked hranked
  have hsecond := TapeRenaming.run_rename rankLayout (TapeEmbedding.machine 6 RankLoop.machine) _ _ _ he
  let second := TapeRenaming.receipt rankLayout (TapeEmbedding.receipt (fun _ : Fin 6 => 0) extra ranked)
  have hmid : Composition.restart first.final rankMachine.start =
      TapeRenaming.config rankLayout (TapeEmbedding.config (fun _ : Fin 6 => 0) extra
        (initialConfiguration RankLoop.machine (SourceHandoff.sourceTapes (RankLoop.stream req.sortedWords)))) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, initialConfiguration, Fin.addCases, hresetHeads]
    · have hzero := (hresetOut (0 : Fin 6)).trans hout'
      change reset.final.tapes 0 = RankLoop.stream req.sortedWords at hzero
      funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, initialConfiguration, SourceHandoff.sourceTapes, Fin.addCases, extra, hzero]
  have hnext : runFrom rankMachine (req.sortedWords.length * (7 * req.width + 14) + 1)
      (Composition.restart first.final rankMachine.start) = some second := by
    rw [hmid]
    exact hsecond
  have hj := Composition.run_join sortMachine rankMachine (2 * source.steps + 2)
    (req.sortedWords.length * (7 * req.width + 14) + 1)
    (initialConfiguration sortMachine (SourceHandoff.sourceTapes (stream req.records))) first second hfirst hnext
  have hcount := sorted_length req
  have hbound : (2 * source.steps + 2) + 1 + (req.sortedWords.length * (7 * req.width + 14) + 1) ≤ rawBudget req := by
    change source.steps ≤ SortCarrier.budget req.records at hsteps
    unfold rawBudget
    rw [hcount]
    omega
  have hmore := runFrom_moreFuel machine
    ((2 * source.steps + 2) + 1 + (req.sortedWords.length * (7 * req.width + 14) + 1))
    (rawBudget req - ((2 * source.steps + 2) + 1 + (req.sortedWords.length * (7 * req.width + 14) + 1)))
    _ _ hj
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨Composition.joinedReceipt first second, hmore, ?_, ?_⟩
  · simpa [Composition.joinedReceipt, Composition.rightConfig, second, TapeRenaming.receipt,
      TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, Fin.addCases] using hrankedOut
  · change reset.steps + 1 + ranked.steps ≤ rawBudget req
    rw [hresetSteps]
    omega

noncomputable def carrier : WordFunction Request (fun req => stream req.records)
    (fun req => RankLoop.labels req.width 0 req.sortedWords ++ [false])
    (fun req => 4 * (stream req.records).length + 3 + rawBudget req) :=
  FramedSource.ofRaw (Request := Request) (t := 11) (s := 108) (by decide) machine (7 : Fin 11)
    (fun req => stream req.records) (fun req => RankLoop.labels req.width 0 req.sortedWords ++ [false]) rawBudget (by
      intro req
      obtain ⟨r, hr, ho, _⟩ := raw_run req
      exact ⟨r, hr, ho⟩)

end NearCubicWires.RepairOrdinary.SortRank
