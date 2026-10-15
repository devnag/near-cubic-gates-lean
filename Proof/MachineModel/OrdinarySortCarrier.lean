import Proof.MachineModel.OrdinarySortPreparation
import Proof.Foundations.OrdinaryFramedSource

/-! Complete ordinary sorting function. The program receives only the framed
record stream. Width extraction, unary header, head reset, two radix cycles,
output location and retained intermediate storage are all part of its run. -/
namespace NearCubicWires.RepairOrdinary.SortCarrier
open LocalBitMultitape StablePartition RadixSemantics SortPreparation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 6 86 :=
  Composition.machine SortPreparation.machine (TapeEmbedding.machine 1 RadixIteration.machine)

def budget (rs : List Record) : ℕ :=
  6 * width rs + 6 + 2 * width rs * (10 * (stream rs).length + 12)

theorem raw_sort (rs : List Record) (hw : ∀ r ∈ rs, (word r).length = width rs) :
    ∃ sorted : List Record, ∃ r : ExecutionReceipt 6 86,
      sorted.Perm rs ∧ sorted.Pairwise (fun a b => value (word a) ≤ value (word b)) ∧
      run machine (budget rs) (SourceHandoff.sourceTapes (stream rs)) = some r ∧
      r.final.tapes 0 = stream sorted ∧ r.steps ≤ budget rs ∧
      r.peakTapeCells ≤ 8 * (stream rs).length + 5 * width rs + 3 := by
  obtain ⟨pre, hp, ht, hh, hsteps, hpeak⟩ := prepare_run rs
  obtain ⟨sorted, raw, hperm, hsorted, hr, hout, _, hs, hb⟩ := RadixEven.sort_run rs (width rs) hw
  let extra := fun _ : Fin 1 => List.replicate (3 * width rs + 1) false
  let heads := fun _ : Fin 1 => 0
  have he := TapeEmbedding.run_embed RadixIteration.machine heads extra
    (2 * width rs * (10 * (stream rs).length + 12) + 1) _ raw hr
  have hmid : Composition.restart pre.final (TapeEmbedding.machine 1 RadixIteration.machine).start =
      TapeEmbedding.config heads extra (initialConfiguration RadixIteration.machine
        (RadixEven.input rs (width rs))) := by
    apply configuration_ext
    · rfl
    · funext i
      change pre.final.heads i = _
      rw [hh]
      fin_cases i <;> simp [TapeEmbedding.config, heads, initialConfiguration, Fin.addCases]
    · exact ht
  have hnext : runFrom (TapeEmbedding.machine 1 RadixIteration.machine)
      (2 * width rs * (10 * (stream rs).length + 12) + 1)
      (Composition.restart pre.final (TapeEmbedding.machine 1 RadixIteration.machine).start) =
      some (TapeEmbedding.receipt heads extra raw) := by
    rw [hmid]
    exact he
  have hj := Composition.run_join SortPreparation.machine (TapeEmbedding.machine 1 RadixIteration.machine)
    (6 * width rs + 4) (2 * width rs * (10 * (stream rs).length + 12) + 1)
    (initialConfiguration SortPreparation.machine (SourceHandoff.sourceTapes (stream rs)))
    pre (TapeEmbedding.receipt heads extra raw) hp hnext
  have hinit : initialConfiguration machine (SourceHandoff.sourceTapes (stream rs)) =
      Composition.leftConfig 80
        (initialConfiguration SortPreparation.machine (SourceHandoff.sourceTapes (stream rs))) := rfl
  have hbudget : (6 * width rs + 4) + 1 + (2 * width rs * (10 * (stream rs).length + 12) + 1) =
      budget rs := by unfold budget; omega
  refine ⟨sorted, Composition.joinedReceipt pre (TapeEmbedding.receipt heads extra raw),
    hperm, hsorted, ?_, ?_, ?_, ?_⟩
  · change runFrom machine _ _ = _
    rw [hinit, ← hbudget]
    exact hj
  · simpa [Composition.joinedReceipt, Composition.rightConfig, TapeEmbedding.receipt,
      TapeEmbedding.config, Fin.addCases] using hout
  · change pre.steps + 1 + raw.steps ≤ budget rs
    unfold budget
    omega
  · change max pre.peakTapeCells (raw.peakTapeCells + TapeEmbedding.extraCells extra) ≤ _
    simp only [TapeEmbedding.extraCells, extra, Fin.sum_univ_one, List.length_replicate]
    omega

structure Request where
  records : List Record
  uniform : ∀ r ∈ records, (word r).length = width records

noncomputable def sorted (request : Request) : List Record :=
  Classical.choose (raw_sort request.records request.uniform)

theorem sorted_perm (request : Request) : (sorted request).Perm request.records := by
  obtain ⟨r, hp, _⟩ := Classical.choose_spec (raw_sort request.records request.uniform)
  exact hp

theorem sorted_order (request : Request) :
    (sorted request).Pairwise (fun a b => value (word a) ≤ value (word b)) := by
  obtain ⟨r, _, hs, _⟩ := Classical.choose_spec (raw_sort request.records request.uniform)
  exact hs

noncomputable def carrier : WordFunction Request (fun request => stream request.records)
    (fun request => stream (sorted request))
    (fun request => 4 * (stream request.records).length + 3 + budget request.records) :=
  FramedSource.ofRaw (by decide) machine 0 _ _ _ (by
    intro request
    obtain ⟨r, _, _, hr, ho, _⟩ := Classical.choose_spec (raw_sort request.records request.uniform)
    exact ⟨r, hr, ho⟩)

end NearCubicWires.RepairOrdinary.SortCarrier
