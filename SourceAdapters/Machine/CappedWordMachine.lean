import SourceAdapters.Machine.CappedCoreRun
import SourceAdapters.Machine.CappedLoaderRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: complete literal serialized capped-run program. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

noncomputable def program (p : Program) : Program where
  tapeCount := tapes p
  stateCount := _
  twoTapes := by unfold tapes; omega
  machine := machine p
  outputTape := outputSlot p
  outputFresh := by simp [outputSlot]

theorem program_input (p : Program) (r : CappedRequest) :
    (program p).inputTapes (cappedRequestWord r)=extend p (RequestLoader.requestInput r) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Program.inputTapes,program,extend,RequestLoader.requestInput]
  · simp [Program.inputTapes,program,extend]

theorem word_run (p : Program) (cap : ℕ) (word : List Bool) :
    ∃ receipt, run (program p).machine (55*(cap+word.length+1))
        ((program p).inputTapes (cappedRequestWord (cap,word)))=some receipt ∧
      receipt.final.tapes (program p).outputTape=frame (cappedResultWord p (cap,word)) := by
  obtain ⟨first,hfirst,hh,ht,ho,hori⟩ := loader_run p cap word
  obtain ⟨last,hlast,hout⟩ := core_run p cap word first.final.tapes ht ho hori
  have he : Composition.restart first.final (core p).start =
      initialConfiguration (core p) first.final.tapes := by
    apply configuration_ext
    · rfl
    · funext i; exact hh i
    · rfl
  have htail : runFrom (core p) (14*cap+24)
      (Composition.restart first.final (core p).start)=some last := by rw [he]; exact hlast
  have hj := Composition.run_join (loader p) (core p) (30*(cap+word.length+1)) (14*cap+24)
    _ first last hfirst htail
  change run (machine p) (30*(cap+word.length+1)+1+(14*cap+24))
    (extend p (RequestLoader.requestInput (cap,word)))=some _ at hj
  have hb : 30*(cap+word.length+1)+1+(14*cap+24) ≤ 55*(cap+word.length+1) := by omega
  have hmore := run_moreFuel (machine p) (30*(cap+word.length+1)+1+(14*cap+24))
    (55*(cap+word.length+1)-(30*(cap+word.length+1)+1+(14*cap+24))) _ _ hj
  rw [Nat.add_sub_of_le hb] at hmore
  rw [program_input]
  exact ⟨_,hmore,hout⟩

end NearCubicGates.Adapters.Machine.Capped.Layout
