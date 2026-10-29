import SourceAdapters.Machine.CappedOutputWriteRun
import Proof.Foundations.OrdinaryComposition
import Proof.Foundations.OrdinaryTapeEmbedding

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: one actual linear-time success-result serializer. -/
namespace NearCubicGates.Adapters.Machine.Capped.OutputSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def writer : Machine 5 8 := TapeEmbedding.machine 1 OutputFrame.machine

def machine : Machine 5 (20+8) := Composition.machine OutputSeek.machine writer

theorem bridge (source marker : List Bool) (cap : ℕ) :
    Composition.restart (OutputSeek.ready source marker cap) writer.start =
      TapeEmbedding.config (fun _ : Fin 1 => source.length-1)
        (fun _ : Fin 1 => List.replicate cap true)
        (OutputFrame.entry source marker (source.length-1)) := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem serialize_run (source marker : List Bool) (cap : ℕ)
    (hm : OutputTracking.Marked source marker) (hcap : source.length ≤ cap) :
    ∃ result, run machine (12*cap+17) (OutputSeek.input source marker cap)=some result ∧
      result.final.tapes 1=frame (true::frame source) := by
  obtain ⟨first,hfirst,hf⟩ := OutputSeek.seek_run source marker cap hm hcap
  obtain ⟨last,hlast,hlf⟩ := OutputFrame.marked_writer_run source marker hm
  let extraHeads := fun _ : Fin 1 => source.length-1
  let extraTapes := fun _ : Fin 1 => List.replicate cap true
  have he := TapeEmbedding.run_embed OutputFrame.machine extraHeads extraTapes _ _ last hlast
  have hjump : Composition.restart first.final writer.start =
      TapeEmbedding.config extraHeads extraTapes (OutputFrame.entry source marker (source.length-1)) := by
    rw [hf]
    exact bridge source marker cap
  rw [←hjump] at he
  have hj := Composition.run_join OutputSeek.machine writer (8*cap+13) (4*source.length+3)
    _ first _ hfirst he
  change run machine ((8*cap+13)+1+(4*source.length+3))
    (OutputSeek.input source marker cap)=some _ at hj
  have hb : (8*cap+13)+1+(4*source.length+3) ≤ 12*cap+17 := by omega
  have hmore := run_moreFuel machine ((8*cap+13)+1+(4*source.length+3))
    (12*cap+17-((8*cap+13)+1+(4*source.length+3))) _ _ hj
  rw [Nat.add_sub_of_le hb] at hmore
  refine ⟨_,hmore,?_⟩
  simp [Composition.joinedReceipt,Composition.rightConfig,TapeEmbedding.receipt,
    TapeEmbedding.config,hlf,OutputFrame.config]
  rfl

end NearCubicGates.Adapters.Machine.Capped.OutputSerialize
