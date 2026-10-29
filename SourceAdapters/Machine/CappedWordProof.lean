import SourceAdapters.Machine.CappedWordMachine

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: unconditional implementation of the `CappedRun` interface. -/
namespace NearCubicGates.Adapters.Machine.Capped
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

noncomputable def cappedWordFunction (p : Program) :
    WordFunction CappedRequest cappedRequestWord (fun r => frame (cappedResultWord p r))
      (fun r => 55*(r.1+r.2.length+1)) where
  program := Layout.program p
  realizes := by
    rintro ⟨cap,word⟩
    exact Layout.word_run p cap word

theorem cappedWordRun : CappedWordRun := by
  intro p
  exact ⟨55,by decide,⟨cappedWordFunction p⟩⟩

theorem cappedRun : CappedRun := ⟨cappedMachineRun,cappedWordRun⟩

end NearCubicGates.Adapters.Machine.Capped
