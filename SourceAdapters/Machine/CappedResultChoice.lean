import SourceAdapters.Machine.CappedFailureOutput
import Proof.CaseAnalysis.WitnessHeaderSwitch

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: paid selection of success and failure result writers. -/
namespace NearCubicGates.Adapters.Machine.Capped.ResultWriter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
set_option autoImplicit false

def idle : Machine 6 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

def successMachine : Machine 6 (20+8) := TapeEmbedding.machine 1 OutputSerialize.machine

def input (source marker : List Bool) (cap : ℕ) (status : Bool) : Fin 6 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
    (OutputSeek.input source marker cap) (fun _ => [status])

noncomputable def machine := CloseoutWitness.HeaderSwitch.machine idle successMachine failureMachine
  (fun _ => true) (fun scan => scan 5)

theorem selected_run (j : Fin 3) (hj : j=1 ∨ j=2) (data : Fin 6 → List Bool) (fuel : ℕ)
    (base : ExecutionReceipt 6 (CloseoutWitness.HeaderSwitch.sizes 1 (20+8) (failureBits.length+1) j))
    (hbit : j=if readTapeBit (data 5) 0 then 1 else 2)
    (hr : run (CloseoutWitness.HeaderSwitch.programs idle successMachine failureMachine j) fuel data=some base) :
    ∃ result, run machine (fuel+2) data=some result ∧ result.final.tapes=base.final.tapes := by
  let prior : ExecutionReceipt 6 1 := ⟨⟨0,fun _ => 0,data⟩,0,(⟨0,fun _ => 0,data⟩ : Configuration 6 1).tapeCells⟩
  have hp : runFrom idle 0 ⟨idle.start,fun _ => 0,data⟩=some prior := rfl
  obtain ⟨result,hresult,_,_,ht⟩ := CloseoutWitness.HeaderSwitch.accepted idle successMachine failureMachine
    (fun _ => true) (fun scan => scan 5) j hj 0 fuel (fun _ => 0) data prior base hp hr rfl hbit
  refine ⟨result,?_,ht⟩
  simpa only [run,initialConfiguration,machine,Nat.zero_add,Nat.add_comm 1 fuel,Nat.add_assoc,Nat.reduceAdd] using hresult

theorem success_run (source marker : List Bool) (cap : ℕ) (status : Bool)
    (hm : OutputTracking.Marked source marker) (hcap : source.length ≤ cap) :
    ∃ result, run successMachine (12*cap+17) (input source marker cap status)=some result ∧
      result.final.tapes 1=frame (true::frame source) := by
  obtain ⟨r,hr,hout⟩ := OutputSerialize.serialize_run source marker cap hm hcap
  have he := TapeEmbedding.run_embed OutputSerialize.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => [status]) _ _ r hr
  have hi : TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => [status])
      (initialConfiguration OutputSerialize.machine (OutputSeek.input source marker cap)) =
      initialConfiguration successMachine (input source marker cap status) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at he
  refine ⟨_,he,?_⟩
  exact hout

end NearCubicGates.Adapters.Machine.Capped.ResultWriter
