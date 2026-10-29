import SourceAdapters.Machine.CappedRequestPrefix
import Proof.Foundations.OrdinaryFramedSource

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: the actual externally framed request loader and paid reset. -/
namespace NearCubicGates.Adapters.Machine.Capped.RequestLoader
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

def requestMachine : Machine 8 13 :=
  Rewind.machine (FramedSource.machine 4 (by decide) machine)

def requestSlot (i : Fin 4) : Fin 8 :=
  (FramedSource.inputLayout 4 (by decide) (i.castAdd 3)).castAdd 1

def requestInput (r : CappedRequest) : Fin 8 → List Bool :=
  fun i => if i.val=0 then frame (cappedRequestWord r) else []

/-- The three actual requested fields, with every head reset. -/
theorem request_run (cap : ℕ) (word : List Bool) :
    ∃ r, run requestMachine (30*(cap+word.length+1)) (requestInput (cap,word)) = some r ∧
      (∀ i, r.final.heads i=0) ∧
      r.final.tapes (requestSlot 1) = frame word ∧
      r.final.tapes (requestSlot 2) = List.replicate cap true ∧
      r.final.tapes (requestSlot 3) = [true] := by
  obtain ⟨raw, hr, hf, _⟩ := loader_run cap word
  obtain ⟨loaded, hl, hlt, _, _⟩ := FramedSource.source_handoff (by decide : 0<4)
    machine (cappedRequestWord (cap,word)) (2*cap+2*word.length+3) raw hr
  obtain ⟨result, hres, hrest, hresh, _, _⟩ := Rewind.reset_run _ _ _ loaded hl
  have hsteps := runFrom_steps_le _ _ _ loaded hl
  have hlen : (cappedRequestWord (cap,word)).length = 2*cap+2*word.length+2 := by
    simp [cappedRequestWord, frame_length]
    omega
  have hb : 2*loaded.steps+2 ≤ 30*(cap+word.length+1) := by rw [hlen] at hsteps; omega
  have hmore := run_moreFuel _ (2*loaded.steps+2)
    (30*(cap+word.length+1)-(2*loaded.steps+2)) _ result hres
  rw [Nat.add_sub_of_le hb] at hmore
  have hi : Fin.addCases (motive := fun _ : Fin (7+1) => List Bool) (fun i : Fin 7 => if i.val=0 then frame (cappedRequestWord (cap,word)) else [])
      (fun _ : Fin 1 => []) = requestInput (cap,word) := by
    funext i
    fin_cases i <;> rfl
  rw [hi] at hmore
  refine ⟨result, hmore, hresh, ?_, ?_, ?_⟩
  · rw [requestSlot, hrest, hlt, hf]
    rfl
  · rw [requestSlot, hrest, hlt, hf]
    rfl
  · rw [requestSlot, hrest, hlt, hf]
    rfl

end NearCubicGates.Adapters.Machine.Capped.RequestLoader
