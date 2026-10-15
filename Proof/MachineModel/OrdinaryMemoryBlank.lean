import Proof.MachineModel.OrdinaryMemoryValidation
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! Remove all preallocated blank scratch from the actual checker entry.
Only the sorted source, framed initial key and true result bit remain. Cells
are allocated by actual writes, with exactly the same execution time. -/
namespace NearCubicWires.RepairOrdinary.MemoryBlank
open LocalBitMultitape MemoryLog MemorySort MemoryCompare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (source initialKey : List Bool) : Fin 14 → List Bool :=
  fun i => if i = 7 then source else if i = 8 then frame initialKey
    else if i = 13 then [true] else []

def capacities (I : ℕ) : Fin 14 → ℕ :=
  ![0,0,4*(I+2)+1,8*(I+2)+3,0,2*(I+2)+1,24*(I+2)+14,
    0,0,1,0,MemoryCycle.checkCap I,MemoryCycle.copyCap I,0]

theorem padded_input (I : ℕ) (source initialKey : List Bool) :
    ZeroPadding.config (capacities I)
      (initialConfiguration MemoryLoop.machine (tapes source initialKey)) =
    MemoryBody.config MemoryLoop.machine.start I [] [] [] source 0 initialKey false [] true := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config, initialConfiguration, MemoryBody.config,
      MemoryCycle.ready, MemoryCycle.config, TapeEmbedding.config, Fin.addCases]
  · funext i
    fin_cases i <;> simp [ZeroPadding.config, initialConfiguration, MemoryBody.config,
      MemoryCycle.ready, MemoryCycle.config, TapeEmbedding.config, Fin.addCases,
      MemoryBody.workspace, tapes, capacities, ZeroPadding.pad]

theorem blank_run {N : ℕ} (I W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^(I+2))
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    ∃ r : ExecutionReceipt 14 43,
      run MemoryLoop.machine (N*(240*(I+2)+182)+1)
        (tapes (StablePartition.stream (SortCarrier.sorted (request I (I+2) W events)))
          (key I W MemoryScan.blank)) = some r ∧
      r.final.tapes 13 =
        [(MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome] ∧
      r.final.heads 13 = 0 ∧ r.steps = N*(240*(I+2)+182)+1 := by
  obtain ⟨base, hb, ho, hh, hs⟩ := MemoryValidation.checked_run I W events hN hc ha
  rw [← padded_input] at hb
  obtain ⟨r, hr, hf, ht, _⟩ := ZeroPadding.run_unpad MemoryLoop.machine (capacities I)
    _ _ base hb
  refine ⟨r, hr, ?_, ?_, ht.trans hs⟩
  · have h := congrArg (fun c => c.tapes 13) hf
    simpa [ZeroPadding.config, capacities, ho] using h
  · have h := congrArg (fun c => c.heads 13) hf
    exact h.trans hh

end NearCubicWires.RepairOrdinary.MemoryBlank
