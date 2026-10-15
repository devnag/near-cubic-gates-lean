import Proof.MachineModel.OrdinaryMemoryRecordEmitter

/-! Reuse the serializer's larger reset counter for ordinary binary
increments. Retained zeros are preserved and no surrounding stream is reset. -/
namespace NearCubicWires.RepairOrdinary.MemoryEmitCounter
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (cap : ℕ) : Fin 2 → ℕ := ![0,cap]
theorem increment_run (width n cap : ℕ) (hn : n+1 < 2^width) (hcap : width ≤ cap) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom (Rewind.machine BinaryIncrement.machine) (2*width+2)
        (RankScalar.scalarConfig 0 (binary width n) 0 (List.replicate cap false) 0) = some r ∧
      r.final = RankScalar.scalarConfig 3 (binary width (n+1)) 0 (List.replicate cap false) 0 := by
  obtain ⟨base, hb, hf, _, _⟩ := RankScalar.increment_run width n hn
  obtain ⟨r, hr, hrf, _, _⟩ := ZeroPadding.run_config (Rewind.machine BinaryIncrement.machine)
    (capacities cap) _ _ base hb
  have padding (state : Fin 4) (bits : List Bool) :
      ZeroPadding.config (capacities cap)
        (RankScalar.scalarConfig state bits 0 (List.replicate width false) 0) =
      RankScalar.scalarConfig state bits 0 (List.replicate cap false) 0 := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, capacities, RankScalar.scalarConfig,
        Rewind.Workspace.pad_zeros, max_eq_left hcap]
  rw [padding] at hr
  refine ⟨r, hr, ?_⟩
  rw [hrf, hf, padding]

end NearCubicWires.RepairOrdinary.MemoryEmitCounter
