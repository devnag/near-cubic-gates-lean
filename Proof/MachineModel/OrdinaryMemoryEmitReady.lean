import Proof.MachineModel.OrdinaryMemoryEmitField

/-! Repeatable scalar serializer: actual masked rewind retains the stream
append position. The unary width and scalar bits survive unchanged. -/
namespace NearCubicWires.RepairOrdinary.MemoryEmitReady
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 3) : Bool := i.val == 0 || i.val == 1
def machine (close : Bool) : Machine 4 5 :=
  MaskedReset.machine (MemoryEmitField.machine close) selected
def config {s : ℕ} (state : Fin s) (bits out : List Bool) (cap : ℕ) : Configuration 4 s :=
  ⟨state, ![0,0,out.length,0],
    ![bits,List.replicate bits.length true,out,List.replicate cap false]⟩

theorem field_run (close : Bool) (bits out : List Bool) (cap : ℕ)
    (hcap : 2*bits.length+1 ≤ cap) :
    ∃ r : ExecutionReceipt 4 5,
      runFrom (machine close) (4*bits.length+4) (config 0 bits out cap) = some r ∧
      r.final = config 4 bits (out++Streaming.marks bits++MemoryEmitField.suffix close) cap ∧
      r.steps = 4*bits.length+4 := by
  obtain ⟨base, hb, hf, hs⟩ := MemoryEmitField.append_run close bits out
  obtain ⟨r, hr, hrf, hrs, _⟩ := MaskedReset.workspace_run (MemoryEmitField.machine close)
    selected (2*bits.length+1) cap (MemoryEmitField.config 0 bits 0 out) base hb
    (by intro i hi; fin_cases i <;> simp_all [selected, MemoryEmitField.config])
    (by rw [hs]; exact hcap)
  have hi : ZeroPadding.config (Rewind.Workspace.capacities 3 cap)
      (Rewind.recording (MemoryEmitField.config 0 bits 0 out) 0) = config (0 : Fin 5) bits out cap := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, Rewind.recording, Rewind.config,
        MemoryEmitField.config, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, Rewind.Workspace.capacities,
        Rewind.recording, Rewind.config, MemoryEmitField.config, config,
        Fin.addCases, ZeroPadding.pad]
  rw [hi, hs] at hr
  have htime : 2*(2*bits.length+1)+2 = 4*bits.length+4 := by omega
  rw [htime] at hr
  refine ⟨r, hr, ?_, by omega⟩
  rw [hrf, hf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [SelectiveReset.finished, Rewind.config,
      MemoryEmitField.config, config, selected, Fin.addCases]
  · funext i
    fin_cases i <;> simp [SelectiveReset.finished, Rewind.config,
      MemoryEmitField.config, config, Fin.addCases]

end NearCubicWires.RepairOrdinary.MemoryEmitReady
