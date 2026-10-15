import Proof.MachineModel.OrdinaryLocalCell

/-! Execute a scalar cell beside the advancing matrix-output cursor, then
append and clear the one-bit local result in one real transition. -/
namespace NearCubicWires.RepairOrdinary.CellEmit
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cleared (tapes : Fin 8 → List Bool) : Fin 8 → List Bool := Function.update tapes 5 [false]
def config {s : ℕ} (state : Fin s) (tapes : Fin 8 → List Bool) (out : List Bool) : Configuration 9 s :=
  ⟨state, Fin.addCases (motive := fun _ : Fin (8 + 1) => ℕ) (fun _ => 0) (fun _ => out.length),
    Fin.addCases (motive := fun _ : Fin (8 + 1) => List Bool) tapes (fun _ => out)⟩
def emitter : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 1
  rule := fun state scanned => if state.val = 0 then
    some ⟨1, fun i => if i.val = 5 then some false else if i.val = 8 then some (scanned 5) else none,
      fun i => if i.val = 8 then .right else .stay⟩ else none

theorem emit_run (tapes : Fin 8 → List Bool) (out : List Bool) (bit : Bool) (hbit : tapes 5 = [bit]) :
    ∃ r : ExecutionReceipt 9 2,
      runFrom emitter 1 (config 0 tapes out) = some r ∧
      r.final = config 1 (cleared tapes) (out ++ [bit]) ∧ r.steps = 1 ∧
      r.peakTapeCells ≤ TapeEmbedding.extraCells tapes + out.length + 1 := by
  have hread : (config (0 : Fin 2) tapes out).scanned 5 = bit := by
    change readTapeBit (tapes 5) 0 = bit
    rw [hbit]
    rfl
  have hstep : step emitter (config 0 tapes out) = some (config 1 (cleared tapes) (out ++ [bit])) := by
    simp [step, emitter, config]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [applyAction, HeadMove.apply, Fin.addCases]
    · funext i
      fin_cases i <;> simp [applyAction, cleared, Fin.addCases, hbit, Streaming.write_append]
      · rfl
      · exact hread
  have hspace : (config (1 : Fin 2) (cleared tapes) (out ++ [bit])).tapeCells ≤
      TapeEmbedding.extraCells tapes + out.length + 1 := by
    have hl : ∀ i, (cleared tapes i).length = (tapes i).length := by
      intro i
      by_cases h : i = 5
      · subst i
        simp [cleared, hbit]
      · simp [cleared, h]
    simp [Configuration.tapeCells, config, Fin.sum_univ_succ, Fin.addCases, hl, TapeEmbedding.extraCells]
    omega
  have hp : Prefix emitter (TapeEmbedding.extraCells tapes + out.length + 1) 1
      (config 0 tapes out) (config 1 (cleared tapes) (out ++ [bit])) :=
    Prefix.step (by simp [Configuration.tapeCells, config, Fin.sum_univ_succ, Fin.addCases, TapeEmbedding.extraCells]; omega)
      (by rfl) hstep (Prefix.refl _ hspace)
  exact hp.run (by rfl) hspace

def localMachine : Machine 9 18 := TapeEmbedding.machine 1 LocalCell.machine
def machine : Machine 9 20 := Composition.machine localMachine emitter

theorem cell_run (width a b rank : ℕ) (backing out : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ width) (hrank : rank < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 9 20,
      runFrom machine (12 * width + 16)
        (config machine.start (LocalCell.input width a b rank backing mask) out) = some r ∧
      r.final = config 19 (cleared (LocalCell.output width a b rank mask))
        (out ++ [LeftCell.selected a b rank mask]) ∧
      r.steps = 12 * width + 16 ∧ r.peakTapeCells ≤ 26 * width + out.length + 22 := by
  obtain ⟨base, hl, ht, hh, hs, hp⟩ := LocalCell.local_run width a b rank backing mask hfit hrank hb
  let extraHeads : Fin 1 → ℕ := fun _ => out.length
  let extraTapes : Fin 1 → List Bool := fun _ => out
  have he := TapeEmbedding.run_embed LocalCell.machine extraHeads extraTapes _ _ base hl
  let first := TapeEmbedding.receipt extraHeads extraTapes base
  obtain ⟨second, hsecond, hf, hsteps, hpeak⟩ := emit_run (LocalCell.output width a b rank mask) out
    (LeftCell.selected a b rank mask) rfl
  have hmid : Composition.restart first.final emitter.start = config 0 (LocalCell.output width a b rank mask) out := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        config, extraHeads, hh, Fin.addCases]
    · simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config, config, ht, extraTapes]
  have hsecond' : runFrom emitter 1 (Composition.restart first.final emitter.start) = some second := by
    rw [hmid]
    exact hsecond
  have hj := Composition.run_join localMachine emitter (12 * width + 14) 1
    (TapeEmbedding.config extraHeads extraTapes (initialConfiguration LocalCell.machine
      (LocalCell.input width a b rank backing mask))) first second he hsecond'
  have hi : Composition.leftConfig 2
      (TapeEmbedding.config extraHeads extraTapes (initialConfiguration LocalCell.machine
        (LocalCell.input width a b rank backing mask))) =
      config machine.start (LocalCell.input width a b rank backing mask) out := rfl
  have htime : (12 * width + 14) + 1 + 1 = 12 * width + 16 := by omega
  refine ⟨Composition.joinedReceipt first second, by rw [hi, htime] at hj; exact hj, ?_, ?_, ?_⟩
  · change Composition.rightConfig 18 second.final = _
    rw [hf]
    rfl
  · change base.steps + 1 + second.steps = _
    omega
  · change max (base.peakTapeCells + TapeEmbedding.extraCells extraTapes) second.peakTapeCells ≤ _
    simp [TapeEmbedding.extraCells, LocalCell.output, Fin.sum_univ_succ] at hpeak
    simp [TapeEmbedding.extraCells, extraTapes]
    omega

end NearCubicWires.RepairOrdinary.CellEmit
