import Proof.MachineModel.OrdinaryMemoryEmitAdvance

/-! One actual initialization cell. Read the next physical framed input bit,
emit its exact event, and advance both consecutive counters. The source and
event stream remain at their streaming cursors throughout. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialCell
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (I K serial cell cap : ℕ)
    (out source : List Bool) (cursor : ℕ) (after : Bool) : Configuration 9 s :=
  TapeEmbedding.config (![cursor] : Fin 1 → ℕ) (![source] : Fin 1 → List Bool)
    (MemoryRecordEmitter.config state (binary I serial) (binary K cell) out false after cap)

@[simp] theorem config_cells {s : ℕ} (state : Fin s) (I K serial cell cap : ℕ)
    (out source : List Bool) (cursor : ℕ) (after : Bool) :
    (config state I K serial cell cap out source cursor after).tapeCells =
      2*I+2*K+out.length+cap+2+source.length := by
  simp [config, TapeEmbedding.config_cells, TapeEmbedding.extraCells]

def loadAction (bit : Bool) : Action 9 2 :=
  ⟨1, fun i => if i = 7 then some bit else none,
    fun i => if i = 8 then .right else .stay⟩
def load : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val == 1
  rule := fun s scanned => if s.val = 0 then some (loadAction (scanned 8)) else none
def emit : Machine 9 23 := TapeEmbedding.machine 1 MemoryEmitAdvance.machine
def machine : Machine 9 25 := Composition.machine load emit

theorem load_step (I K serial cell cap : ℕ) (out source : List Bool)
    (cursor : ℕ) (after : Bool) :
    step load (config 0 I K serial cell cap out source cursor after) =
      some (config 1 I K serial cell cap out source (cursor+1) (readTapeBit source cursor)) := by
  change some (applyAction (config 0 I K serial cell cap out source cursor after)
    (loadAction (readTapeBit source cursor))) = _
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, loadAction, config, TapeEmbedding.config,
      MemoryRecordEmitter.config, HeadMove.apply, Fin.addCases]
  · funext i
    fin_cases i <;> simp [applyAction, loadAction, config, TapeEmbedding.config,
      MemoryRecordEmitter.config, Fin.addCases, writeTapeBit]

theorem load_run (I K serial cell cap : ℕ) (out source : List Bool)
    (cursor : ℕ) (after : Bool) :
    ∃ r : ExecutionReceipt 9 2,
      runFrom load 1 (config 0 I K serial cell cap out source cursor after) = some r ∧
      r.final = config 1 I K serial cell cap out source (cursor+1) (readTapeBit source cursor) := by
  let last := config (1 : Fin 2) I K serial cell cap out source (cursor+1) (readTapeBit source cursor)
  let tail : ExecutionReceipt 9 2 := ⟨last,0,last.tapeCells⟩
  have ht : runFrom load 0 last = some tail := runFrom_zero_of_halted load last (by rfl)
  have hr := runFrom_step load _ _ tail (by rfl)
    (load_step I K serial cell cap out source cursor after) ht
  exact ⟨_, hr, rfl⟩

theorem cell_run (I K serial cell cap : ℕ) (out source : List Bool)
    (cursor : ℕ) (after : Bool)
    (hs : serial+1 < 2^I) (hk : cell+1 < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 9 25,
      runFrom machine (6*I+6*K+22)
        (config 0 I K serial cell cap out source cursor after) = some r ∧
      r.final = config 24 I K (serial+1) (cell+1) cap
        (out++frame (false::readTapeBit source cursor::binary I serial++binary K cell))
        source (cursor+1) (readTapeBit source cursor) := by
  obtain ⟨first, hf, hff⟩ := load_run I K serial cell cap out source cursor after
  obtain ⟨base, hb, hbf⟩ := MemoryEmitAdvance.record_run I K serial cell cap out false
    (readTapeBit source cursor) hs hk hI hK
  have he := TapeEmbedding.run_embed MemoryEmitAdvance.machine
    (![cursor+1] : Fin 1 → ℕ) (![source] : Fin 1 → List Bool) _ _ base hb
  let last := TapeEmbedding.receipt (![cursor+1] : Fin 1 → ℕ) (![source] : Fin 1 → List Bool) base
  have hi : Composition.restart first.final emit.start =
      TapeEmbedding.config (![cursor+1] : Fin 1 → ℕ) (![source] : Fin 1 → List Bool)
        (MemoryRecordEmitter.config 0 (binary I serial) (binary K cell) out false
          (readTapeBit source cursor) cap) := by rw [hff]; rfl
  rw [← hi] at he
  have hall := Composition.run_join load emit 1 (6*I+6*K+20)
    (config 0 I K serial cell cap out source cursor after) first last hf he
  have htime : 1+1+(6*I+6*K+20) = 6*I+6*K+22 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last, hall, ?_⟩
  simp only [Composition.joinedReceipt, last, TapeEmbedding.receipt, hbf]
  rfl

end NearCubicWires.RepairOrdinary.MemoryInitialCell
