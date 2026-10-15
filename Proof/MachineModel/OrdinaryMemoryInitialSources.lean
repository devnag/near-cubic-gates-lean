import Proof.MachineModel.OrdinaryMemoryInitialEmission

/-! Both initialization sources in one actual machine. Static tape routing
selects the witness source and its separately produced tape-one key; no large
source or output is recopied. The width and reset tapes are reused. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialSources
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (I K serial inputCell witnessCell cap : ℕ)
    (out input witness : List Bool) (inputCursor witnessCursor : ℕ) (after : Bool) : Configuration 11 s :=
  TapeEmbedding.config (![witnessCursor,0] : Fin 2 → ℕ)
    (![witness,binary K witnessCell] : Fin 2 → List Bool)
    (MemoryInitialCell.config state I K serial inputCell cap out input inputCursor after)

def layout : Fin 11 ≃ Fin 11 where
  toFun := ![0,1,2,3,10,5,6,7,9,8,4]
  invFun := ![0,1,2,3,10,5,6,7,9,8,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem inverse : (layout.symm : Fin 11 → Fin 11) = ![0,1,2,3,10,5,6,7,9,8,4] := rfl

def first : Machine 11 77 := TapeEmbedding.machine 2 MemoryInitialLoop.machine
def second : Machine 11 77 := TapeRenaming.machine layout first
def machine : Machine 11 154 := Composition.machine first second

theorem swapped {s : ℕ} (state : Fin s) (I K serial inputCell witnessCell cap : ℕ)
    (out input witness : List Bool) (inputCursor witnessCursor : ℕ) (after : Bool) :
    TapeRenaming.config layout
      (config state I K serial inputCell witnessCell cap out input witness inputCursor witnessCursor after) =
    config state I K serial witnessCell inputCell cap out witness input witnessCursor inputCursor after := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config, MemoryInitialCell.config,
      TapeEmbedding.config, MemoryRecordEmitter.config, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config, MemoryInitialCell.config,
      TapeEmbedding.config, MemoryRecordEmitter.config, Fin.addCases]

theorem first_run (I K serial cell otherCell cap : ℕ) (out pre bits post witness : List Bool)
    (witnessCursor : ℕ) (after : Bool)
    (hs : serial+(frame bits).length < 2^I) (hk : cell+(frame bits).length < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 11 77,
      runFrom first (MemoryInitialLoop.budget I K bits.length)
        (config first.start I K serial cell otherCell cap out (pre++frame bits++post) witness
          pre.length witnessCursor after) = some r ∧
      r.final = config 76 I K (serial+(frame bits).length) (cell+(frame bits).length) otherCell cap
        (out++MemoryInitialPair.records I K serial cell (frame bits)) (pre++frame bits++post) witness
        (pre.length+(frame bits).length) witnessCursor false := by
  obtain ⟨base, hb, hf⟩ := MemoryInitialLoop.frame_run I K serial cell cap out pre bits post after hs hk hI hK
  have hr := TapeEmbedding.run_embed MemoryInitialLoop.machine (![witnessCursor,0] : Fin 2 → ℕ)
    (![witness,binary K otherCell] : Fin 2 → List Bool) _ _ base hb
  refine ⟨TapeEmbedding.receipt (![witnessCursor,0] : Fin 2 → ℕ)
    (![witness,binary K otherCell] : Fin 2 → List Bool) base, hr, ?_⟩
  simp only [TapeEmbedding.receipt, hf]
  rfl

theorem initialized_run (I K W cap : ℕ) (input witness : List Bool)
    (hs : (frame input).length+(frame witness).length < 2^I)
    (hx : (frame input).length < 2^K) (hw : 2^W+(frame witness).length < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 11 154,
      runFrom machine (MemoryInitialLoop.budget I K input.length+1+MemoryInitialLoop.budget I K witness.length)
        (config machine.start I K 0 0 (2^W) cap [] (frame input) (frame witness) 0 0 false) = some r ∧
      r.final = config 153 I K ((frame input).length+(frame witness).length)
        (frame input).length (2^W+(frame witness).length) cap
        (MemoryInitialEmission.fields I K W 0 (MemoryInitialization.events input witness))
        (frame input) (frame witness) (frame input).length (frame witness).length false := by
  let emitted := MemoryInitialPair.records I K 0 0 (frame input)
  obtain ⟨firstReceipt, hf, hff⟩ := first_run I K 0 0 (2^W) cap [] [] input [] (frame witness) 0 false
    (by omega) (by simpa only [Nat.zero_add] using hx) hI hK
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hf hff
  obtain ⟨base, hb, hbf⟩ := first_run I K (frame input).length (2^W) (frame input).length cap
    emitted [] witness [] (frame input) (frame input).length false hs hw hI hK
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hb hbf
  have hr := TapeRenaming.run_rename layout first _ _ base hb
  rw [swapped] at hr
  let last := TapeRenaming.receipt layout base
  have hlast : last.final = config 76 I K ((frame input).length+(frame witness).length)
      (frame input).length (2^W+(frame witness).length) cap
      (emitted++MemoryInitialPair.records I K (frame input).length (2^W) (frame witness))
      (frame input) (frame witness) (frame input).length (frame witness).length false := by
    simp only [last, TapeRenaming.receipt, hbf, swapped]
  have hi : Composition.restart firstReceipt.final second.start =
      config first.start I K (frame input).length (frame input).length (2^W) cap emitted
        (frame input) (frame witness) (frame input).length 0 false := by rw [hff]; rfl
  rw [← hi] at hr
  have hall := Composition.run_join first second (MemoryInitialLoop.budget I K input.length)
    (MemoryInitialLoop.budget I K witness.length)
    (config first.start I K 0 0 (2^W) cap [] (frame input) (frame witness) 0 0 false)
    firstReceipt last hf hr
  refine ⟨Composition.joinedReceipt firstReceipt last, hall, ?_⟩
  simp only [Composition.joinedReceipt, hlast, MemoryInitialEmission.initialization_fields]
  rfl

end NearCubicWires.RepairOrdinary.MemoryInitialSources
