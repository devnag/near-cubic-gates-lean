import Proof.MachineModel.OrdinaryMemoryEmitCounter

/-! Emit one initialization event and advance both the global serial and
the consecutive cell address. Every operation runs on the same eight tapes;
large output prefixes are retained at their append position. -/
namespace NearCubicWires.RepairOrdinary.MemoryEmitAdvance
open LocalBitMultitape SignedSortKey
open MemoryRecordEmitter (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 8 ≃ Fin 8 where
  toFun := ![0,3,1,2,4,5,6,7]
  invFun := ![0,2,3,1,4,5,6,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem inverse : (layout.symm : Fin 8 → Fin 8) = ![0,2,3,1,4,5,6,7] := rfl
def serialMachine : Machine 8 4 := TapeRenaming.machine layout
  (TapeEmbedding.machine 6 (Rewind.machine BinaryIncrement.machine))
def keyMachine : Machine 8 4 := TapeRenaming.machine MemoryRecordEmitter.keyLayout serialMachine
def advanceMachine : Machine 8 8 := Composition.machine serialMachine keyMachine
def machine : Machine 8 23 := Composition.machine MemoryRecordEmitter.machine advanceMachine

theorem serial_run (width n : ℕ) (key out : List Bool) (read after : Bool) (cap : ℕ)
    (hn : n+1 < 2^width) (hcap : width ≤ cap) :
    ∃ r : ExecutionReceipt 8 4,
      runFrom serialMachine (2*width+2) (config 0 (binary width n) key out read after cap) = some r ∧
      r.final = config 3 (binary width (n+1)) key out read after cap := by
  obtain ⟨base, hb, hf⟩ := MemoryEmitCounter.increment_run width n cap hn hcap
  let extra : Fin 6 → List Bool :=
    ![List.replicate width true,out,key,List.replicate key.length true,[read],[after]]
  have he := TapeEmbedding.run_embed (Rewind.machine BinaryIncrement.machine)
    (![0,out.length,0,0,0,0] : Fin 6 → ℕ) extra _ _ base hb
  have hr := TapeRenaming.run_rename layout (TapeEmbedding.machine 6 (Rewind.machine BinaryIncrement.machine))
    _ _ _ he
  have hi : TapeRenaming.config layout
      (TapeEmbedding.config (![0,out.length,0,0,0,0] : Fin 6 → ℕ) extra
        (RankScalar.scalarConfig 0 (binary width n) 0 (List.replicate cap false) 0)) =
      config (0 : Fin 4) (binary width n) key out read after cap := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
        RankScalar.scalarConfig, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
        RankScalar.scalarConfig, config, extra, Fin.addCases]
  rw [hi] at hr
  refine ⟨TapeRenaming.receipt layout
    (TapeEmbedding.receipt (![0,out.length,0,0,0,0] : Fin 6 → ℕ) extra base), hr, ?_⟩
  simp only [TapeRenaming.receipt, TapeEmbedding.receipt, hf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
      RankScalar.scalarConfig, config, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config,
      RankScalar.scalarConfig, config, extra, Fin.addCases]

theorem swapped {s : ℕ} (state : Fin s) (serial key out : List Bool)
    (read after : Bool) (cap : ℕ) :
    TapeRenaming.config MemoryRecordEmitter.keyLayout (config state serial key out read after cap) =
      config state key serial out read after cap := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]

theorem key_run (width n : ℕ) (serial out : List Bool) (read after : Bool) (cap : ℕ)
    (hn : n+1 < 2^width) (hcap : width ≤ cap) :
    ∃ r : ExecutionReceipt 8 4,
      runFrom keyMachine (2*width+2) (config 0 serial (binary width n) out read after cap) = some r ∧
      r.final = config 3 serial (binary width (n+1)) out read after cap := by
  obtain ⟨base, hb, hf⟩ := serial_run width n serial out read after cap hn hcap
  have hr := TapeRenaming.run_rename MemoryRecordEmitter.keyLayout serialMachine _ _ _ hb
  rw [swapped] at hr
  refine ⟨TapeRenaming.receipt MemoryRecordEmitter.keyLayout base, hr, ?_⟩
  simp only [TapeRenaming.receipt, hf, swapped]

theorem record_run (I K serial cell cap : ℕ) (out : List Bool) (read after : Bool)
    (hs : serial+1 < 2^I) (hk : cell+1 < 2^K)
    (hIs : 2*I+1 ≤ cap) (hKs : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 8 23,
      runFrom machine (6*I+6*K+20)
        (config 0 (binary I serial) (binary K cell) out read after cap) = some r ∧
      r.final = config 22 (binary I (serial+1)) (binary K (cell+1))
        (out++frame (read::after::binary I serial++binary K cell)) read after cap := by
  let appended := out++frame (read::after::binary I serial++binary K cell)
  obtain ⟨emit, he, hef⟩ := MemoryRecordEmitter.record_run (binary I serial) (binary K cell)
    out read after cap (by simpa using hIs) (by simpa using hKs)
  simp only [binary_length] at he
  obtain ⟨first, hf, hff⟩ := serial_run I serial (binary K cell) appended read after cap hs (by omega)
  obtain ⟨last, hl, hlf⟩ := key_run K cell (binary I (serial+1)) appended read after cap hk (by omega)
  have hmid : Composition.restart first.final keyMachine.start =
      config 0 (binary I (serial+1)) (binary K cell) appended read after cap := by rw [hff]; rfl
  rw [← hmid] at hl
  have hj := Composition.run_join serialMachine keyMachine (2*I+2) (2*K+2)
    (config 0 (binary I serial) (binary K cell) appended read after cap) first last hf hl
  have hemit : Composition.restart emit.final advanceMachine.start =
      Composition.leftConfig 4 (config 0 (binary I serial) (binary K cell) appended read after cap) := by
    rw [hef]
    rfl
  rw [← hemit] at hj
  have hall := Composition.run_join MemoryRecordEmitter.machine advanceMachine
    (4*I+4*K+14) ((2*I+2)+1+(2*K+2))
    (config 0 (binary I serial) (binary K cell) out read after cap) emit
    (Composition.joinedReceipt first last) he hj
  have htime : (4*I+4*K+14)+1+((2*I+2)+1+(2*K+2)) = 6*I+6*K+20 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt emit (Composition.joinedReceipt first last), hall, ?_⟩
  simp only [Composition.joinedReceipt, hlf]
  rfl

end NearCubicWires.RepairOrdinary.MemoryEmitAdvance
