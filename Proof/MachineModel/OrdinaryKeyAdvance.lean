import Proof.MachineModel.OrdinaryBoundaryStore

/-! Advance both bucket scalars in the actual retained keyed workspace.
Neither the source table nor the growing aggregate output is traversed. -/
namespace NearCubicWires.RepairOrdinary.KeyAdvance
open LocalBitMultitape SignedSortKey RankBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap : ℕ) : Configuration 22 s :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (4 * W + 3) false)
    (KeyReset.config state W a b rank upper record clone mask source out K I inner keyCap resetCap)

def incrementLayout : Fin 22 ≃ Fin 22 where
  toFun := ![17,19,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,21]
  invFun := ![2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,0,19,1,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem increment_inverse : (incrementLayout.symm : Fin 22 → Fin 22) =
    ![2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,0,19,1,20,21] := rfl
def boundaryLayout : Fin 22 ≃ Fin 22 where
  toFun := ![0,1,2,3,21,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
  invFun := ![0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem boundary_inverse : (boundaryLayout.symm : Fin 22 → Fin 22) =
    ![0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,4] := rfl

def incrementHeads (out : List Bool) : Fin 20 → ℕ := fun i => if i.val = 8 then out.length else 0
def incrementTapes (W a b rank : ℕ) (upper record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I resetCap : ℕ) : Fin 20 → List Bool :=
  ![frame (binary W a), frame (binary W b), upper, List.replicate (2*W+1) false,
    frame (binary W rank), [false], [mask], List.replicate (6*W+6) false, out,
    record, clone, List.replicate (4*W+1) false, List.replicate (8*W+3) false,
    List.replicate (2*W+1) false, List.replicate (24*W+14) false, source,
    frame (binary K 0), frame (binary I 0), List.replicate resetCap false, List.replicate (4*W+3) false]
def boundaryHeads (out : List Bool) : Fin 17 → ℕ := fun i => if i.val = 4 then out.length else 0
def boundaryTapes (W rank : ℕ) (record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I inner keyCap resetCap : ℕ) : Fin 17 → List Bool :=
  ![frame (binary W rank), [false], [mask], List.replicate (6*W+6) false, out,
    record, clone, List.replicate (4*W+1) false, List.replicate (8*W+3) false,
    List.replicate (2*W+1) false, List.replicate (24*W+14) false, source,
    frame (binary K 0), frame (binary I inner), frame (binary I 0),
    List.replicate keyCap false, List.replicate resetCap false]

def scalar {s : ℕ} (state : Fin s) (I inner cap : ℕ) : Configuration 2 s :=
  ⟨state, fun _ => 0, Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
    (fun _ : Fin 1 => frame (binary I inner)) (fun _ : Fin 1 => List.replicate cap false)⟩
def increment : Machine 22 5 := TapeRenaming.machine incrementLayout (TapeEmbedding.machine 20 FramedIncrement.machine)
def boundary : Machine 22 13 := TapeRenaming.machine boundaryLayout (TapeEmbedding.machine 17 BoundaryStore.machine)
def machine : Machine 22 18 := Composition.machine increment boundary

-- reason: measured250k exhaustion normalizing the fixed22-tape placement; no data-dependent recursion.
set_option maxHeartbeats 1000000 in
theorem place_increment {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap : ℕ) :
    TapeRenaming.config incrementLayout (TapeEmbedding.config (incrementHeads out)
      (incrementTapes W a b rank upper record clone mask source out K I resetCap) (scalar state I inner keyCap)) =
      config state W a b rank upper record clone mask source out K I inner keyCap resetCap := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, scalar, config, KeyReset.config,
      KeyCell.config, RecordCell.config, CellEmit.config, RecordCell.recordHeads, incrementHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, scalar, config, KeyReset.config,
      KeyCell.config, RecordCell.config, CellEmit.config, LocalCell.input, LocalCell.raw,
      RecordCell.recordTapes, KeyCell.extraTapes, incrementTapes, Fin.addCases]

-- reason: measured250k exhaustion normalizing the fixed22-tape placement; no data-dependent recursion.
set_option maxHeartbeats 1000000 in
theorem place_boundary {s : ℕ} (state : Fin s) (W a b rank : ℕ) (upper record clone : List Bool)
    (mask : Bool) (source out : List Bool) (K I inner keyCap resetCap : ℕ) :
    TapeRenaming.config boundaryLayout (TapeEmbedding.config (boundaryHeads out)
      (boundaryTapes W rank record clone mask source out K I inner keyCap resetCap) (BoundaryStore.config state W a b upper)) =
      config state W a b rank upper record clone mask source out K I inner keyCap resetCap := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, BoundaryStore.config, config, KeyReset.config,
      KeyCell.config, RecordCell.config, CellEmit.config, RecordCell.recordHeads, boundaryHeads, Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, TapeEmbedding.config, BoundaryStore.config, config, KeyReset.config,
      KeyCell.config, RecordCell.config, CellEmit.config, LocalCell.input, LocalCell.raw,
      RecordCell.recordTapes, KeyCell.extraTapes, boundaryTapes, Fin.addCases]

theorem increment_cells (W a b rank : ℕ) (upper record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I resetCap : ℕ) :
    TapeEmbedding.extraCells (incrementTapes W a b rank upper record clone mask source out K I resetCap) =
      source.length + out.length + upper.length + record.length + clone.length + 56*W + 2*K + 2*I + resetCap + 36 := by
  simp only [TapeEmbedding.extraCells, incrementTapes, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, frame_length, binary_length,
    List.length_replicate, List.length_cons, List.length_nil]
  omega
theorem boundary_cells (W rank : ℕ) (record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I inner keyCap resetCap : ℕ) :
    TapeEmbedding.extraCells (boundaryTapes W rank record clone mask source out K I inner keyCap resetCap) =
      source.length + out.length + record.length + clone.length + 46*W + 2*K + 4*I + keyCap + resetCap + 31 := by
  simp [TapeEmbedding.extraCells, boundaryTapes, Fin.sum_univ_succ]
  omega

theorem increment_run (W a b rank : ℕ) (upper record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I inner keyCap resetCap : ℕ) (hi : inner + 1 < 2 ^ I) (hc : 2*I ≤ keyCap) :
    Executes increment (4*I+2)
      (source.length + out.length + upper.length + record.length + clone.length + 56*W + 2*K + 6*I + keyCap + resetCap + 37)
      (config 0 W a b rank upper record clone mask source out K I inner keyCap resetCap)
      (config 4 W a b rank upper record clone mask source out K I (inner+1) keyCap resetCap) := by
  obtain ⟨r, hr, ht, hc', hh, hs, hp⟩ := FramedIncrement.increment_run I inner keyCap hi hc
  have hhalt := (prefix_of_run _ _ _ _ hr).2
  have hcontrol : r.final.control = 4 := by
    have h : ∀ state : Fin 5, FramedIncrement.machine.halted state = true → state = 4 := by
      intro state
      fin_cases state <;> simp [FramedIncrement.machine, Rewind.machine, Fin.addCases]
    exact h _ hhalt
  have hfinal : r.final = scalar 4 I (inner+1) keyCap := by
    apply configuration_ext
    · exact hcontrol
    · funext i; exact hh i
    · funext i; fin_cases i <;> simp [scalar, Fin.addCases, ht, hc']
  have he := TapeEmbedding.run_embed FramedIncrement.machine (incrementHeads out)
    (incrementTapes W a b rank upper record clone mask source out K I resetCap) _ _ r hr
  have hn := TapeRenaming.run_rename incrementLayout (TapeEmbedding.machine 20 FramedIncrement.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt incrementLayout (TapeEmbedding.receipt (incrementHeads out)
    (incrementTapes W a b rank upper record clone mask source out K I resetCap) r), ?_, ?_, hs, ?_⟩
  · change runFrom increment (4*I+2)
      (TapeRenaming.config incrementLayout (TapeEmbedding.config (incrementHeads out)
        (incrementTapes W a b rank upper record clone mask source out K I resetCap) (scalar 0 I inner keyCap))) = _ at hn
    simpa only [place_increment] using hn
  · change TapeRenaming.config incrementLayout (TapeEmbedding.config (incrementHeads out)
      (incrementTapes W a b rank upper record clone mask source out K I resetCap) r.final) = _
    rw [hfinal, place_increment]
  · change r.peakTapeCells + TapeEmbedding.extraCells _ ≤ _
    rw [increment_cells]
    omega

theorem boundary_run (W a b rank : ℕ) (upper record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I inner keyCap resetCap : ℕ) (hfit : a+b < 2^W) (hu : upper.length ≤ 2*W+1) :
    Executes boundary (12*W+13)
      (source.length + out.length + record.length + clone.length + 66*W + 2*K + 4*I + keyCap + resetCap + 43)
      (config boundary.start W a b rank upper record clone mask source out K I inner keyCap resetCap)
      (config 12 W (a+b) b rank (frame (binary W (a+b))) record clone mask source out K I inner keyCap resetCap) := by
  obtain ⟨r, hr, hf, hs, hp⟩ := BoundaryStore.advance_store_run W a b upper hfit hu
  have he := TapeEmbedding.run_embed BoundaryStore.machine (boundaryHeads out)
    (boundaryTapes W rank record clone mask source out K I inner keyCap resetCap) _ _ r hr
  have hn := TapeRenaming.run_rename boundaryLayout (TapeEmbedding.machine 17 BoundaryStore.machine) _ _ _ he
  refine ⟨TapeRenaming.receipt boundaryLayout (TapeEmbedding.receipt (boundaryHeads out)
    (boundaryTapes W rank record clone mask source out K I inner keyCap resetCap) r), ?_, ?_, hs.le, ?_⟩
  · simpa only [place_boundary, boundary, TapeRenaming.machine, TapeEmbedding.machine] using hn
  · change TapeRenaming.config boundaryLayout (TapeEmbedding.config (boundaryHeads out)
      (boundaryTapes W rank record clone mask source out K I inner keyCap resetCap) r.final) = _
    rw [hf, place_boundary]
  · change r.peakTapeCells + TapeEmbedding.extraCells _ ≤ _
    rw [boundary_cells]
    omega

theorem advance_run (W a b rank : ℕ) (upper record clone : List Bool) (mask : Bool)
    (source out : List Bool) (K I inner keyCap resetCap : ℕ)
    (hi : inner+1 < 2^I) (hc : 2*I ≤ keyCap) (hfit : a+b < 2^W) (hu : upper.length ≤ 2*W+1) :
    Executes machine (12*W+4*I+16)
      (source.length + out.length + record.length + clone.length + 66*W + 2*K + 6*I + keyCap + resetCap + 43)
      (config machine.start W a b rank upper record clone mask source out K I inner keyCap resetCap)
      (config 17 W (a+b) b rank (frame (binary W (a+b))) record clone mask source out K I (inner+1) keyCap resetCap) := by
  let space := source.length + out.length + record.length + clone.length + 66*W + 2*K + 6*I + keyCap + resetCap + 43
  obtain ⟨r, hr, hf, hs, hp⟩ := increment_run W a b rank upper record clone mask source out K I inner keyCap resetCap hi hc
  have first : Executes increment (4*I+2) space _ _ := ⟨r, hr, hf, hs, by dsimp only [space]; omega⟩
  obtain ⟨q, hq, hqf, hqs, hqp⟩ := boundary_run W a b rank upper record clone mask source out K I (inner+1) keyCap resetCap hfit hu
  have second : Executes boundary (12*W+13) space _ _ := ⟨q, hq, hqf, hqs, by dsimp only [space]; omega⟩
  have joined := first.join second rfl
  have htime : 4*I+2+1+(12*W+13) = 12*W+4*I+16 := by omega
  rw [htime] at joined
  exact joined

end NearCubicWires.RepairOrdinary.KeyAdvance
