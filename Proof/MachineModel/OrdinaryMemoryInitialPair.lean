import Proof.MachineModel.OrdinaryMemoryInitialCell

/-! Paid marker/payload pair for the framed initialization loop. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialPair
open LocalBitMultitape SignedSortKey
open MemoryInitialCell (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def records (I K : ℕ) : ℕ → ℕ → List Bool → List Bool
  | _, _, [] => []
  | serial, cell, b::bs =>
    frame (false::b::binary I serial++binary K cell) ++ records I K (serial+1) (cell+1) bs

theorem records_append (I K serial cell : ℕ) (xs ys : List Bool) :
    records I K serial cell (xs++ys) = records I K serial cell xs ++
      records I K (serial+xs.length) (cell+xs.length) ys := by
  induction xs generalizing serial cell with
  | nil => simp [records]
  | cons b bs ih =>
    have hs : serial+1+bs.length = serial+(bs.length+1) := by omega
    have hc : cell+1+bs.length = cell+(bs.length+1) := by omega
    simp only [List.cons_append, records, ih, List.length_cons, List.append_assoc, hs, hc]

def machine : Machine 9 50 := Composition.machine MemoryInitialCell.machine MemoryInitialCell.machine
def budget (I K : ℕ) : ℕ := 12*I+12*K+45

theorem pair_run (I K serial cell cap : ℕ) (out source : List Bool)
    (cursor : ℕ) (after : Bool)
    (hs : serial+2 < 2^I) (hk : cell+2 < 2^K)
    (hI : 2*I+1 ≤ cap) (hK : 2*K+1 ≤ cap) :
    ∃ r : ExecutionReceipt 9 50,
      runFrom machine (budget I K)
        (config 0 I K serial cell cap out source cursor after) = some r ∧
      r.final = config 49 I K (serial+2) (cell+2) cap
        (out++records I K serial cell [readTapeBit source cursor,readTapeBit source (cursor+1)])
        source (cursor+2) (readTapeBit source (cursor+1)) := by
  obtain ⟨first, hf, hff⟩ := MemoryInitialCell.cell_run I K serial cell cap out source cursor after
    (by omega) (by omega) hI hK
  let nextOut := out++frame (false::readTapeBit source cursor::binary I serial++binary K cell)
  obtain ⟨last, hl, hlf⟩ := MemoryInitialCell.cell_run I K (serial+1) (cell+1) cap nextOut source
    (cursor+1) (readTapeBit source cursor) (by omega) (by omega) hI hK
  have hi : Composition.restart first.final MemoryInitialCell.machine.start =
      config 0 I K (serial+1) (cell+1) cap nextOut source (cursor+1) (readTapeBit source cursor) := by
    rw [hff]
    rfl
  rw [← hi] at hl
  have hr := Composition.run_join MemoryInitialCell.machine MemoryInitialCell.machine
    (6*I+6*K+22) (6*I+6*K+22)
    (config 0 I K serial cell cap out source cursor after) first last hf hl
  have ht : (6*I+6*K+22)+1+(6*I+6*K+22) = budget I K := by dsimp [budget]; omega
  rw [ht] at hr
  refine ⟨Composition.joinedReceipt first last, hr, ?_⟩
  simp only [Composition.joinedReceipt, hlf, records, List.append_nil, List.append_assoc,
    nextOut, Nat.add_assoc]
  rfl

end NearCubicWires.RepairOrdinary.MemoryInitialPair
