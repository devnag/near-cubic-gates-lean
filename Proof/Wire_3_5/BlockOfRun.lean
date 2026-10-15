import Proof.MachineModel.BlockPlatform
import Proof.MachineModel.OrdinarySortCarrier

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-- Any receipt-level run from a start configuration is a `Block` whose exit bank is the receipt's. -/
noncomputable def ofRunFrom {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : Block t :=
  ofStep (Step.of_run (p := p) (n := n) (hin := H) (tin := A) (Classical.choose_spec h) rfl rfl)

/-- A run from the initial configuration (`run p n T`, all heads at cell 0). -/
noncomputable def ofRun {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : Block t :=
  ofRunFrom p n (fun _ => 0) T h

@[simp] theorem ofRunFrom_cost {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).cost = n := rfl

@[simp] theorem ofRunFrom_entryH {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).entryH = H := rfl

@[simp] theorem ofRunFrom_entryA {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).entryA = A := rfl

@[simp] theorem ofRunFrom_machine {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).machine = p := rfl

/-- Determinism: the block's exit tapes are those of ANY successful receipt. -/
theorem ofRunFrom_exitA {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) (r : ExecutionReceipt t s)
    (hr : runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).exitA = r.final.tapes := by
  have e : Classical.choose h = r := Option.some.inj ((Classical.choose_spec h).symm.trans hr)
  change (Classical.choose h).final.tapes = r.final.tapes
  rw [e]

/-- Determinism: the block's exit heads are those of ANY successful receipt. -/
theorem ofRunFrom_exitH {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r) (r : ExecutionReceipt t s)
    (hr : runFrom p n ⟨p.start, H, A⟩ = some r) : (ofRunFrom p n H A h).exitH = r.final.heads := by
  have e : Classical.choose h = r := Option.some.inj ((Classical.choose_spec h).symm.trans hr)
  change (Classical.choose h).final.heads = r.final.heads
  rw [e]

/-- A partial specification of the run lemma (any property of the final heads and tapes of the
receipt it names) holds for the block's exit bank. -/
theorem ofRunFrom_spec {t s : ℕ} (p : Machine t s) (n : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (P : (Fin t → ℕ) → (Fin t → List Bool) → Prop)
    (hspec : ∃ r, runFrom p n ⟨p.start, H, A⟩ = some r ∧ P r.final.heads r.final.tapes) :
    P (ofRunFrom p n H A (hspec.elim fun r hr => ⟨r, hr.1⟩)).exitH
      (ofRunFrom p n H A (hspec.elim fun r hr => ⟨r, hr.1⟩)).exitA := by
  obtain ⟨r, hr, hP⟩ := hspec
  rw [ofRunFrom_exitH p n H A _ r hr, ofRunFrom_exitA p n H A _ r hr]
  exact hP

@[simp] theorem ofRun_cost {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).cost = n := rfl

@[simp] theorem ofRun_entryH {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).entryH = fun _ => 0 := rfl

@[simp] theorem ofRun_entryA {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) : (ofRun p n T h).entryA = T := rfl

theorem ofRun_exitA {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) (r : ExecutionReceipt t s) (hr : run p n T = some r) :
    (ofRun p n T h).exitA = r.final.tapes :=
  ofRunFrom_exitA p n (fun _ => 0) T h r hr

theorem ofRun_exitH {t s : ℕ} (p : Machine t s) (n : ℕ) (T : Fin t → List Bool)
    (h : ∃ r, run p n T = some r) (r : ExecutionReceipt t s) (hr : run p n T = some r) :
    (ofRun p n T h).exitH = r.final.heads :=
  ofRunFrom_exitH p n (fun _ => 0) T h r hr

/-! ## The sorter as a block -/

open NearCubicWires.RepairOrdinary.StablePartition NearCubicWires.RepairOrdinary.RadixSemantics

theorem sort_runs (rs : List Record) (hw : ∀ r ∈ rs, (word r).length = SortPreparation.width rs) :
    ∃ r, run SortCarrier.machine (SortCarrier.budget rs) (SourceHandoff.sourceTapes (stream rs)) = some r := by
  obtain ⟨_, r, _, _, hr, _⟩ := SortCarrier.raw_sort rs hw
  exact ⟨r, hr⟩

/-- The Theorem 2.5 radix sorter (6 tapes) as a block, at its own budget. -/
noncomputable def sortBlock (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = SortPreparation.width rs) : Block 6 :=
  ofRun SortCarrier.machine (SortCarrier.budget rs) (SourceHandoff.sourceTapes (stream rs)) (sort_runs rs hw)

/-- Its output tape 0 is the stream of a sorted permutation of the records, and its cost is the
sorter's budget `6w+6+2w(10·|stream|+12)`, linear in the stream for a fixed record width. -/
theorem sortBlock_out (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = SortPreparation.width rs) :
    ∃ sorted : List Record, sorted.Perm rs ∧
      sorted.Pairwise (fun a b => value (word a) ≤ value (word b)) ∧
      (sortBlock rs hw).exitA 0 = stream sorted ∧
      (sortBlock rs hw).cost = SortCarrier.budget rs := by
  obtain ⟨sorted, r, hp, hs, hr, h0, _, _⟩ := SortCarrier.raw_sort rs hw
  refine ⟨sorted, hp, hs, ?_, rfl⟩
  rw [sortBlock, ofRun_exitA _ _ _ _ r hr]
  exact h0

theorem sortBlock_entry (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = SortPreparation.width rs) :
    (sortBlock rs hw).entryH = (fun _ => 0) ∧
      (sortBlock rs hw).entryA = SourceHandoff.sourceTapes (stream rs) := ⟨rfl, rfl⟩

end NearCubicWires.WireExponent3_5.Block
