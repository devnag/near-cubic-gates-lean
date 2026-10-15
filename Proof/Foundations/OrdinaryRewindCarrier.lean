import Proof.Foundations.OrdinaryRewind
import Proof.Foundations.OrdinaryPartitionCarrier

/-! Paid reset applied to the shared ordinary carrier and the actual partition
pass. Budget enlargement follows a proved interpreter step bound. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem runFrom_steps_le {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c = some r) : r.steps ≤ fuel := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact Nat.le_refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact Nat.zero_le _
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom p fuel d with
        | none => simp [hs, ht] at hr
        | some tail =>
          simp only [hs, ht, Option.some.injEq] at hr
          subst r
          exact Nat.add_le_add_right (ih d tail ht) 1

def Rewind.program (p : Program) : Program where
  tapeCount := p.tapeCount + 1
  stateCount := p.stateCount + 2
  twoTapes := by have h := p.twoTapes; omega
  machine := Rewind.machine p.machine
  outputTape := p.outputTape.castAdd 1
  outputFresh := p.outputFresh

theorem Rewind.input_tapes (p : Program) (bs : List Bool) :
    (Rewind.program p).inputTapes bs = Fin.addCases (p.inputTapes bs) (fun _ => []) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Program.inputTapes, Rewind.program]
  · have ht := p.twoTapes
    have hn : p.tapeCount ≠ 0 := by omega
    simp [Program.inputTapes, Rewind.program, hn]

theorem WordFunction.reset_realizes {Request : Type}
    {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) :
    ∃ r, run (Rewind.program f.program).machine (2 * budget req + 2)
        ((Rewind.program f.program).inputTapes (input req)) = some r ∧
      r.final.tapes (Rewind.program f.program).outputTape = output req ∧
      ∀ i, r.final.heads i = 0 := by
  obtain ⟨raw, hraw, hout⟩ := f.realizes req
  have hsteps := runFrom_steps_le f.program.machine (budget req) _ raw hraw
  obtain ⟨r, hr, ho, hh, _, _⟩ := Rewind.reset_run f.program.machine
    (budget req) (f.program.inputTapes (input req)) raw hraw
  have hbudget : 2 * raw.steps + 2 ≤ 2 * budget req + 2 := by omega
  have hmore := run_moreFuel (Rewind.machine f.program.machine) (2 * raw.steps + 2)
    ((2 * budget req + 2) - (2 * raw.steps + 2)) _ r hr
  refine ⟨r, ?_, (ho f.program.outputTape).trans hout, hh⟩
  rw [Rewind.input_tapes]
  simpa only [Rewind.program, Nat.add_sub_of_le hbudget] using hmore

def WordFunction.reset {Request : Type}
    {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) :
    RewoundWordFunction Request input output (fun req => 2 * budget req + 2) where
  program := Rewind.program f.program
  realizes := by
    intro req
    obtain ⟨r, hr, ho, _⟩ := f.reset_realizes req
    exact ⟨r, hr, ho⟩
  headsReset := by
    intro req r hr i
    obtain ⟨actual, ha, _, hh⟩ := f.reset_realizes req
    have he : actual = r := Option.some.inj (ha.symm.trans hr)
    subst r
    exact hh i

def StablePartition.rewoundPartitionCarrier (tag : Bool) :
    RewoundWordFunction (List StablePartition.Record) StablePartition.stream
      (fun rs => StablePartition.stream (StablePartition.selected tag rs))
      (fun rs => 2 * (6 * (StablePartition.stream rs).length + 3) + 2) :=
  (StablePartition.partitionCarrier tag).reset

end NearCubicWires.RepairOrdinary
