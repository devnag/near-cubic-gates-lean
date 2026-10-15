import Proof.CaseAnalysis.FinalWorkerDockBody
import Proof.Amplification.RecoveryTapeSupport

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A local run never shortens a tape -/

/-- One transition either leaves a tape alone or writes one cell, and
`writeTapeBit` is length-monotone. -/
theorem step_length_le {t s : ℕ} (p : Machine t s) (c d : Configuration t s)
    (hs : step p c = some d) (i : Fin t) : (c.tapes i).length ≤ (d.tapes i).length := by
  unfold step at hs
  obtain ⟨action, _, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  simp only [applyAction]
  cases ha : action.write i
  · exact le_rfl
  · simp only [RecoveryTapeSupport.write_length]
    omega

/-- Hence a whole run never shortens a tape. -/
theorem runFrom_length_le {t s : ℕ} (p : Machine t s) (fuel : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) (i : Fin t) :
    (c.tapes i).length ≤ (r.final.tapes i).length := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact le_rfl
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact le_rfl
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases he : runFrom p fuel d with
        | none => simp [hs, he] at hr
        | some tail =>
          simp only [hs, he, Option.some.injEq] at hr
          subst r
          exact (step_length_le p c d hs i).trans (ih d tail he)

/-- **No stage can empty a tape.**  The statement in the `Step` idiom. -/
theorem Step_length_le {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (i : Fin t) :
    (tin i).length ≤ (tout i).length := by
  obtain ⟨r, hr, _, ht, _⟩ := h
  have hle := runFrom_length_le p n ⟨p.start, hin, tin⟩ r hr i
  rw [ht] at hle
  exact hle

/-! ## §2 The answer slots are outside both docked stages -/

/-- The fold's ninety-four accumulator tapes, as bank tapes. -/
def foldBankSlot (i : Fin 94) : Fin 218 := foldSlot (i.castAdd 1)

theorem foldBankSlot_val (i : Fin 94) :
    (foldBankSlot i).val = if i.val = 88 then 76 else 92 + i.val := by
  unfold foldBankSlot
  rw [foldSlot_val]
  rfl

theorem foldBankSlot_injective : Function.Injective foldBankSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [foldBankSlot_val, foldBankSlot_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  refine Fin.ext ?_
  by_cases hA : a.val = 88 <;> by_cases hB : b.val = 88 <;>
    simp only [hA, hB, if_true, if_false] at hv <;> omega

theorem foldBankSlot_lt (i : Fin 94) : (foldBankSlot i).val < 187 := by
  rw [foldBankSlot_val]
  have := i.isLt
  split <;> omega

theorem answerSlot_ne_foldBankSlot (i : Fin 94) (j : Fin 29) : foldBankSlot i ≠ answerSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [answerSlot_val] at hv
  have := foldBankSlot_lt i
  omega

theorem answerSlot_ne_entrySlot (k : Fin 90) (j : Fin 29) : entrySlot k ≠ answerSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, answerSlot_val] at hv
  have := k.isLt
  omega

theorem answerSlot_ne_foldSlot (k : Fin 95) (j : Fin 29) : foldSlot k ≠ answerSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [foldSlot_val, answerSlot_val] at hv
  have := k.isLt
  split at hv <;> omega

/-! ## §3 The premise really is satisfiable -/

theorem store_inhabited (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry) :
    ∃ base : Fin 94 → List Bool,
      CompetitorSumFold.Store (joinScalarWidth entryWidth entries.length)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
        (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
          (contributions entries)) base := by
  obtain ⟨_receipt, out, _hrun, _hsteps, _htapes, _hheads, hstore, _hvalue⟩ :=
    CompetitorSumEntry.uniform_cold_sum_run (CompetitorRationalDecision.width entryWidth)
      (contributions entries) (contributions_valid entryWidth entries hentries)
  have hwidth : CompetitorSumWidth.width (contributions entries).length
      (CompetitorRationalDecision.width entryWidth) =
      joinScalarWidth entryWidth entries.length := by
    rw [joinScalarWidth, contributions_length]
  rw [hwidth] at hstore
  exact ⟨out, hstore⟩

/-! ## §4 The current `hemit` is refutable -/

/-- Port `1` of the record appender is the empty tape. -/
theorem append_input_one (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) :
    CloseoutRowsEstimatorCoefficients.Append.input b q count denominator 1 = [] := rfl

/-- **`body_runs`'s `hemit`, as written, has no witness.**  Quantified over an
arbitrary exit bank whose only constraint is the fold's `Store`, the emitter's
twenty-two empty operand ports cannot be produced: bank tape `188`
(`answerSlot 1`) is outside the `Store`'s reach, so it may already carry
`[true]`, and no run shortens a tape. -/
theorem emit_over_arbitrary_exit_refuted {emitStates : ℕ} (emitLoader : Machine 218 emitStates)
    (emitFuel entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry) :
    ¬ (∀ (heads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
        CompetitorSumFold.Store (joinScalarWidth entryWidth entries.length)
            (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
            (CompetitorSumFold.words (joinScalarWidth entryWidth entries.length)
              (contributions entries))
            (fun i : Fin 94 => exit (foldSlot (i.castAdd 1))) →
          ∃ (operandHeads : Fin 218 → ℕ) (operands : Fin 218 → List Bool),
            Step emitLoader emitFuel heads exit operandHeads operands ∧
            (∀ j : Fin 29, operandHeads (answerSlot j) = 0) ∧
            (∀ j : Fin 29,
              operands (answerSlot j) =
                CloseoutRowsEstimatorCoefficients.Append.input
                  (joinScalarWidth entryWidth entries.length)
                  (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
                  1 1 j)) := by
  intro hemit
  obtain ⟨base, hbase⟩ := store_inhabited entryWidth entries hentries
  have hproj : (fun i : Fin 94 => install foldBankSlot (fun _ => [true]) base
      (foldSlot (i.castAdd 1))) = base := by
    funext i
    exact install_slot foldBankSlot foldBankSlot_injective (fun _ => [true]) base i
  have hdirty : install foldBankSlot (fun _ => [true]) base (answerSlot 1) = [true] :=
    install_other foldBankSlot (fun _ => [true]) base (answerSlot 1)
      (fun i => answerSlot_ne_foldBankSlot i 1)
  obtain ⟨_operandHeads, operands, hstep, _hheads, hports⟩ :=
    hemit (fun _ => 0) (install foldBankSlot (fun _ => [true]) base) (by rw [hproj]; exact hbase)
  have hempty : operands (answerSlot 1) = [] := (hports 1).trans (append_input_one _ _ 1 1)
  have hle := Step_length_le hstep (answerSlot 1)
  rw [hdirty, hempty] at hle
  simp at hle

/-! ## §5 The corrected premise -/

/-- The emitter's `n`-determined constant ports: the runtime width word and the
two normalization fields.  These are the loader's, not the emit loader's: they
name no fold output. -/
def emitConstants (b : ℕ) (j : Fin 29) : List Bool :=
  if j.val = 0 then List.replicate b true
  else if j.val = 26 ∨ j.val = 27 then frame (binary b 1) else []

/-- **What the loader must leave on bank tapes `187 .. 215`.**  The three data
ports `23, 24, 25` are empty -- the emit loader writes them from the fold's
stored accumulator -- and the constant ports carry their words. -/
def EmitEntry (b : ℕ) (bank : Fin 218 → List Bool) : Prop :=
  ∀ j : Fin 29,
    bank (answerSlot j) = if j.val = 23 ∨ j.val = 24 ∨ j.val = 25 then [] else emitConstants b j

/-- **The corrected premise plus the three data ports is exactly
`Append.input`.**  Nothing else has to be written, and nothing has to be
erased. -/
theorem emitEntry_append (b : ℕ) (q : CompetitorValidity.Estimate)
    (bank : Fin 218 → List Bool) (hentry : EmitEntry b bank)
    (out : Fin 218 → List Bool)
    (h23 : out (answerSlot 23) = frame (binary (CompetitorRationalDecision.width b) q.positive))
    (h24 : out (answerSlot 24) = frame (binary (CompetitorRationalDecision.width b) q.negative))
    (h25 : out (answerSlot 25) = frame (binary (CompetitorRationalDecision.width b) q.denominator))
    (hrest : ∀ j : Fin 29, ¬ (j.val = 23 ∨ j.val = 24 ∨ j.val = 25) →
      out (answerSlot j) = bank (answerSlot j)) (j : Fin 29) :
    out (answerSlot j) = CloseoutRowsEstimatorCoefficients.Append.input b q 1 1 j := by
  by_cases hj : j.val = 23 ∨ j.val = 24 ∨ j.val = 25
  · have hje : j = 23 ∨ j = 24 ∨ j = 25 := by
      rcases hj with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hje with rfl | rfl | rfl
    · exact h23
    · exact h24
    · exact h25
  · rw [hrest j hj, hentry j, if_neg hj]
    have hv : j.val ≠ 23 ∧ j.val ≠ 24 ∧ j.val ≠ 25 := by
      refine ⟨fun h => hj (Or.inl h), fun h => hj (Or.inr (Or.inl h)), fun h => hj (Or.inr (Or.inr h))⟩
    unfold emitConstants CloseoutRowsEstimatorCoefficients.Append.input
    by_cases h0 : j.val = 0
    · rw [if_pos h0, if_pos (Fin.ext h0 : j = 0)]
    · rw [if_neg h0, if_neg (fun h : j = 0 => h0 (congrArg Fin.val h))]
      by_cases h26 : j.val = 26 ∨ j.val = 27
      · rw [if_pos h26, if_pos (by omega : 23 ≤ j.val ∧ j.val ≤ 27)]
        rcases h26 with h | h
        · unfold CloseoutRowsEstimatorCoefficients.Append.scalarFields
          rw [show j = (26 : Fin 29) from Fin.ext h]
          rfl
        · unfold CloseoutRowsEstimatorCoefficients.Append.scalarFields
          rw [show j = (27 : Fin 29) from Fin.ext h]
          rfl
      · rw [if_neg h26, if_neg (by omega : ¬ (23 ≤ j.val ∧ j.val ≤ 27))]

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
