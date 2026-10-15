import Proof.CaseAnalysis.FinalWorkerEmitBody

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerLoaderPorts

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The two stage inputs, port by port -/

theorem entry_input_cases (b t : ℕ) (xs : List Entry) (k : Fin 89) :
    CloseoutRowsEstimatorCoefficients.EntryMachine.input b t xs k =
      if k.val = 88 then CompareMachine.word xs.length
      else if k.val = 79 then CloseoutRowsEstimatorCoefficients.Stream.words b xs
      else if k.val = 81 then List.replicate (CompetitorRationalDecision.width b) true
      else if k.val = 82 then List.replicate (CompetitorRationalDecision.width t) true
      else if k.val = 83 then List.replicate t true
      else if k.val = 84 then List.replicate (CompetitorReusableDecision.capacity t) true
      else [] := by
  refine Fin.addCases (m := 88) (n := 1) ?_ ?_ k
  · intro m
    have hm : (Fin.castAdd 1 m).val ≠ 88 := by
      have := m.isLt
      change m.val ≠ 88
      omega
    rw [if_neg hm]
    show CompetitorMonomialEntry.extendTapes
        (CompetitorMonomialStream.coldInput b t
          (CloseoutRowsEstimatorCoefficients.Stream.words b xs)) xs.length
        (Fin.castAdd 1 m) = _
    rw [CompetitorMonomialEntry.extendTapes, Fin.addCases_left]
    rfl
  · intro m
    have hm : m = 0 := Fin.eq_zero m
    subst hm
    show CompetitorMonomialEntry.extendTapes
        (CompetitorMonomialStream.coldInput b t
          (CloseoutRowsEstimatorCoefficients.Stream.words b xs)) xs.length
        (Fin.natAdd 88 (0 : Fin 1)) = _
    rw [CompetitorMonomialEntry.extendTapes, Fin.addCases_right]
    rfl

theorem readyInput_cases (b t : ℕ) (xs : List Entry) (j : Fin 90) :
    CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput b t xs j =
      if j.val = 79 then CloseoutRowsEstimatorCoefficients.Stream.words b xs
      else if j.val = 81 then List.replicate (CompetitorRationalDecision.width b) true
      else if j.val = 82 then List.replicate (CompetitorRationalDecision.width t) true
      else if j.val = 83 then List.replicate t true
      else if j.val = 84 then List.replicate (CompetitorReusableDecision.capacity t) true
      else if j.val = 88 then CompareMachine.word xs.length
      else [] := by
  refine Fin.addCases (m := 89) (n := 1) ?_ ?_ j
  · intro k
    have hread : CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput b t xs
        (Fin.castAdd 1 k) = CloseoutRowsEstimatorCoefficients.EntryMachine.input b t xs k := by
      simp only [CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput, Fin.addCases_left]
    rw [hread]
    simp only [Fin.val_castAdd]
    rw [entry_input_cases]
    by_cases h88 : k.val = 88
    · rw [if_pos h88, if_neg (by omega : k.val ≠ 79), if_neg (by omega : k.val ≠ 81),
        if_neg (by omega : k.val ≠ 82), if_neg (by omega : k.val ≠ 83),
        if_neg (by omega : k.val ≠ 84), if_pos h88]
    · rw [if_neg h88, if_neg h88]
  · intro k
    have hk : k = 0 := Fin.eq_zero k
    subst hk
    have hread : CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput b t xs
        (Fin.natAdd 89 (0 : Fin 1)) = [] := by
      simp only [CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput, Fin.addCases_right]
    rw [hread]
    have hval : (Fin.natAdd 89 (0 : Fin 1)).val = 89 := rfl
    rw [hval]
    norm_num

theorem sum_input_cases (b : ℕ) (terms : List CompetitorValidity.Estimate) (j : Fin 95) :
    CompetitorSumEntry.input b terms j =
      if j.val = 94 then CompareMachine.word terms.length
      else if j.val = 6 then List.replicate (CompetitorRationalDecision.width b) true
      else if j.val = 84 then List.replicate b true
      else if j.val = 88 then CompetitorSumFold.words b terms
      else if j.val = 90 then
        List.replicate (CompetitorReusableDecision.capacity b) true
      else [] := by
  refine Fin.addCases (m := 94) (n := 1) ?_ ?_ j
  · intro m
    have hm : (Fin.castAdd 1 m).val ≠ 94 := by
      have := m.isLt
      change m.val ≠ 94
      omega
    rw [if_neg hm]
    show CompetitorSumEntry.extendTapes
        (CompetitorSumFold.coldInput b (CompetitorSumFold.words b terms)) terms.length
        (Fin.castAdd 1 m) = _
    rw [CompetitorSumEntry.extendTapes, Fin.addCases_left]
    rfl
  · intro m
    have hm : m = 0 := Fin.eq_zero m
    subst hm
    show CompetitorSumEntry.extendTapes
        (CompetitorSumFold.coldInput b (CompetitorSumFold.words b terms)) terms.length
        (Fin.natAdd 94 (0 : Fin 1)) = _
    rw [CompetitorSumEntry.extendTapes, Fin.addCases_right]
    rfl

/-! ## §2 The prologue's target, as bank ports -/

/-- **The ready bank, port by port.**  Ten words on ten named bank tapes, and
every other tape of the estimator bank empty. -/
theorem dockReady_of_ports (entryWidth : ℕ) (entries : List Entry)
    (bank : Fin 218 → List Bool)
    (h81 : bank 81 = CloseoutRowsEstimatorCoefficients.Stream.words entryWidth entries)
    (h83 : bank 83 = List.replicate (CompetitorRationalDecision.width entryWidth) true)
    (h84 : bank 84 = List.replicate
      (CompetitorRationalDecision.width (joinScalarWidth entryWidth entries.length)) true)
    (h85 : bank 85 = List.replicate (joinScalarWidth entryWidth entries.length) true)
    (h86 : bank 86 = List.replicate
      (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth entries.length)) true)
    (h90 : bank 90 = CompareMachine.word entries.length)
    (h98 : bank 98 = List.replicate
      (CompetitorRationalDecision.width (joinScalarWidth entryWidth entries.length)) true)
    (h176 : bank 176 = List.replicate (joinScalarWidth entryWidth entries.length) true)
    (h182 : bank 182 = List.replicate
      (CompetitorReusableDecision.capacity (joinScalarWidth entryWidth entries.length)) true)
    (h186 : bank 186 = CompareMachine.word entries.length)
    (hblank : ∀ i : Fin 218, 2 ≤ i.val → i.val < 187 →
      i.val ≠ 81 → i.val ≠ 83 → i.val ≠ 84 → i.val ≠ 85 → i.val ≠ 86 → i.val ≠ 90 →
      i.val ≠ 98 → i.val ≠ 176 → i.val ≠ 182 → i.val ≠ 186 → bank i = []) :
    DockReady entryWidth entries bank := by
  constructor
  · intro j
    rw [readyInput_cases]
    have hv : (entrySlot j).val = 2 + j.val := entrySlot_val j
    have hlt := j.isLt
    by_cases c79 : j.val = 79
    · rw [if_pos c79, show entrySlot j = (81 : Fin 218) from Fin.ext (by omega)]
      exact h81
    by_cases c81 : j.val = 81
    · rw [if_neg c79, if_pos c81, show entrySlot j = (83 : Fin 218) from Fin.ext (by omega)]
      exact h83
    by_cases c82 : j.val = 82
    · rw [if_neg c79, if_neg c81, if_pos c82,
        show entrySlot j = (84 : Fin 218) from Fin.ext (by omega)]
      exact h84
    by_cases c83 : j.val = 83
    · rw [if_neg c79, if_neg c81, if_neg c82, if_pos c83,
        show entrySlot j = (85 : Fin 218) from Fin.ext (by omega)]
      exact h85
    by_cases c84 : j.val = 84
    · rw [if_neg c79, if_neg c81, if_neg c82, if_neg c83, if_pos c84,
        show entrySlot j = (86 : Fin 218) from Fin.ext (by omega)]
      exact h86
    by_cases c88 : j.val = 88
    · rw [if_neg c79, if_neg c81, if_neg c82, if_neg c83, if_neg c84, if_pos c88,
        show entrySlot j = (90 : Fin 218) from Fin.ext (by omega)]
      exact h90
    · rw [if_neg c79, if_neg c81, if_neg c82, if_neg c83, if_neg c84, if_neg c88]
      exact hblank (entrySlot j) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    rw [sum_input_cases]
    have hv : (foldSlot j).val = if j.val = 88 then 76 else 92 + j.val := foldSlot_val j
    rw [if_neg hj] at hv
    have hlt := j.isLt
    by_cases c94 : j.val = 94
    · rw [if_pos c94, show foldSlot j = (186 : Fin 218) from Fin.ext (by omega)]
      rw [h186, contributions_length]
    by_cases c6 : j.val = 6
    · rw [if_neg c94, if_pos c6, show foldSlot j = (98 : Fin 218) from Fin.ext (by omega)]
      exact h98
    by_cases c84 : j.val = 84
    · rw [if_neg c94, if_neg c6, if_pos c84,
        show foldSlot j = (176 : Fin 218) from Fin.ext (by omega)]
      exact h176
    by_cases c90 : j.val = 90
    · rw [if_neg c94, if_neg c6, if_neg c84, if_neg hj, if_pos c90,
        show foldSlot j = (182 : Fin 218) from Fin.ext (by omega)]
      exact h182
    · rw [if_neg c94, if_neg c6, if_neg c84, if_neg hj, if_neg c90]
      exact hblank (foldSlot j) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **The emitter's three constant ports, as bank ports.** -/
theorem emitEntry_of_ports (b : ℕ) (bank : Fin 218 → List Bool)
    (h187 : bank 187 = List.replicate b true)
    (h213 : bank 213 = frame (binary b 1))
    (h214 : bank 214 = frame (binary b 1))
    (hblank : ∀ i : Fin 218, 187 < i.val → i.val < 216 →
      i.val ≠ 213 → i.val ≠ 214 → bank i = []) :
    EmitEntry b bank := by
  intro j
  have hv : (answerSlot j).val = 187 + j.val := answerSlot_val j
  have hlt := j.isLt
  by_cases c : j.val = 23 ∨ j.val = 24 ∨ j.val = 25
  · rw [if_pos c]
    exact hblank (answerSlot j) (by omega) (by omega) (by rcases c with h|h|h <;> omega)
      (by rcases c with h|h|h <;> omega)
  · rw [if_neg c]
    have hv23 : j.val ≠ 23 := fun h => c (Or.inl h)
    have hv24 : j.val ≠ 24 := fun h => c (Or.inr (Or.inl h))
    have hv25 : j.val ≠ 25 := fun h => c (Or.inr (Or.inr h))
    unfold emitConstants
    by_cases c0 : j.val = 0
    · rw [if_pos c0, show answerSlot j = (187 : Fin 218) from Fin.ext (by omega)]
      exact h187
    · rw [if_neg c0]
      by_cases c26 : j.val = 26 ∨ j.val = 27
      · rw [if_pos c26]
        rcases c26 with h | h
        · rw [show answerSlot j = (213 : Fin 218) from Fin.ext (by omega)]
          exact h213
        · rw [show answerSlot j = (214 : Fin 218) from Fin.ext (by omega)]
          exact h214
      · rw [if_neg c26]
        have h26 : j.val ≠ 26 := fun h => c26 (Or.inl h)
        have h27 : j.val ≠ 27 := fun h => c26 (Or.inr h)
        exact hblank (answerSlot j) (by omega) (by omega) (by omega) (by omega)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerLoaderPorts
