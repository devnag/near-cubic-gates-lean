import SourceAdapters.Code.PairTransformConcat
import SourceAdapters.Code.PairTransformLayout
import Proof.Gates.Cells.OutLen

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid application of an ordinary framed-output
function to the first field of a pair while preserving the second field. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairTransform

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.CheckedPCPP

variable {A : Type} {input output : A → List Bool} {budget : A → ℕ}

def rawBudget (input output : A → List Bool) (budget : A → ℕ) (r : A × List Bool) : ℕ :=
  (44 * (input r.1).length + 44 * r.2.length + 62) + 1 + (2 * budget r.1 + 2) + 1 +
    (44 * (output r.1).length + 44 * r.2.length + 40)

theorem raw_run (P : WordFunction A input (fun a => frame (output a)) budget) (a : A) (y : List Bool) :
    ∃ receipt, run (rawMachine (Rewind.program P.program)) (rawBudget input output budget (a, y))
      (SourceHandoff.sourceTapes (frame (input a) ++ frame y)) = some receipt ∧
      receipt.final.tapes (finishSlots (Rewind.program P.program) 3) = frame (output a) ++ frame y := by
  let p := Rewind.program P.program
  let T : Fin (tapes p) → List Bool := SourceHandoff.sourceTapes (frame (input a) ++ frame y)
  obtain ⟨os, hs, hs2, hs3⟩ := split_ready (input a) y
  obtain ⟨op, hp, hop⟩ := wordFunction_ready P a
  obtain ⟨ofn, hf, hof⟩ := Retained.pair_ready (output a) y
  have hs' := hs.focus (splitSlots p) (splitSlots_injective p) T (by intro i; rfl)
  let B := install (splitSlots p) T os
  have hinput : ∀ i, B (callSlots p i) = p.inputTapes (input a) i := by
    intro i
    by_cases hi : i.val = 0
    · change install (splitSlots p) T os (callSlots p i) = _
      have he : callSlots p i = splitSlots p 2 := by simp [callSlots, splitSlots, hi]
      rw [he, install_slot _ (splitSlots_injective p)]
      simpa [Program.inputTapes, hi] using hs2
    · rw [show B = install (splitSlots p) T os from rfl,
        install_other _ _ _ _ (call_not_split p i hi)]
      simp [T, SourceHandoff.sourceTapes, Program.inputTapes, callSlots, hi]
  have hp' := hp.focus (callSlots p) (callSlots_injective p) B hinput
  let D := install (callSlots p) B op
  have hwork : ∀ i : Fin 6, i.val ≠ 0 ∧ i.val ≠ 2 → D (finishSlots p i) = [] := by
    intro i hi
    rw [show D = install (callSlots p) B op from rfl,
      install_other _ _ _ _ (finish_work_not_call p i hi)]
    rw [show B = install (splitSlots p) T os from rfl,
      install_other _ _ _ _ (finish_work_not_split p i hi)]
    simp [T, SourceHandoff.sourceTapes, finishSlots, hi.1, hi.2]
  have hfinal : ∀ i, D (finishSlots p i) = Retained.bank (output a) (frame y) i := by
    intro i
    fin_cases i
    · have he : finishSlots p 0 = callSlots p p.outputTape := by
        simp [finishSlots, callSlots, p.outputFresh]
      change install (callSlots p) B op (finishSlots p 0) = _
      rw [he, install_slot _ (callSlots_injective p)]
      exact hop
    · exact hwork 1 (by decide)
    · change install (callSlots p) B op (splitSlots p 3) = frame y
      rw [install_other _ _ _ _ (call_not_second p)]
      change install (splitSlots p) T os (splitSlots p 3) = _
      rw [install_slot _ (splitSlots_injective p)]
      exact hs3
    · exact hwork 3 (by decide)
    · exact hwork 4 (by decide)
    · exact hwork 5 (by decide)
  have hf' := hf.focus (finishSlots p) (finishSlots_injective p) D hfinal
  have first := ClockJoin.join _ _ _ _ T B D hs' hp'
  have all := ClockJoin.join _ _ _ _ T D _ first hf'
  obtain ⟨receipt, hrun, hout, _, _⟩ := all
  refine ⟨receipt, hrun, ?_⟩
  rw [hout, install_slot _ (finishSlots_injective p)]
  exact hof

noncomputable def mapped (P : WordFunction A input (fun a => frame (output a)) budget) :
    WordFunction (A × List Bool) (fun r => pairWord (input r.1, r.2))
      (fun r => frame (output r.1) ++ frame r.2)
      (fun r => 4 * (pairWord (input r.1, r.2)).length + 3 + rawBudget input output budget r) :=
  FramedSource.ofRaw (by dsimp [tapes]; omega) (rawMachine (Rewind.program P.program))
    (finishSlots (Rewind.program P.program) 3) _ _ _ (fun r => raw_run P r.1 r.2)

def mapBudget (pairLength sourceBudget : ℕ) : ℕ := 100 * pairLength + 46 * sourceBudget + 120

/-- Only the first payload changes. `P` already produces its exact output frame. -/
noncomputable def mapFirst (P : WordFunction A input (fun a => frame (output a)) budget) :
    WordFunction (A × List Bool) (fun r => frame (input r.1) ++ frame r.2)
      (fun r => frame (output r.1) ++ frame r.2)
      (fun r => mapBudget (frame (input r.1) ++ frame r.2).length (budget r.1)) :=
  (mapped P).enlargeBudget (fun r => by
    have ho := NearCubicGates.Close.Cells.wf_out_len P r.1
    rw [frame_length] at ho
    dsimp [mapBudget, rawBudget, pairWord]
    simp only [List.length_append, frame_length]
    omega)

theorem mapBudget_poly (K e : ℕ)
    (h : ∀ r : A × List Bool, budget r.1 ≤ K * ((frame (input r.1) ++ frame r.2).length + 1) ^ e) :
    ∀ r : A × List Bool, mapBudget (frame (input r.1) ++ frame r.2).length (budget r.1) ≤
      (46 * K + 220) * ((frame (input r.1) ++ frame r.2).length + 1) ^ (e + 1) := by
  intro r
  have hn : 1 ≤ (frame (input r.1) ++ frame r.2).length + 1 := by omega
  have he := Nat.pow_le_pow_right hn (show e ≤ e + 1 by omega)
  have h1 := Nat.pow_le_pow_right hn (show 1 ≤ e + 1 by omega)
  have hp : 1 ≤ ((frame (input r.1) ++ frame r.2).length + 1) ^ (e + 1) := Nat.one_le_pow _ _ hn
  have hb := (h r).trans (Nat.mul_le_mul_left K he)
  simp only [pow_one] at h1
  dsimp [mapBudget]
  nlinarith

theorem mapBudget_poly_of_source (K e : ℕ)
    (h : ∀ a, budget a ≤ K * ((input a).length + 1) ^ e) :
    ∀ r : A × List Bool, mapBudget (frame (input r.1) ++ frame r.2).length (budget r.1) ≤
      (46 * K + 220) * ((frame (input r.1) ++ frame r.2).length + 1) ^ (e + 1) := by
  apply mapBudget_poly K e
  intro r
  apply (h r.1).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [List.length_append, frame_length]
  omega

end NearCubicGates.Adapters.Code.PairTransform
