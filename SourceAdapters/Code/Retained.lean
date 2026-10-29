import SourceAdapters.Code.RetainedLayout
import Proof.Gates.Cells.OutLen

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": retain a source request beside the framed output
of an actual ordinary computation, with an explicit paid polynomial bound. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Retained

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.CheckedPCPP

variable {A : Type} {input output : A → List Bool} {budget : A → ℕ}

noncomputable def wordFunctionRaw
    (P : WordFunction A input (fun a => frame (output a)) budget) :
    WordFunction A input (fun a => frame (input a) ++ frame (output a))
      (fun a => (44 * (input a).length + 20) + 1 + (2 * budget a + 2) + 1 +
        (44 * (input a).length + 44 * (output a).length + 40)) where
  program := program (Rewind.program P.program)
  realizes a := by
    let p := Rewind.program P.program
    let T := (program p).inputTapes (input a)
    obtain ⟨oc, hc, hc0, hc3⟩ := copy_ready (input a)
    obtain ⟨op, hp, hop⟩ := wordFunction_ready P a
    obtain ⟨ofn, hf, hof⟩ := pair_ready (input a) (output a)
    have hc' := hc.focus (copySlots p) (copySlots_injective p) T (by
      intro i
      change (if i.val = 0 then frame (input a) else []) = bank (input a) [] i
      fin_cases i <;> rfl)
    let B := install (copySlots p) T oc
    have hinput : ∀ i, B (callSlots p i) = p.inputTapes (input a) i := by
      intro i
      by_cases hi : i.val = 0
      · change install (copySlots p) T oc (callSlots p i) = _
        have he : callSlots p i = copySlots p 3 := by simp [callSlots, copySlots, hi]
        rw [he, install_slot _ (copySlots_injective p)]
        simpa [Program.inputTapes, hi] using hc3
      · rw [show B = install (copySlots p) T oc from rfl,
          install_other _ _ _ _ (call_not_copy p i hi)]
        simp [T, Program.inputTapes, callSlots, hi]
    have hp' := hp.focus (callSlots p) (callSlots_injective p) B hinput
    let D := install (callSlots p) B op
    have hwork : ∀ i : Fin 6, i.val ≠ 0 ∧ i.val ≠ 2 → D (pairSlots p i) = [] := by
      intro i hi
      rw [show D = install (callSlots p) B op from rfl,
        install_other _ _ _ _ (pair_work_not_call p i hi)]
      rw [show B = install (copySlots p) T oc from rfl,
        install_other _ _ _ _ (pair_work_not_copy p i hi)]
      simp [T, Program.inputTapes, pairSlots, hi.1, hi.2]
    have hfinal : ∀ i, D (pairSlots p i) = bank (input a) (frame (output a)) i := by
      intro i
      fin_cases i
      · change install (callSlots p) B op (copySlots p 0) = frame (input a)
        rw [install_other _ _ _ _ (call_not_original p)]
        change install (copySlots p) T oc (copySlots p 0) = _
        rw [install_slot _ (copySlots_injective p)]
        exact hc0
      · exact hwork 1 (by decide)
      · have he : pairSlots p 2 = callSlots p p.outputTape := by
          simp [pairSlots, callSlots, p.outputFresh]
        change install (callSlots p) B op (pairSlots p 2) = _
        rw [he, install_slot _ (callSlots_injective p)]
        exact hop
      · exact hwork 3 (by decide)
      · exact hwork 4 (by decide)
      · exact hwork 5 (by decide)
    have hf' := hf.focus (pairSlots p) (pairSlots_injective p) D hfinal
    have first := ClockJoin.join _ _ _ _ T B D hc' hp'
    have all := ClockJoin.join _ _ _ _ T D _ first hf'
    obtain ⟨receipt, hrun, hout, _, _⟩ := all
    refine ⟨receipt, hrun, ?_⟩
    change receipt.final.tapes (pairSlots p 3) = _
    rw [hout, install_slot _ (pairSlots_injective p)]
    exact hof

def retainedBudget (inputLength sourceBudget : ℕ) : ℕ :=
  88 * inputLength + 46 * sourceBudget + 64

/-- The source output already has its frame. The wrapper pays to preserve the
input frame, execute the source, copy both frames and reset every head. -/
noncomputable def wordFunction
    (P : WordFunction A input (fun a => frame (output a)) budget) :
    WordFunction A input (fun a => frame (input a) ++ frame (output a))
      (fun a => retainedBudget (input a).length (budget a)) :=
  (wordFunctionRaw P).enlargeBudget (fun a => by
    have h := NearCubicGates.Close.Cells.wf_out_len P a
    rw [frame_length] at h
    dsimp [retainedBudget]
    omega)

theorem retainedBudget_poly (K e : ℕ)
    (h : ∀ a, budget a ≤ K * ((input a).length + 1) ^ e) :
    ∀ a, retainedBudget (input a).length (budget a) ≤
      (46 * K + 152) * ((input a).length + 1) ^ (e + 1) := by
  intro a
  have hn : 1 ≤ (input a).length + 1 := by omega
  have he := Nat.pow_le_pow_right hn (show e ≤ e + 1 by omega)
  have h1 := Nat.pow_le_pow_right hn (show 1 ≤ e + 1 by omega)
  have hp : 1 ≤ ((input a).length + 1) ^ (e + 1) := Nat.one_le_pow _ _ hn
  have hb := (h a).trans (Nat.mul_le_mul_left K he)
  simp only [pow_one] at h1
  dsimp [retainedBudget]
  nlinarith

end NearCubicGates.Adapters.Code.Retained
