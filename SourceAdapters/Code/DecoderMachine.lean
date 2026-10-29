import SourceAdapters.Code.DecoderPrepareAlgorithm
import SourceAdapters.Code.DecoderRunAlgorithm
import SourceAdapters.Code.DecoderBounds
import SourceAdapters.Code.FramedCells

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": both ordinary decoder stages are compiled with explicit
resource bounds and composed through paid framing. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code NearCubicGates.PublishedSources.PCPP
open DecoderTypes DecoderBounds PolynomialCosts

abbrev measure (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : ℕ := (jobWord F j).length

def firstInput (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : List Bool := LengthPreparation.prepared (jobWord F j)

def middle (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : List Bool := input F (L F j) (workOf F j)

theorem first_leading (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : leadOnes (firstInput F j) = L F j :=
  LengthPreparation.leading _

theorem middle_leading (F : BinaryFamily) {onset : ℕ} (j : Job F onset) : leadOnes (middle F j) = L F j :=
  NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep _ _

def prepCost (F : BinaryFamily) (onset K e : ℕ) (j : Job F onset) : ℕ :=
  3 * DecoderPrepareAlgorithm.cost onset (L F j) (jobLength F j) (jobBits F j).length
    ((sizes onset K e).Lk (L F j)) ((sizes onset K e).Bk (L F j)) + 2

def runCost (F : BinaryFamily) (onset K e : ℕ) (j : Job F onset) : ℕ :=
  DecoderRunAlgorithm.cost (L F j) (payload F (workOf F j)).length
    ((sizes onset K e).Lk (L F j)) ((sizes onset K e).Bk (L F j))

noncomputable def preparationWordFunction (F : BinaryFamily) (onset K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e))
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    WordFunction (Job F onset) (firstInput F) (fun j => frame (middle F j))
      (fun j => langBudget (EncoderAlgorithm.callee F onset K e W) (sizes onset K e) 12 0
        (firstInput F j) (prepCost F onset K e j)) :=
  wordFunction_of_lang (firstInput F) (fun j => frame (middle F j))
    (EncoderAlgorithm.callee F onset K e W) (sizes onset K e)
    (FramedCells.framed (DecoderPrepareAlgorithm.script onset)) (prepCost F onset K e)
    (by
      intro j
      have hj := hmessage j
      have hl := word_length F j
      have hn : jobLength F j ≤ (jobWord F j).length := by omega
      obtain ⟨b, hb, hout⟩ := DecoderPrepareAlgorithm.runs F onset K e W
        ((sizes onset K e).W (L F j)) ((sizes onset K e).Lk (L F j)) ((sizes onset K e).Bk (L F j))
        (L F j) j (prep_capacity F K e j hj) (input_room F K e j _ hn)
        (by
          intro i
          apply call_clock F K e j
          have hs := (blockSize_bounds (jobLength F j) i).2
          omega)
      obtain ⟨c, hc, hco⟩ := FramedCells.framed_runs _ hb
      refine ⟨c, prepCost F onset K e j, ?_, ?_, le_rfl⟩
      · simp only [ctxOf, first_leading]
        exact hc
      · rw [hco, hout]
        rfl)
    (by
      intro j
      rw [first_leading]
      simp only [sizes, Sz.W, one_mul]
      exact Nat.succ_le_of_lt (by positivity))

noncomputable def executionWordFunction (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (K e : ℕ)
    (W : WordFunction (TotalSourceRequest F) (fun p => decoderInput F p.1 p.2)
      (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p)))
      (fun p => K * ((decoderInput F p.1 p.2).length + 1) ^ e))
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    WordFunction (Job F onset) (middle F) (jobOutput F D)
      (fun j => langBudget (DecoderRunAlgorithm.callee F D K e W) (sizes onset K e) 12 0
        (middle F j) (runCost F onset K e j)) :=
  wordFunction_of_lang (middle F) (jobOutput F D) (DecoderRunAlgorithm.callee F D K e W)
    (sizes onset K e) DecoderRunAlgorithm.script (runCost F onset K e)
    (by
      intro j
      obtain ⟨b, hb, hout⟩ := DecoderRunAlgorithm.runs F D K e W
        ((sizes onset K e).W (L F j)) ((sizes onset K e).Lk (L F j)) ((sizes onset K e).Bk (L F j))
        (L F j) (workOf F j) (run_capacity F K e j (hmessage j))
        (by
          intro p hp
          have hs := source_word_le F j (hmessage j) p hp
          exact ⟨input_room F K e j _ hs, call_clock F K e j _ hs⟩)
      refine ⟨b, runCost F onset K e j, ?_, ?_, le_rfl⟩
      · simp only [ctxOf, middle_leading]
        exact hb
      · exact hout.trans (work_output F D j))
    (by
      intro j
      rw [middle_leading]
      simp only [sizes, Sz.W, one_mul]
      exact Nat.succ_le_of_lt (by positivity))

theorem size_polynomials (F : BinaryFamily) (onset K e : ℕ) :
    Bound (measure F) (fun j : Job F onset => (sizes onset K e).W (L F j)) ∧
    Bound (measure F) (fun j : Job F onset => (sizes onset K e).Lk (L F j)) ∧
    Bound (measure F) (fun j : Job F onset => (sizes onset K e).Bk (L F j)) := by
  have hs := allocation_poly F onset
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sizes, Sz.W, one_mul] using mul hs (constant (cutoff onset + 100))
  · simpa only [sizes, Sz.Lk, one_mul, mul_one] using hs
  · simpa only [sizes, Sz.Bk, ← pow_mul, Nat.mul_comm e] using mul (pow hs e) (constant K)

theorem bit_lengths_poly (F : BinaryFamily) (onset : ℕ) :
    Bound (measure F) (fun j : Job F onset => (jobBits F j).length) ∧
    Bound (measure F) (fun j : Job F onset => (jobLength F j).bits.length) := by
  constructor
  all_goals
    apply mono self
    intro j
    dsimp [measure]
    rw [word_length]
    omega

theorem message_poly (F : BinaryFamily) (onset : ℕ)
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    Bound (measure F) (jobLength F (onset := onset)) := mono (bit_lengths_poly F onset).1 hmessage

theorem payload_poly (F : BinaryFamily) (onset : ℕ)
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    Bound (measure F) (fun j : Job F onset => (payload F (workOf F j)).length) := by
  apply mono (add (add (mul (constant 4) (message_poly F onset hmessage))
    (mul (constant 2) (bit_lengths_poly F onset).1)) (constant 13))
  exact payload_length F

theorem first_input_poly (F : BinaryFamily) (onset : ℕ) :
    Bound (measure F) (fun j : Job F onset => (firstInput F j).length) := by
  have hp := add (add (prefix_poly F onset) (constant 1)) (self (measure := measure F))
  simpa only [firstInput, LengthPreparation.prepared, List.length_append, List.length_replicate,
    List.length_cons, L, measure, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem middle_poly (F : BinaryFamily) (onset : ℕ)
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    Bound (measure F) (fun j : Job F onset => (middle F j).length) := by
  have hp := add (add (prefix_poly F onset) (constant 1)) (payload_poly F onset hmessage)
  simpa only [middle, input, List.length_append, List.length_replicate, List.length_cons,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem preparationBudget_poly (F : BinaryFamily) (onset K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e))
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    Bound (measure F) (fun j => langBudget (EncoderAlgorithm.callee F onset K e W) (sizes onset K e) 12 0
      (firstInput F j) (prepCost F onset K e j)) := by
  obtain ⟨hW, hI, hB⟩ := size_polynomials F onset K e
  have hL := prefix_poly F onset
  have hn := message_poly F onset hmessage
  obtain ⟨hbits, hmeta⟩ := bit_lengths_poly F onset
  have hc : Bound (measure F) (prepCost F onset K e) := by
    change Bound (measure F) (fun j => 3 * (1000 * (L F j + (jobLength F j).bits.length + jobLength F j +
      (jobBits F j).length + cutoff onset + (sizes onset K e).Lk (L F j) + (sizes onset K e).Bk (L F j) + 1)) + 2)
    exact add (mul (constant 3) (mul (constant 1000)
      (add (add (add (add (add (add (add hL hmeta) hn) hbits) (constant (cutoff onset))) hI) hB) (constant 1))))
      (constant 2)
  apply language
  · simpa only [first_leading] using hL
  · simpa only [first_leading] using hW
  · simpa only [first_leading] using hI
  · simpa only [first_leading] using hB
  · exact first_input_poly F onset
  · exact hc

theorem executionBudget_poly (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (K e : ℕ)
    (W : WordFunction (TotalSourceRequest F) (fun p => decoderInput F p.1 p.2)
      (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p)))
      (fun p => K * ((decoderInput F p.1 p.2).length + 1) ^ e))
    (hmessage : ∀ j : Job F onset, jobLength F j ≤ (jobBits F j).length) :
    Bound (measure F) (fun j => langBudget (DecoderRunAlgorithm.callee F D K e W) (sizes onset K e) 12 0
      (middle F j) (runCost F onset K e j)) := by
  obtain ⟨hW, hI, hB⟩ := size_polynomials F onset K e
  have hL := prefix_poly F onset
  have hP := payload_poly F onset hmessage
  have hc : Bound (measure F) (runCost F onset K e) := by
    change Bound (measure F) (fun j => 1000 * (L F j + (payload F (workOf F j)).length +
      (sizes onset K e).Lk (L F j) + (sizes onset K e).Bk (L F j) + 1))
    exact mul (constant 1000) (add (add (add (add hL hP) hI) hB) (constant 1))
  apply language
  · simpa only [middle_leading] using hL
  · simpa only [middle_leading] using hW
  · simpa only [middle_leading] using hI
  · simpa only [middle_leading] using hB
  · exact middle_poly F onset hmessage
  · exact hc

end NearCubicGates.Adapters.Code.DecoderMachine
