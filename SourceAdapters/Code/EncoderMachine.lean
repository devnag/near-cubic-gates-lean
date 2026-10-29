import SourceAdapters.Code.EncoderAlgorithm
import SourceAdapters.Code.PolynomialCosts

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid ordinary-machine packaging of the entire encoder,
including target input conversion and a polynomial encoded-length bound. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.EncoderMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code
open EncoderAlgorithm Parsing PolynomialCosts

def sizes (onset K e : ℕ) : Sz := ⟨cutoff onset + 8, 1, 1, 1, K, e⟩

def input (p : MessageRequest) : List Bool := preparedWord (p.1.bits, List.ofFn p.2.val)

def cost (onset K e : ℕ) (p : MessageRequest) : ℕ :=
  languageCost onset p.1.bits.length p.1 ((sizes onset K e).Lk p.1.bits.length)
    ((sizes onset K e).Bk p.1.bits.length)

theorem capacity (onset K e : ℕ) (p : MessageRequest) :
    2 * p.1 + 6 + cutoff onset < 2 ^ ((sizes onset K e).W p.1.bits.length) := by
  have h := Nat.lt_size_self p.1
  rw [← Nat.size_eq_bits_len] at h
  have hs : 1 ≤ 2 ^ p.1.bits.length := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left (cutoff onset) hs
  have hw : 2 * p.1 + 6 + cutoff onset ≤ (sizes onset K e).W p.1.bits.length := by
    simp only [sizes, Sz.W, one_mul]
    nlinarith
  exact hw.trans_lt Nat.lt_two_pow_self

theorem room (onset K e : ℕ) (p : MessageRequest) : p.1 ≤ (sizes onset K e).Lk p.1.bits.length := by
  have h := Nat.lt_size_self p.1
  rw [← Nat.size_eq_bits_len] at h
  simpa [sizes, Sz.Lk] using h.le

theorem clock (onset K e : ℕ) (p : MessageRequest) (i : Fin 3) :
    K * (blockSize p.1 i + 1) ^ e ≤ (sizes onset K e).Bk p.1.bits.length := by
  have h := Nat.lt_size_self p.1
  rw [← Nat.size_eq_bits_len] at h
  have hb := (blockSize_bounds p.1 i).2
  have hs : blockSize p.1 i + 1 ≤ 2 ^ p.1.bits.length := by omega
  have hp := Nat.mul_le_mul_left K (Nat.pow_le_pow_left hs e)
  simpa [sizes, Sz.Bk, ← pow_mul, Nat.mul_comm] using hp

noncomputable def preparedWordFunction (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F) (K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e)) :
    WordFunction MessageRequest input (fun p => List.ofFn ((patchedFamily F D).enc p.1 p.2.val))
      (fun p => langBudget (callee F onset K e W) (sizes onset K e) 12 0 (input p) (cost onset K e p)) :=
  wordFunction_of_lang input (fun p => List.ofFn ((patchedFamily F D).enc p.1 p.2.val))
    (callee F onset K e W) (sizes onset K e) (script onset) (cost onset K e)
    (by
      intro p
      obtain ⟨b, hb, hout⟩ := EncoderAlgorithm.runs F D hlinear K e W
        ((sizes onset K e).W p.1.bits.length) ((sizes onset K e).Lk p.1.bits.length)
        ((sizes onset K e).Bk p.1.bits.length) p.1.bits.length p.1 p.2.val
        (capacity onset K e p) (room onset K e p) (clock onset K e p)
      refine ⟨b, cost onset K e p, ?_, hout, le_rfl⟩
      simp only [ctxOf, input, preparedWord_leadOnes]
      simpa only [preparedWord, cost] using hb)
    (by
      intro p
      simp only [input, preparedWord_leadOnes, sizes, Sz.W, one_mul]
      exact Nat.succ_le_of_lt (by positivity))

theorem budget_poly (F : BinaryFamily) (onset K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e)) :
    Bound (fun p : MessageRequest => (messageWord p).length)
      (fun p => langBudget (callee F onset K e W) (sizes onset K e) 12 0 (input p) (cost onset K e p)) := by
  let measure := fun p : MessageRequest => (messageWord p).length
  have hn : Bound measure (fun p => p.1) := mono self message_length_le_word
  have hL : Bound measure (fun p => p.1.bits.length) := mono self (fun p => by
    dsimp [measure]
    rw [messageWord_length]
    omega)
  have hS : Bound measure (fun p => 2 ^ p.1.bits.length) := by
    refine ⟨2, 1, fun p => ?_⟩
    have h := two_pow_bits_length_le p.1
    have hm := message_length_le_word p
    simp only [pow_one, measure]
    omega
  have hW : Bound measure (fun p => (sizes onset K e).W p.1.bits.length) := by
    simpa only [sizes, Sz.W, one_mul] using mul hS (constant (cutoff onset + 8))
  have hI : Bound measure (fun p => (sizes onset K e).Lk p.1.bits.length) := by
    simpa only [sizes, Sz.Lk, one_mul, mul_one] using hS
  have hB : Bound measure (fun p => (sizes onset K e).Bk p.1.bits.length) := by
    simpa only [sizes, Sz.Bk, ← pow_mul, Nat.mul_comm e] using mul (pow hS e) (constant K)
  have hw : Bound measure (fun p => (input p).length) := by
    refine ⟨2, 1, fun p => ?_⟩
    simp only [input, preparedWord, List.length_append, List.length_replicate,
      List.length_cons, frame_length, List.length_ofFn, measure, messageWord_length, pow_one]
    omega
  have hcost : Bound measure (cost onset K e) := by
    change Bound measure (fun p => 1000 * (p.1.bits.length + p.1 + cutoff onset +
      (sizes onset K e).Lk p.1.bits.length + (sizes onset K e).Bk p.1.bits.length + 1))
    repeat' first
      | exact hL
      | exact hn
      | exact hI
      | exact hB
      | exact constant _
      | apply add
      | apply mul
  apply language
  · simpa only [input, preparedWord_leadOnes] using hL
  · simpa only [input, preparedWord_leadOnes] using hW
  · simpa only [input, preparedWord_leadOnes] using hI
  · simpa only [input, preparedWord_leadOnes] using hB
  · exact hw
  · exact hcost

/-- The full ordinary encoder on the target serialization. Its source
algorithm is an actual framed word function; no target machine is assumed. -/
theorem wordFunction_of_source (hX8 : NearCubicGates.Adapters.Joins.CappedWordRun)
    (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius)
    (hlinear : IsLinear F) (A : EfficientEncoder F onset) :
    ∃ K e : ℕ, Nonempty (WordFunction MessageRequest messageWord
      (fun p => List.ofFn ((patchedFamily F D).enc p.1 p.2.val))
      (fun p => K * ((messageWord p).length + 1) ^ e)) := by
  obtain ⟨C, d, W⟩ := framed_encoder_wordFunction hX8 F A
  obtain ⟨W⟩ := W
  let Q := preparedWordFunction F D hlinear C d W
  let P := messagePreparationWordFunction
  let R := composeFramed P Q
  obtain ⟨K, e, h⟩ := composeFramed_budget_poly messageWord
    (fun p => preparationBudget (p.1.bits, List.ofFn p.2.val))
    (fun p => langBudget (callee F onset C d W) (sizes onset C d) 12 0 (input p) (cost onset C d p))
    messagePreparationBudget_poly (budget_poly F onset C d W)
  exact ⟨K, e, ⟨R.enlargeBudget h⟩⟩

end NearCubicGates.Adapters.Code.EncoderMachine
