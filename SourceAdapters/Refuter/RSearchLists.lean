import SourceAdapters.Refuter.Assembly
import Proof.MachineModel.OrdinarySignedSortKey

/-!
# The words R writes, as lists (input 7, R: record and binary-field shapes)

Paper anchor: the records `x_i = ⟨M,N,w_i⟩ = 1^M 0 1^{N−M−2−g} 0 w_i` of CLW20 §4.1 (proof of `cor:framed-refuter`),
written by R as its output (proof of `lem:multitape-refuter`) and inside every membership query; the
interval endpoint `high` of a query is written as `high.bits` (join X5(b) `CNFCompilationRequest.word`,
).

* `record_ofFn`: at the lengths where the record is valid (`machineIndex M + 2 + ⌊N/16⌋ ≤ N`, all
  large `N`), `List.ofFn (record M N i)` is the literal concatenation R emits.
* `binary_eq_bits`: a number below `2^W` stored by L's word arithmetic (`SignedSortKey.binary W q`,
  little-endian, fixed width) is `q.bits` followed by blanks — so R emits `q.bits` by copying the
  stored width up to the last `1`.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.RepairSource

set_option autoImplicit false

theorem record_ofFn (M : OrdinaryWeakMachine) (N i : ℕ) (h : machineIndex M + 2 + N / 16 ≤ N) :
    List.ofFn (record M N i) =
      List.replicate (machineIndex M) true ++ false ::
        (List.replicate (N - N / 16 - machineIndex M - 2) true ++ false ::
          List.ofFn (unrank (N / 16) i)) := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    have hj : j < N := by simpa using h1
    simp only [List.getElem_ofFn, record]
    have hN : N / 16 ≤ N := Nat.div_le_self _ _
    by_cases ha : j < machineIndex M
    · rw [if_pos ha, List.getElem_append_left (by simpa using ha)]; simp
    · rw [if_neg ha, List.getElem_append_right (by simpa using ha)]
      simp only [List.length_replicate]
      by_cases hb : j = machineIndex M
      · subst hb; simp
      · rw [if_neg hb]
        obtain ⟨k, hk⟩ : ∃ k, j - machineIndex M = k + 1 := ⟨j - machineIndex M - 1, by omega⟩
        simp only [hk, List.getElem_cons_succ]
        by_cases hc : j + 1 < N - N / 16
        · rw [dif_pos hc, List.getElem_append_left (by simp only [List.length_replicate]; omega)]; simp
        · rw [dif_neg hc, List.getElem_append_right (by simp only [List.length_replicate]; omega)]
          simp only [List.length_replicate]
          by_cases hd : j + 1 = N - N / 16
          · rw [dif_pos hd]
            have : k - (N - N / 16 - machineIndex M - 2) = 0 := by omega
            simp [this]
          · rw [dif_neg hd]
            obtain ⟨l, hl⟩ : ∃ l, k - (N - N / 16 - machineIndex M - 2) = l + 1 :=
              ⟨k - (N - N / 16 - machineIndex M - 2) - 1, by omega⟩
            simp only [hl, List.getElem_cons_succ, List.getElem_ofFn]
            congr 1
            ext
            simp only
            omega

open NearCubicWires.RepairOrdinary.SignedSortKey in
theorem binary_zero (W : ℕ) : binary W 0 = List.replicate W false := by
  induction W with
  | zero => rfl
  | succ W ih => simp [binary, ih, List.replicate_succ]

open NearCubicWires.RepairOrdinary.SignedSortKey in
/-- A width-`W` little-endian word is the canonical bits followed by blanks. -/
theorem binary_eq_bits : ∀ (W q : ℕ), q < 2 ^ W →
    binary W q = q.bits ++ List.replicate (W - q.bits.length) false := by
  intro W
  induction W with
  | zero =>
    intro q hq
    have : q = 0 := by simpa using hq
    subst this; rfl
  | succ W ih =>
    intro q hq
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp [binary_zero]
    · have hd : q / 2 < 2 ^ W := by rw [pow_succ] at hq; omega
      have hbits : q.bits = (q % 2 == 1) :: (q / 2).bits := by
        have hq2 : q = Nat.bit (q % 2 == 1) (q / 2) := by
          rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [Nat.bit, h] <;> omega
        conv_lhs => rw [hq2]
        apply Nat.bits_append_bit
        intro h0
        rcases Nat.mod_two_eq_zero_or_one q with h | h
        · omega
        · simp [h]
      rw [hbits, binary, ih _ hd]
      simp only [List.length_cons, List.cons_append, Nat.add_sub_add_right]

end NearCubicGates.Adapters.Refuter
