import SourceAdapters.Amplification.DispUnary
import SourceAdapters.Joins.STVEncoderTable

/-!
# The output word of the amplifier in each regime (A05, `app:sources`, "Full-range amplification interface")

`truthTableWord (ampG …)` on the request `(n, f)` is: `[false, false]` (constant, arity 0) when `S(n) = 0` or
`S(n) ≥ U(n)`; the parity table on `S(n)+1` bits for `n < n0`; the parity table on `n+1` bits when `S(n) ≤ n^c`;
and otherwise the X9 output word `encoderOutput C ⟨dyadicExp c S(n), n, f⟩`. The parity table is written with the
Hadamard bit of `2^s − 1` (`parityWord`, `par_table`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification.Enc

open Finset NearCubicWires NearCubicWires.ExecutableInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma39
open NearCubicWires.RepairSource (AmplifierOutput)

/-- The framed arity and the parity table on `s` bits. -/
def parityWord (s : ℕ) : List Bool :=
  frame s.bits ++ (List.range (2 ^ s)).map fun c => hadBit s (2 ^ s - 1) c

theorem sum_bitZ {s : ℕ} (c : ℕ) :
    (∑ j : Fin s, bitZ (c.testBit j)) = (((range s).filter fun j => c.testBit j).card : ZMod 2) := by
  rw [Finset.card_filter, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold bitZ; split_ifs <;> simp

theorem zmod2_eq_one (m : ℕ) : ((m : ZMod 2) = 1) ↔ m % 2 = 1 := by
  rw [show (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) by simp, ZMod.natCast_eq_natCast_iff']

theorem par_table (s : ℕ) :
    boolFunctionTable (par s) = (List.range (2 ^ s)).map fun c => hadBit s (2 ^ s - 1) c := by
  unfold boolFunctionTable
  refine List.map_congr_left fun c _ => ?_
  unfold par hadBit
  rw [sum_bitZ]
  have e : ((range s).filter fun j => (2 ^ s - 1).testBit j && c.testBit j) = (range s).filter fun j => c.testBit j := by
    ext j
    simp only [mem_filter, mem_range, Bool.and_eq_true, and_congr_right_iff]
    intro hj
    rw [Nat.testBit_two_pow_sub_one]; simp [hj]
  rw [e]
  exact decide_eq_decide.mpr (zmod2_eq_one _)

theorem amp_zero (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) (h0 : S n = 0) :
    truthTableWord (ampG C A a c hc S) ⟨n, f⟩ = [false, false] := by
  have e : ampG C A a c hc S n f = ⟨0, fun _ => false⟩ := by unfold ampG; rw [if_pos h0]
  unfold truthTableWord; simp only; rw [e]; rfl

theorem amp_small (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) (h0 : S n ≠ 0)
    (h1 : n < ampOnset A a) : truthTableWord (ampG C A a c hc S) ⟨n, f⟩ = parityWord (S n + 1) := by
  have e : ampG C A a c hc S n f = ⟨S n + 1, par (S n + 1)⟩ := by unfold ampG; rw [if_neg h0, if_pos h1]
  unfold truthTableWord parityWord; simp only; rw [e]; simp only; rw [par_table]

theorem amp_poly (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) (h0 : S n ≠ 0)
    (h1 : ¬ n < ampOnset A a) (h2 : S n ≤ n ^ c) :
    truthTableWord (ampG C A a c hc S) ⟨n, f⟩ = parityWord (n + 1) := by
  have e : ampG C A a c hc S n f = ⟨n + 1, par (n + 1)⟩ := by unfold ampG; rw [if_neg h0, if_neg h1, if_pos h2]
  unfold truthTableWord parityWord; simp only; rw [e]; simp only; rw [par_table]

theorem amp_big (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) (h0 : S n ≠ 0)
    (h1 : ¬ n < ampOnset A a) (h2 : ¬ S n ≤ n ^ c) (h3 : 2 ^ (n + 3) ≤ S n) :
    truthTableWord (ampG C A a c hc S) ⟨n, f⟩ = [false, false] := by
  have e : ampG C A a c hc S n f = ⟨0, fun _ => false⟩ := by
    unfold ampG; rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]
  unfold truthTableWord; simp only; rw [e]; rfl

theorem amp_mid (C A a c : ℕ) (hc : 1 ≤ c) (S : ℕ → ℕ) (n : ℕ) (f : BoolFunction n) (h0 : S n ≠ 0)
    (h1 : ¬ n < ampOnset A a) (h2 : ¬ S n ≤ n ^ c) (h3 : ¬ 2 ^ (n + 3) ≤ S n) :
    truthTableWord (ampG C A a c hc S) ⟨n, f⟩ = Joins.encoderOutput C ⟨dyadicExp c (S n) hc, n, f⟩ := by
  have e : ampG C A a c hc S n f = Joins.stvOutput C n (dyadicExp c (S n) hc) f := by
    unfold ampG; rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]; rfl
  unfold truthTableWord Joins.encoderOutput; simp only; rw [e]

end NearCubicGates.Adapters.Amplification.Enc
