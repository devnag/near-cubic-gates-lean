import SourceAdapters.Routing.TermsMachinePrefixStep

/-! Numerical capacities for the coordinate-prefix printer. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open NearCubicWires NearCubicWires.CanonicalBinary
open ShortPCP.Machines.FL

/-- All capacities concern literal words, loop counts, or gate indices. -/
structure Bounds (G : Glob) (f m start : ℕ) : Prop where
  f_pos : 1 ≤ f
  m_pos : 1 ≤ m
  m_N : m ≤ G.N
  K_N : G.K ≤ G.N
  coefficient_index : m*m*f ≤ G.cap
  word_power : 2^f ≤ G.cap
  gate_count : start+3*m*m+2*m ≤ G.cap
  bit_budget : natBitLength (max (start+3*m*m+2*m) (2^f)) + 2 ≤ G.K

variable {G : Glob} {f m start : ℕ}

theorem Bounds.three_cap (h : Bounds G f m start) : 3 ≤ G.cap := by
  have := h.gate_count
  have := h.m_pos
  nlinarith

theorem Bounds.bits_gate (h : Bounds G f m start) {v : ℕ}
    (hv : v ≤ start+3*m*m+2*m) : natBitLength v + 2 ≤ G.K := by
  have hm : natBitLength v ≤ natBitLength (max (start+3*m*m+2*m) (2^f)) :=
    Nat.add_le_add_right (Nat.log_mono_right (hv.trans (Nat.le_max_left _ (2^f)))) 1
  exact (Nat.add_le_add_right hm 2).trans h.bit_budget

theorem Bounds.bits_word (h : Bounds G f m start) {v : ℕ}
    (hv : v ≤ 2^f) : natBitLength v + 2 ≤ G.K := by
  have hm : natBitLength v ≤ natBitLength (max (start+3*m*m+2*m) (2^f)) :=
    Nat.add_le_add_right (Nat.log_mono_right (hv.trans (Nat.le_max_right (start+3*m*m+2*m) _))) 1
  exact (Nat.add_le_add_right hm 2).trans h.bit_budget

theorem Bounds.bits_tag (h : Bounds G f m start) {v : ℕ} (hv : v ≤ 3) :
    natBitLength v + 2 ≤ G.K := by
  apply h.bits_gate
  have := h.m_pos
  nlinarith

theorem Bounds.power_index (_h : Bounds G f m start) {r : ℕ} (hr : r < m) :
    start+r ≤ start+3*m*m+2*m := by omega

theorem Bounds.row_end (_h : Bounds G f m start) {a : ℕ} (ha : a < m) :
    start+m+a*(3*m+1)+3*m+1 ≤ start+3*m*m+2*m := by
  have hmul := Nat.mul_le_mul_right (3*m+1) (show a+1 ≤ m by omega)
  nlinarith

theorem word_getD_le (f : ℕ) (cs : List ℕ) (hcs : ∀ c ∈ cs, c < 2^f) (j : ℕ) :
    cs.getD j 0 ≤ 2^f := by
  by_cases hj : j < cs.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact Nat.le_of_lt (hcs _ (List.getElem_mem hj))
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
