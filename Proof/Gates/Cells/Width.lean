import Proof.Gates.Cells.Forms8

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

section W
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
theorem cellN_len : (cellN c p wt).length ≤ 70 * (c.n + 1) ^ 5 := by
  set N := c.n + 1 with hN
  have hN5 : 5 ≤ N := by have := hadm.1; omega
  have hN1 : 1 ≤ N := by omega
  have hW := hadm.2.2.2.2.2.2.1
  have h1 := call_len c hadm
  have h2 := params_len c p hadm hs
  have h3 := wit_len c p hadm hs wt w hw
  have hJ := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have e1 : (2 * c.W) ≤ 4 * N ^ 4 := by omega
  have e2 : p.J * 2 * (1 + 2 * c.W) ≤ 2 * N * (1 + 4 * N ^ 4) := by
    have := Nat.mul_le_mul (show p.J * 2 ≤ 2 * N by omega) (show 1 + 2 * c.W ≤ 1 + 4 * N ^ 4 by omega)
    exact this
  rw [← hN] at h1 h2
  have e3 : N ^ 5 = N * N ^ 4 := by ring
  have e4 : 5 * N ^ 4 ≤ N ^ 5 := by rw [e3]; exact Nat.mul_le_mul_right _ hN5
  have e5 : N ≤ N ^ 4 := by simpa using pw_le hN1 (show 1 ≤ 4 by omega)
  have e6 : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
  have e7 : 2 * N * (1 + 4 * N ^ 4) = 2 * N + 8 * N ^ 5 := by ring
  simp only [cellN, List.length_append]
  omega

include hadm hs hw in
theorem cellN_len_lt : (cellN c p wt).length < 2 ^ (5 * c.n + 7) := by
  have h := cellN_len c p wt hadm hs w hw
  have h1 : c.n + 1 ≤ 2 ^ c.n := Nat.lt_two_pow_self
  have h2 : (c.n + 1) ^ 5 ≤ (2 ^ c.n) ^ 5 := Nat.pow_le_pow_left h1 5
  have h3 : (2 ^ c.n) ^ 5 * 2 ^ 7 = 2 ^ (5 * c.n + 7) := by rw [← pow_mul, ← pow_add]; ring_nf
  have h4 : 0 < (2 ^ c.n) ^ 5 := by positivity
  omega

theorem lt_of_big {Big x : ℕ} (hB : ∀ y ∈ cellN c p wt, natBitLength y ≤ Big) (hx : x ∈ cellN c p wt) :
    x < 2 ^ Big :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) x)
    (Nat.pow_le_pow_right (by norm_num) (by have := hB x hx; unfold natBitLength at this; omega))

theorem mem_cellN_call {x : ℕ} (hx : x ∈ callN c) : x ∈ cellN c p wt := by
  simp only [cellN, List.mem_append]; exact Or.inl (Or.inl hx)

theorem mem_cellN_params {x : ℕ} (hx : x ∈ paramsN p) : x ∈ cellN c p wt := by
  simp only [cellN, List.mem_append]; exact Or.inl (Or.inr hx)

theorem mem_callN_circ (r : ℕ) {x : ℕ} (hx : x ∈ circN (circ c r)) : x ∈ callN c := by
  unfold circ at hx
  split_ifs at hx <;> simp [callN, hx]

theorem gates_len_mem (r : ℕ) : (circ c r).gates.length ∈ cellN c p wt :=
  mem_cellN_call c p wt (mem_callN_circ c r (by simp [circN]))

theorem coeffs_len_mem (r : ℕ) : (circ c r).coeffs.length ∈ cellN c p wt :=
  mem_cellN_call c p wt (mem_callN_circ c r (by simp [circN]))

theorem coeff_mem (r : ℕ) {a : ℤ} (ha : a ∈ (circ c r).coeffs) : a.natAbs ∈ cellN c p wt := by
  have h : a.natAbs ∈ circN (circ c r) := by
    simp only [circN, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨a, ha, by simp [intN]⟩))
  exact mem_cellN_call c p wt (mem_callN_circ c r h)

theorem weight_mem (r : ℕ) {g : NormalizedThresholdGate c.n} (hg : g ∈ (circ c r).gates) (i : Fin c.n) :
    (g.weight i).natAbs ∈ cellN c p wt := by
  have h1 : (g.weight i).natAbs ∈ gateN g := by
    simp only [gateN, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨g.weight i, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [intN]⟩)
  have h : (g.weight i).natAbs ∈ circN (circ c r) := by
    simp only [circN, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, h1⟩))))
  exact mem_cellN_call c p wt (mem_callN_circ c r h)

theorem threshold_mem (r : ℕ) {g : NormalizedThresholdGate c.n} (hg : g ∈ (circ c r).gates) :
    g.threshold.natAbs ∈ cellN c p wt := by
  have h1 : g.threshold.natAbs ∈ gateN g := by simp [gateN, intN]
  have h : g.threshold.natAbs ∈ circN (circ c r) := by
    simp only [circN, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, h1⟩))))
  exact mem_cellN_call c p wt (mem_callN_circ c r h)

theorem n_mem : c.n ∈ cellN c p wt := mem_cellN_call c p wt (by simp [callN])

theorem J_mem : p.J ∈ cellN c p wt := mem_cellN_params c p wt (by simp [paramsN])

theorem W_mem : p.W ∈ cellN c p wt := mem_cellN_params c p wt (by simp [paramsN])

theorem factor_mem {f : ℕ} (hf : f ∈ p.factors) : f ∈ cellN c p wt := mem_cellN_params c p wt (by simp [paramsN, hf])

theorem nfactors_mem : p.factors.length ∈ cellN c p wt := mem_cellN_params c p wt (by simp [paramsN])

end W

end NearCubicGates.Close.Cells
