import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine

/-- The bit bound of every cell-input field. -/
def bigOf (B1 B2 n : ℕ) : ℕ := 2 ^ 10 * (n + 1) ^ (B1 + B2 + 8)

theorem cellN_bits_le {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) :
    ∀ x ∈ cellN r.c r.p r.wt, natBitLength x ≤ bigOf B1 B2 r.c.n := by
  intro x hx
  unfold bigOf
  obtain ⟨w, hw⟩ := r.hw
  have hadm := r.adm
  have hs := selectParams_spec cT (header r.c) r.p r.hp
  set c := r.c
  set N := c.n + 1 with hN
  have hN1 : 1 ≤ N := by omega
  set Q := N ^ (B1 + B2 + 8) with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have q1 : N ≤ Q := by simpa using pw_le hN1 (show 1 ≤ B1 + B2 + 8 by omega)
  have q2 : N ^ 2 ≤ Q := pw_le hN1 (by omega)
  have q4 : N ^ 4 ≤ Q := pw_le hN1 (by omega)
  have qB : N ^ B2 ≤ Q := pw_le hN1 (by omega)
  have hW := hadm.2.2.2.2.2.2.1
  have hn4 : c.n ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
  simp only [cellN, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · have := call_bits c hadm x hx; rw [← hN] at this; omega
  · have := params_bits c r.p hadm hs x hx; rw [← hN] at this; omega
  · have := wit_bits c r.p hadm hs r.wt w hw x hx; omega

theorem vecs_length (q : ℕ) : ∀ d, (vecs q d).length = q ^ d
  | 0 => by simp [vecs]
  | d + 1 => by
    simp only [vecs, List.length_flatMap, List.length_map, vecs_length q d]
    simp [pow_succ, mul_comm]

theorem sum_sort_eq (s : Finset ℕ) (f : ℕ → ℕ) : ((s.sort (· ≤ ·)).map f).sum = ∑ q ∈ s, f q := by
  rw [((Finset.sort_perm_toList s (· ≤ ·)).map f).sum_eq, Finset.sum_map_toList]

/-- **The request count.** -/
theorem reqIds_length (c : Call) (p : Params) : (reqIds c p).length = requestCount c p := by
  unfold reqIds requestCount formCount
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_range,
    List.length_cons, List.length_nil]
  simp only [sum_sort_eq, List.map_const', List.sum_replicate, smul_eq_mul, vecs_length, List.length_range]
  have : ∀ x : ℕ, x ^ (roleCount c.kind * p.J) * x ^ roleCount c.kind = x ^ (roleCount c.kind * (p.J + 1)) := by
    intro x; rw [← pow_add, show roleCount c.kind * p.J + roleCount c.kind = roleCount c.kind * (p.J + 1) by ring]
  simp only [this]

end NearCubicGates.Close.CellsPack
