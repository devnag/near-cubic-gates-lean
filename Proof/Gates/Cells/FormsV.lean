import Proof.Gates.Cells.Width

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

theorem wr_full (L W : List ℕ) (h : L.length ≤ W.length) : wr L 0 W = W := by
  unfold wr; simp [List.drop_eq_nil_of_le h]

theorem wr_length_eq (L W : List ℕ) : (wr L 0 W).length = max L.length W.length := by
  unfold wr; simp; omega

theorem drop_eq_len {L X : List ℕ} {b : ℕ} (h : L.drop b = X) (hX : X ≠ []) : b + X.length = L.length := by
  have h1 := congrArg List.length h
  rw [List.length_drop] at h1
  have : X.length ≠ 0 := by simpa using hX
  omega

theorem sum_le_of_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.sum ≤ l.length * B := by
  have := List.sum_le_card_nsmul l B h
  simpa using this

section V
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

theorem coeffs_le_len (ρ : ℕ) : (circ c ρ).coeffs.length ≤ (cellN c p wt).length := by
  have h1 : (circ c ρ).coeffs.length ≤ (circN (circ c ρ)).length := by
    simp only [circN, List.length_append, List.length_singleton, flatMap_intN_length, flatMap_gateN_length,
      List.length_map]; omega
  have h2 : (circN (circ c ρ)).length ≤ (callN c).length := by
    unfold circ; split_ifs <;> simp [callN] <;> omega
  have h3 : (callN c).length ≤ (cellN c p wt).length := by simp [cellN]
  omega

include hadm hs hw in
theorem nfactors_eq : p.factors.length = p.J - 1 := by rw [hs.factors_eq]; simp [chainFactors]

include hadm hs hw in
theorem blocksAll_ne : blocksAll wt.coef (roleCount c.kind) p.J ≠ [] := by
  have hJ := hs.J_pos
  have hr := roleCount_pos c.kind
  obtain ⟨J', hJ'⟩ : ∃ J', p.J = J' + 1 := ⟨p.J - 1, by omega⟩
  obtain ⟨r', hr'⟩ : ∃ r', roleCount c.kind = r' + 1 := ⟨roleCount c.kind - 1, by omega⟩
  unfold blocksAll blocksOf
  rw [hJ', hr']
  simp [List.range_succ]

end V

section Sizes
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)
  (Big Wd : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big) (hWd : 3 * Big + 6 * c.n + 20 ≤ Wd)

theorem pw_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

include hBig hWd in
theorem sz_big {x : ℕ} (hx : x ∈ cellN c p wt) : x < 2 ^ Wd :=
  lt_of_lt_of_le (lt_of_big c p wt hBig hx) (pw_mono (by omega))

include hadm hs hw hWd in
theorem sz_len : (cellN c p wt).length < 2 ^ Wd :=
  lt_of_lt_of_le (cellN_len_lt c p wt hadm hs w hw) (pw_mono (by omega))

include hBig hWd in
theorem sz_gate (r : ℕ) (g : NormalizedThresholdGate c.n) (hg : g ∈ (circ c r).gates) :
    ((List.ofFn g.weight).map Int.natAbs).sum + g.threshold.natAbs < 2 ^ Wd := by
  have h1 := sum_le_of_le ((List.ofFn g.weight).map Int.natAbs) (2 ^ Big) (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact (lt_of_big c p wt hBig (weight_mem c p wt r hg k)).le)
  simp only [List.length_map, List.length_ofFn] at h1
  have h2 := lt_of_big c p wt hBig (threshold_mem c p wt r hg)
  have h3 : (c.n + 1) * 2 ^ Big ≤ 2 ^ c.n * 2 ^ Big := Nat.mul_le_mul_right _ Nat.lt_two_pow_self
  have h4 : 2 ^ c.n * 2 ^ Big < 2 ^ Wd := by
    rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h5 : (c.n + 1) * 2 ^ Big = c.n * 2 ^ Big + 2 ^ Big := by ring
  omega

include hBig hWd in
theorem sz_coeffs (r : ℕ) : ((circ c r).coeffs.map Int.natAbs).sum < 2 ^ Wd := by
  have h1 := sum_le_of_le ((circ c r).coeffs.map Int.natAbs) (2 ^ Big) (by
    intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact (lt_of_big c p wt hBig (coeff_mem c p wt r ha)).le)
  rw [List.length_map] at h1
  have h2 := lt_of_big c p wt hBig (coeffs_len_mem c p wt r)
  have h3 : (circ c r).coeffs.length * 2 ^ Big ≤ 2 ^ Big * 2 ^ Big := Nat.mul_le_mul_right _ h2.le
  have h4 : 2 ^ Big * 2 ^ Big < 2 ^ Wd := by
    rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

include hadm hs hw hBig in
theorem sz_coef (s ρ : ℕ) (hs' : s < p.J) (hρ : ρ < roleCount c.kind) :
    ((wt.coef s ρ).map Int.natAbs).sum ≤ 2 ^ (2 * Big) := by
  obtain ⟨hl1, hl2⟩ := coef_bounds c p hadm wt w hw s ρ hs' hρ
  have hWB : p.W < 2 ^ Big := lt_of_big c p wt hBig (W_mem c p wt)
  have hW : p.W = c.W := hs.W_eq
  have h1 := sum_le_of_le ((wt.coef s ρ).map Int.natAbs) c.W (by
    intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx; exact hl2 a ha)
  rw [List.length_map] at h1
  have h2 : (wt.coef s ρ).length * c.W ≤ 2 ^ Big * 2 ^ Big := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 2 ^ Big * 2 ^ Big = 2 ^ (2 * Big) := by rw [← pow_add]; ring_nf
  omega

include hWd in
theorem sz_kb : 2 ^ (2 * Big) + 2 ^ Big * 2 ^ (2 * Big) < 2 ^ Wd := by
  have h1 : 2 ^ Big * 2 ^ (2 * Big) = 2 ^ (3 * Big) := by rw [← pow_add]; ring_nf
  have h2 : 2 ^ (2 * Big) ≤ 2 ^ (3 * Big) := pw_mono (by omega)
  have h3 : 2 ^ (3 * Big) * 2 ^ 2 ≤ 2 ^ Wd := by
    rw [← pow_add]; exact pw_mono (by omega)
  have h4 : 0 < 2 ^ (3 * Big) := by positivity
  omega

include hw in
theorem sz_cf (s r : ℕ) (hs' : s < p.J) (hr : r < roleCount c.kind) :
    (wt.coef s r).length ≤ (circ c r).coeffs.length := by
  obtain ⟨vs, hvs, -⟩ := coef_shape c p wt w hw s r hs' hr
  rw [hvs, List.length_map, List.length_zip]; exact Nat.min_le_left _ _

end Sizes

end NearCubicGates.Close.Cells
