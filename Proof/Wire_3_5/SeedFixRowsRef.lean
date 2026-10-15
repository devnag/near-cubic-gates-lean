import Proof.Wire_3_5.SamplerCond
import Proof.Wire_3_5.GaussRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.JoinElimination

/-- `λ^i` by the shift-and-xor product. -/
def accPow (p ℓ lam : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => fmulShift p ℓ (accPow p ℓ lam i) lam

/-- **The column table** of label `λ`: `x^b·λ^i` for `i < 2h`, `b < ℓ` (index `j = iℓ + b`). -/
def colTable (p ℓ twoH lam : ℕ) : List ℕ :=
  (List.range twoH).flatMap fun i => (List.range ℓ).map fun b => (lfsr p ℓ)^[b] (accPow p ℓ lam i)

theorem accPow_spec (p ℓ lam : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hlam : lam < 2 ^ ℓ) :
    ∀ i, accPow p ℓ lam i < 2 ^ ℓ ∧ rep p (accPow p ℓ lam i) = rep p lam ^ i
  | 0 => ⟨Nat.one_lt_two_pow (by omega), by simp [accPow]⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := accPow_spec p ℓ lam hp hℓ hlam i
    obtain ⟨h3, h4⟩ := fmulShift_spec p ℓ _ lam hp h1 hlam
    exact ⟨h3, by rw [accPow, h4, h2, pow_succ]⟩

theorem lfsr_iterate_spec (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) :
    ∀ b, (lfsr p ℓ)^[b] a < 2 ^ ℓ ∧ rep p ((lfsr p ℓ)^[b] a) = xRoot p ^ b * rep p a
  | 0 => ⟨ha, by simp⟩
  | b + 1 => by
    obtain ⟨h1, h2⟩ := lfsr_iterate_spec p ℓ a hp ha b
    obtain ⟨h3, h4⟩ := lfsr_spec p ℓ _ hp h1
    refine ⟨by rw [Function.iterate_succ_apply']; exact h3, ?_⟩
    rw [Function.iterate_succ_apply', h4, h2, pow_succ]
    ring

/-- **The machine's column is the generator's column** `fmul(x^b, λ^i)` (`system`'s coefficient). -/
theorem colWord_eq (p ℓ lam : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hlam : lam < 2 ^ ℓ) (i b : ℕ) (hb : b < ℓ) :
    (lfsr p ℓ)^[b] (accPow p ℓ lam i) = JoinElimination.fmul p ℓ (2 ^ b) (JoinElimination.fpow p ℓ lam i) := by
  obtain ⟨h1, h2⟩ := accPow_spec p ℓ lam hp hℓ hlam i
  obtain ⟨h3, h4⟩ := lfsr_iterate_spec p ℓ _ hp h1 b
  obtain ⟨h5, h6⟩ := fpow_spec p ℓ lam hp hℓ hlam i
  have h2b : 2 ^ b < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hb
  obtain ⟨h7, h8⟩ := fmul_spec p ℓ (2 ^ b) _ hp h2b h5
  rw [je_fmul_eq]
  apply rep_injOn p ℓ _ _ hp h3 h7
  rw [h4, h8, h2, h6, rep_two_pow]

theorem colTable_length (p ℓ twoH lam : ℕ) : (colTable p ℓ twoH lam).length = twoH * ℓ := by
  simp [colTable, List.length_flatMap, List.map_const', List.sum_replicate]

theorem colTable_getD (p ℓ lam : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ (twoH j : ℕ), j < twoH * ℓ → (colTable p ℓ twoH lam).getD j 0 = (lfsr p ℓ)^[j % ℓ] (accPow p ℓ lam (j / ℓ))
  | 0, j, hj => by simp at hj
  | twoH + 1, j, hj => by
    have hsplit : colTable p ℓ (twoH + 1) lam =
        colTable p ℓ twoH lam ++ (List.range ℓ).map fun b => (lfsr p ℓ)^[b] (accPow p ℓ lam twoH) := by
      unfold colTable
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [hsplit]
    by_cases hlt : j < twoH * ℓ
    · rw [List.getD_append _ _ _ _ (by rw [colTable_length]; exact hlt)]
      exact colTable_getD p ℓ lam hℓ twoH j hlt
    · have hge : twoH * ℓ ≤ j := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [colTable_length]; exact hge), colTable_length]
      have hb : j - twoH * ℓ < ℓ := by rw [Nat.add_mul, one_mul] at hj; omega
      rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range]
      have hdiv : j / ℓ = twoH := Nat.div_eq_of_lt_le hge hj
      have hmod : j % ℓ = j - twoH * ℓ := by
        rw [Nat.mod_eq_sub_mul_div, hdiv, mul_comm]
      rw [hdiv, hmod]

/-- **The row of output bit `c`** from a column table: the mask over the remaining seed bits (column `plen + j` for the
`j`-th remaining bit) and the right-hand side `v_c ⊕ Σ_{j<plen} col_j[c]·pre_j`. -/
def rowOf (tab : List ℕ) (rest plen pre c : ℕ) (vbit : Bool) : Row :=
  ((List.range rest).foldl (fun acc j => if ((tab.getD (plen + j) 0).testBit c) then acc ||| (1 <<< j) else acc) 0,
    xor vbit ((List.range plen).foldl (fun acc j => xor acc ((tab.getD j 0).testBit c && pre.testBit j)) false))

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) (l : List β) (h : ∀ a, ∀ b ∈ l, f a b = g a b) :
    ∀ a, l.foldl f a = l.foldl g a := by
  induction l with
  | nil => intro a; rfl
  | cons b l ih =>
    intro a
    simp only [List.foldl_cons]
    rw [h a b (List.mem_cons_self), ih (fun a b hb => h a b (List.mem_cons_of_mem _ hb))]

/-- **The elimination system is the rows of the column tables** (for labels below `2^ℓ` and `plen ≤ 2hℓ`). -/
theorem system_eq_rowOf (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ)
    (hplen : plen ≤ twoH * ℓ) (hcons : ∀ c ∈ cons, c.1 < 2 ^ ℓ) :
    JoinElimination.system p ℓ twoH k plen pre cons =
      cons.flatMap fun con => (List.range k).map fun c =>
        rowOf (colTable p ℓ twoH con.1) (twoH * ℓ - plen) plen pre c (con.2.testBit c) := by
  unfold JoinElimination.system
  refine List.flatMap_congr fun con hcon => ?_
  refine List.map_congr_left fun c _ => ?_
  have hcoef : ∀ j, j < twoH * ℓ →
      (JoinElimination.fmul p ℓ (2 ^ (j % ℓ)) (JoinElimination.fpow p ℓ con.1 (j / ℓ))).testBit c =
        ((colTable p ℓ twoH con.1).getD j 0).testBit c := by
    intro j hj
    rw [colTable_getD p ℓ con.1 hℓ twoH j hj, colWord_eq p ℓ con.1 hp hℓ (hcons con hcon) (j / ℓ) (j % ℓ)
      (Nat.mod_lt _ (by omega))]
  unfold rowOf
  simp only
  congr 1
  · refine foldl_congr_mem _ _ _ (fun acc j hj => ?_) 0
    simp only [hcoef (plen + j) (by have := List.mem_range.mp hj; omega)]
  · congr 1
    refine foldl_congr_mem _ _ _ (fun acc j hj => ?_) false
    simp only [hcoef j (by have := List.mem_range.mp hj; omega)]

/-- The right-hand side of a row: `v_c ⊕ Σ_{j<plen} col_j[c]·pre_j`. -/
def rhsOf (tab : List ℕ) (plen pre c : ℕ) (vbit : Bool) : Bool :=
  xor vbit ((List.range plen).foldl (fun acc j => xor acc ((tab.getD j 0).testBit c && pre.testBit j)) false)

/-- **A row's bits** (the elimination machine's input record): output bit `c` of the remaining columns, then the
right-hand side. -/
theorem rowBits_rowOf (tab : List ℕ) (rest plen pre c : ℕ) (vbit : Bool) :
    Gauss.rowBits rest (rowOf tab rest plen pre c vbit) =
      (List.range rest).map (fun j => (tab.getD (plen + j) 0).testBit c) ++ [rhsOf tab plen pre c vbit] := by
  unfold Gauss.rowBits rowOf rhsOf
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [testBit_or_fold]
  have := List.mem_range.mp hj
  simp [this]

end NearCubicWires.WireExponent3_5.SeedFix
