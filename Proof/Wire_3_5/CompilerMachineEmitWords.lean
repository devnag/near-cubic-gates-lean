import Proof.Wire_3_5.CompilerMachineEmitRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.SupplierPipeline NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord signMagnitude)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- The request's code of one field at width `p + 1`. -/
def sm (p : ℕ) (z : ℤ) : List Bool := frame (signMagnitude (p + 1) z)

theorem ofFn_fields {w : ℕ} (E : RowBinLift.Equation w w) :
    List.ofFn (fun i : Fin w => E.weights (Sum.inl i)) ++ List.ofFn (fun i : Fin w => E.weights (Sum.inr i)) =
      (List.range (w + w)).map (fieldOf E) := by
  apply List.ext_getElem (by simp)
  intro q h1 h2
  simp only [List.getElem_map, List.getElem_range]
  unfold fieldOf
  by_cases hq : q < w
  · rw [List.getElem_append_left (by simpa using hq), List.getElem_ofFn, dif_pos hq]
  · have hq2 : q < w + w := by simpa using h2
    rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn, dif_neg hq, dif_pos hq2]
    simp

theorem fieldOf_target {w : ℕ} (E : RowBinLift.Equation w w) : fieldOf E (w + w) = E.target := by
  unfold fieldOf
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem cutPair_eq {w : ℕ} (p : ℕ) (v : ℤ) (E : RowBinLift.Equation w w) :
    (EquationRow.doubled false [RowBinLift.split v E]).flatMap (cutWord (p + 1)) =
      (List.range (w + w)).flatMap (fun q => sm p (fieldOf E q)) ++ sm p (fieldOf E (w + w)) ++ sm p v ++
        ((List.range (w + w)).flatMap (fun q => sm p (fieldOf E q)) ++ sm p (fieldOf E (w + w) + 1) ++ sm p (-v)) := by
  simp only [EquationRow.doubled, List.flatMap_cons, List.flatMap_nil, List.append_nil, cutWord, MatrixScoreBatch.fields,
    EquationRow.padded, EquationRow.successor, EquationRow.paddedRight, Bool.false_eq_true, ↓reduceIte,
    RowBinLift.split]
  rw [ofFn_fields, fieldOf_target, List.flatMap_append, List.flatMap_append, List.flatMap_map]
  simp [sm, List.append_assoc]

/-! ## The coefficient -/

theorem bits_binary : ∀ (m x : ℕ), x < 2 ^ m → binary m x = Nat.bits x ++ List.replicate (m - (Nat.bits x).length) false
  | 0, x, hx => by
    have : x = 0 := by simpa using hx
    subst this
    simp [binary]
  | m + 1, x, hx => by
    by_cases h0 : x = 0
    · subst h0
      simp [Pool.binary_zero']
    · have hd : x / 2 < 2 ^ m := by rw [pow_succ] at hx; omega
      have ih := bits_binary m (x / 2) hd
      have hb : Nat.bits x = (x % 2 == 1) :: Nat.bits (x / 2) := by
        rcases Nat.mod_two_eq_zero_or_one x with hm | hm
        · have hx2 : 2 * (x / 2) = x := by omega
          have hne : x / 2 ≠ 0 := by omega
          have hb0 := Nat.bit0_bits (x / 2) hne
          rw [hx2] at hb0
          rw [hb0, hm]
          rfl
        · have hx2 : 2 * (x / 2) + 1 = x := by omega
          have hb1 := Nat.bit1_bits (x / 2)
          rw [hx2] at hb1
          rw [hb1, hm]
          rfl
      have hl : m + 1 - ((x / 2).bits.length + 1) = m - (x / 2).bits.length := by omega
      simp only [binary]
      rw [ih, hb]
      simp only [List.length_cons, List.cons_append, hl]

theorem binary_shift : ∀ (a b x : ℕ), binary (a + b) (x * 2 ^ a) = List.replicate a false ++ binary b x
  | 0, b, x => by simp
  | a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [binary, List.replicate_succ, List.cons_append]
    have h1 : x * 2 ^ (a + 1) % 2 = 0 := by rw [pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
    have h2 : x * 2 ^ (a + 1) / 2 = x * 2 ^ a := by
      rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
    rw [h1, h2, binary_shift a b x]
    rfl

theorem neg_one_pow_par (L : ℕ) : -(-1 : ℤ) ^ L = if decide (L % 2 = 1) then 1 else -1 := by
  rcases Nat.even_or_odd L with ⟨r, hr⟩ | ⟨r, hr⟩
  · have : ¬ L % 2 = 1 := by omega
    simp [hr, ← two_mul, pow_mul]
  · simp [hr, pow_add, pow_mul]

/-- The coefficient of a union of `k ≥ 1` masks in a group of coefficient `c` and parity `par` (as `termCuts`). -/
def coefVal (c : ℤ) (L k : ℕ) : ℤ := c * 2 ^ 0 * -(-1 : ℤ) ^ L * (-2) ^ (k - 1)

theorem coefVal_natAbs (c : ℤ) (L k : ℕ) : (coefVal c L k).natAbs = c.natAbs * 2 ^ (k - 1) := by
  unfold coefVal
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_pow]
  simp

theorem coefVal_neg (c : ℤ) (L k : ℕ) (hk : 1 ≤ k) :
    decide (coefVal c L k < 0) =
      (decide (c ≠ 0) && (decide (c < 0) ^^ decide (L % 2 = 1) ^^ decide (k % 2 = 1))) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h2 : (0 : ℤ) < 2 ^ k' := by positivity
  have hpos : ∀ t : ℤ, 0 < t → decide (c * t < 0) = (decide (c ≠ 0) && decide (c < 0)) := by
    intro t ht
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · rw [decide_eq_true (show c * t < 0 by nlinarith), decide_eq_true (show c ≠ 0 by omega), decide_eq_true hc]
      rfl
    · simp
    · rw [decide_eq_false (show ¬ c * t < 0 by nlinarith), decide_eq_false (show ¬ c < 0 by omega)]
      simp
  have hneg : ∀ t : ℤ, 0 < t → decide (c * -t < 0) = (decide (c ≠ 0) && !decide (c < 0)) := by
    intro t ht
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · rw [decide_eq_false (show ¬ c * -t < 0 by nlinarith), decide_eq_true hc]
      simp
    · simp
    · rw [decide_eq_true (show c * -t < 0 by nlinarith), decide_eq_true (show c ≠ 0 by omega),
        decide_eq_false (show ¬ c < 0 by omega)]
      rfl
  have hv : coefVal c L (k' + 1) = c * ((if decide (L % 2 = 1) then 1 else -1) * (-1) ^ k' * 2 ^ k') := by
    unfold coefVal
    rw [neg_one_pow_par, Nat.add_sub_cancel, show (-2 : ℤ) = (-1) * 2 by norm_num, mul_pow]
    ring
  rw [hv]
  rcases Nat.even_or_odd k' with he | ho
  · have hp : (-1 : ℤ) ^ k' = 1 := he.neg_one_pow
    have hk : (k' + 1) % 2 = 1 := by rcases he with ⟨r, hr⟩; omega
    by_cases hL : L % 2 = 1
    · rw [hp, hpos _ (by simp [hL])]
      simp [hL, hk]
    · rw [hp, show (if decide (L % 2 = 1) then (1 : ℤ) else -1) * 1 * 2 ^ k' = -2 ^ k' by simp [hL],
        hneg _ h2]
      simp [hL, hk]
  · have hp : (-1 : ℤ) ^ k' = -1 := ho.neg_one_pow
    have hk : ¬ (k' + 1) % 2 = 1 := by rcases ho with ⟨r, hr⟩; omega
    by_cases hL : L % 2 = 1
    · rw [hp, show (if decide (L % 2 = 1) then (1 : ℤ) else -1) * -1 * 2 ^ k' = -2 ^ k' by simp [hL],
        hneg _ h2]
      simp [hL, hk]
    · rw [hp, show (if decide (L % 2 = 1) then (1 : ℤ) else -1) * -1 * 2 ^ k' = 2 ^ k' by simp [hL],
        hpos _ h2]
      simp [hL, hk]

theorem coef_sm (p : ℕ) (c : ℤ) (L k : ℕ) (hk : 1 ≤ k) :
    signMagnitude (p + 1) (coefVal c L k) =
      (decide (c ≠ 0) && (decide (c < 0) ^^ decide (L % 2 = 1) ^^ decide (k % 2 = 1))) ::
        binary (p + 1) (c.natAbs * 2 ^ (k - 1)) := by
  unfold signMagnitude
  rw [coefVal_neg c L k hk, coefVal_natAbs]

theorem coef_sm_neg (p : ℕ) (c : ℤ) (L k : ℕ) (hk : 1 ≤ k) :
    signMagnitude (p + 1) (-coefVal c L k) =
      (decide (c ≠ 0) && !(decide (c < 0) ^^ decide (L % 2 = 1) ^^ decide (k % 2 = 1))) ::
        binary (p + 1) (c.natAbs * 2 ^ (k - 1)) := by
  have hn : -coefVal c L k = coefVal (-c) L k := by unfold coefVal; ring
  rw [hn, coef_sm p (-c) L k hk, Int.natAbs_neg]
  congr 1
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · rw [decide_eq_true (show -c ≠ 0 by omega), decide_eq_false (show ¬ (-c < 0) by omega),
      decide_eq_true (show c ≠ 0 by omega), decide_eq_true hc]
    cases decide (L % 2 = 1) <;> cases decide (k % 2 = 1) <;> rfl
  · simp
  · rw [decide_eq_true (show -c ≠ 0 by omega), decide_eq_true (show -c < 0 by omega),
      decide_eq_true (show c ≠ 0 by omega), decide_eq_false (show ¬ c < 0 by omega)]
    cases decide (L % 2 = 1) <;> cases decide (k % 2 = 1) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
