import Proof.Supplier.RowBinLiftInput

/-! Bit-width bounds for actual stacked occurrence terms. All magnitude
bounds refer to the supplied explicit equation fields, not a source promise. -/
namespace NearCubicWires.RepairOrdinary.RowBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sum_le_length_mul (xs : List ℕ) (bound : ℕ)
    (hb : ∀ x ∈ xs,x ≤ bound) : xs.sum ≤ xs.length*bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (fun a ha => hb a (by simp [ha]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith

theorem horner_lt_pow (base : ℕ) (_hb : 0 < base) (xs : List ℕ)
    (hx : ∀ x ∈ xs,x < base) : natHornerFold base xs < base^xs.length := by
  induction xs with
  | nil => simp [natHornerFold]
  | cons x xs ih =>
    have hhead := hx x (by simp)
    have htail := ih (fun a ha => hx a (by simp [ha]))
    simp only [natHornerFold,List.length_cons,pow_succ]
    calc
      x+base*natHornerFold base xs < base+base*natHornerFold base xs := by omega
      _ = base*(natHornerFold base xs+1) := by ring
      _ ≤ base*(base^xs.length) := Nat.mul_le_mul_left _ htail
      _ = _ := by ring

theorem stack_magnitude {α : Type} [Fintype α] (es : List (LabelledEquation α)) :
    equationMagnitudeBound (canonicalEquationStack es) <
      ((es.map equationMagnitudeBound).sum+1)^es.length := by
  have hh := horner_lt_pow ((es.map equationMagnitudeBound).sum+1) (by omega)
    (es.map equationMagnitudeBound) (fun x hx => (member_le_sum _ x hx).trans_lt (by omega))
  have he := equationMagnitudeBound_stackEquations_le (equationListBase es) es
  apply he.trans_lt
  have hbase : (equationListBase es).natAbs=(es.map equationMagnitudeBound).sum+1 := by
    change Int.natAbs (((es.map equationMagnitudeBound).sum+1 : ℕ) : ℤ)=_
    rfl
  simpa only [hbase,List.length_map] using hh

theorem stack_base_bound (m w : ℕ) : m*2^w+1 ≤ 2^(m+w+1) := by
  have hm : m ≤ 2^m := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow : 1 ≤ 2^(m+w) := Nat.one_le_pow _ _ (by decide)
  calc
    m*2^w+1 ≤ 2^m*2^w+1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) _
    _ = 2^(m+w)+1 := by rw [pow_add]
    _ ≤ 2^(m+w+1) := by rw [pow_succ]; omega

theorem stack_width {α : Type} [Fintype α] (es : List (LabelledEquation α))
    (m w : ℕ) (hl : es.length ≤ m)
    (hw : ∀ e ∈ es,equationMagnitudeBound e ≤ 2^w) :
    equationMagnitudeBound (canonicalEquationStack es) < 2^((m+w+1)*m) := by
  have hsum := sum_le_length_mul (es.map equationMagnitudeBound) (2^w) (by
    intro n hn
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    exact hw e he)
  simp only [List.length_map] at hsum
  have hb : (es.map equationMagnitudeBound).sum+1 ≤ 2^(m+w+1) :=
    (Nat.add_le_add_right (hsum.trans (Nat.mul_le_mul_right _ hl)) 1).trans
      (stack_base_bound m w)
  apply (stack_magnitude es).trans_le
  calc
    _ ≤ (2^(m+w+1))^es.length := Nat.pow_le_pow_left hb _
    _ = 2^((m+w+1)*es.length) := by rw [pow_mul]
    _ ≤ 2^((m+w+1)*m) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hl)

theorem term_bounds {α : Type} [Fintype α] (Q d w : ℕ)
    (ms : List (List (LabelledEquation α)))
    (hd : ∀ m ∈ ms,m.length ≤ d)
    (hw : ∀ e ∈ ms.flatten,equationMagnitudeBound e ≤ 2^w)
    (t : ℤ × List (LabelledEquation α)) (ht : t ∈ terms Q ms) :
    t.1.natAbs < 2^Q ∧
      equationMagnitudeBound (canonicalEquationStack t.2) < 2^((Q*d+w+1)*(Q*d)) := by
  obtain ⟨j,hj,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨selected,hs,rfl⟩ := List.mem_map.mp ht
  have hjQ : j+1 ≤ Q := (List.mem_range.mp hj).trans_le (Nat.min_le_left _ _)
  have hsub := List.mem_sublistsLen.mp hs
  have hl : selected.flatten.length ≤ Q*d := by
    rw [List.length_flatten]
    have h := sum_le_length_mul (selected.map List.length) d (by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hn
      exact hd m (hsub.1.subset hm))
    simp only [List.length_map,hsub.2] at h
    exact h.trans (Nat.mul_le_mul_right _ hjQ)
  refine ⟨?_,stack_width _ (Q*d) w hl ?_⟩
  · simp only [Int.natAbs_pow]
    change 2^j < 2^Q
    exact Nat.pow_lt_pow_right (by decide) hjQ
  · intro e he
    obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
    exact hw e (List.mem_flatten.mpr ⟨m,hsub.1.subset hm,he⟩)

end NearCubicWires.RepairOrdinary.RowBinLift
