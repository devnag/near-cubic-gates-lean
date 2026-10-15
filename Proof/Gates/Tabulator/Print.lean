import Proof.Gates.Tabulator.Formula
import Proof.Supplier.RowBinLiftCuts

set_option autoImplicit false

namespace NearCubicGates.Close.Tabulator

open scoped BigOperators
open NearCubicWires NearCubicWires.ThresholdCompiler

/-- The input `(y,x)` of `{0,1}^n`: coordinate `i` reads `x` if `σ i` is inner and `y` if it is outer. -/
def joinPoint {n k s : ℕ} (σ : Fin n ≃ Fin k ⊕ Fin s) (y : Fin s → Bool) (x : Fin k → Bool) : Fin n → Bool :=
  fun i => Sum.elim x y (σ i)

/-- The restricted gate on the outer coordinates: weights of the outer coordinates, threshold lowered by the
inner contribution. -/
def restrict {n k s : ℕ} (g : NormalizedThresholdGate n) (σ : Fin n ≃ Fin k ⊕ Fin s) (x : Fin k → Bool) :
    NormalizedThresholdGate s where
  weight t := g.weight (σ.symm (.inr t))
  threshold := g.threshold - ∑ j, g.weight (σ.symm (.inl j)) * if x j then 1 else 0

theorem score_split {n k s : ℕ} (w : Fin n → ℤ) (σ : Fin n ≃ Fin k ⊕ Fin s) (y : Fin s → Bool)
    (x : Fin k → Bool) :
    (∑ i, w i * if joinPoint σ y x i then 1 else 0) =
      (∑ j, w (σ.symm (.inl j)) * if x j then 1 else 0) +
        ∑ t, w (σ.symm (.inr t)) * if y t then 1 else 0 := by
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
  simp [joinPoint]

/-- The restricted gate computes the gate at `(y,x)`. -/
theorem restrict_eval {n k s : ℕ} (g : NormalizedThresholdGate n) (σ : Fin n ≃ Fin k ⊕ Fin s)
    (x : Fin k → Bool) (y : Fin s → Bool) :
    (restrict g σ x).eval y = g.eval (joinPoint σ y x) := by
  unfold NormalizedThresholdGate.eval
  rw [score_split]
  apply decide_eq_decide.mpr
  simp only [restrict]
  constructor <;> intro h <;> linarith

/-- All parameters have magnitude below `2^B` ("bit length at most `B`"). -/
def GateBits {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) : Prop :=
  (∀ i, (g.weight i).natAbs < 2 ^ B) ∧ g.threshold.natAbs < 2 ^ B

theorem card_layout {n k s : ℕ} (σ : Fin n ≃ Fin k ⊕ Fin s) : n = k + s := by
  simpa using Fintype.card_congr σ

theorem restrict_bits {n k s : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) (σ : Fin n ≃ Fin k ⊕ Fin s)
    (x : Fin k → Bool) (hg : GateBits B g) : GateBits (B + Nat.clog 2 (n + 1)) (restrict g σ x) := by
  have hpow : 2 ^ B ≤ 2 ^ (B + Nat.clog 2 (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨fun t => (hg.1 _).trans_le hpow, ?_⟩
  have hk : k ≤ n := by have := card_layout σ; omega
  have hsumZ : |∑ j, g.weight (σ.symm (.inl j)) * (if x j then (1 : ℤ) else 0)| ≤
      ((k * (2 ^ B - 1) : ℕ) : ℤ) := by
    calc |∑ j, g.weight (σ.symm (.inl j)) * (if x j then (1 : ℤ) else 0)|
        ≤ ∑ j, |g.weight (σ.symm (.inl j)) * (if x j then (1 : ℤ) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, ((2 ^ B - 1 : ℕ) : ℤ) := by
          apply Finset.sum_le_sum
          intro j _
          have hw := hg.1 (σ.symm (.inl j))
          have hw' : (g.weight (σ.symm (.inl j))).natAbs ≤ 2 ^ B - 1 := by omega
          have hab : |g.weight (σ.symm (.inl j))| ≤ ((2 ^ B - 1 : ℕ) : ℤ) := by
            rw [Int.abs_eq_natAbs]; exact_mod_cast hw'
          by_cases hx : x j
          · simpa [hx] using hab
          · simp only [hx, Bool.false_eq_true, ↓reduceIte, mul_zero, abs_zero]
            positivity
      _ = ((k * (2 ^ B - 1) : ℕ) : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  have hsum : (∑ j, g.weight (σ.symm (.inl j)) * (if x j then (1 : ℤ) else 0)).natAbs ≤ k * (2 ^ B - 1) := by
    rw [Int.abs_eq_natAbs] at hsumZ
    exact_mod_cast hsumZ
  have hθ := hg.2
  have htot : (restrict g σ x).threshold.natAbs ≤ (k + 1) * (2 ^ B - 1) := by
    simp only [restrict]
    have := Int.natAbs_sub_le g.threshold
      (∑ j, g.weight (σ.symm (.inl j)) * (if x j then (1 : ℤ) else 0))
    have h1 : g.threshold.natAbs ≤ 2 ^ B - 1 := by omega
    calc _ ≤ _ := this
      _ ≤ (2 ^ B - 1) + k * (2 ^ B - 1) := Nat.add_le_add h1 hsum
      _ = (k + 1) * (2 ^ B - 1) := by ring
  have hclog : k + 1 ≤ 2 ^ Nat.clog 2 (n + 1) :=
    (by omega : k + 1 ≤ n + 1).trans (Nat.le_pow_clog (by norm_num) _)
  have hpos : 0 < 2 ^ B := Nat.pow_pos (by norm_num)
  calc (restrict g σ x).threshold.natAbs ≤ (k + 1) * (2 ^ B - 1) := htot
    _ < (k + 1) * 2 ^ B := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ ≤ 2 ^ Nat.clog 2 (n + 1) * 2 ^ B := Nat.mul_le_mul_right _ hclog
    _ = 2 ^ (B + Nat.clog 2 (n + 1)) := by rw [pow_add, mul_comm]

/-- `B_b = B' + ⌈lg(m+1)⌉ + 1` (line 1300). -/
def blockBits (m B' : ℕ) : ℕ := B' + Nat.clog 2 (m + 1) + 1

/-- `m_T = 1 + B_b m ⌈m/2⌉` (line 1301). -/
def mT (m B' : ℕ) : ℕ := 1 + blockBits m B' * m * ((m + 1) / 2)

/-- The exact children of a (non-strict) threshold gate `[θ ≤ w·y]`, i.e. the strict gate `[θ-1 < w·y]`. -/
def exactChildren {m : ℕ} (g : NormalizedThresholdGate m) : List (ExactEquation m) :=
  erratumSafeDisjointChildren g.weight (g.threshold - 1)

/-- The value of an exact test as an integer `0/1`. -/
def testValue {m : ℕ} (c : ExactEquation m) (y : Fin m → Bool) : ℤ := if c.Holds y then 1 else 0

theorem eval_iff_strict {m : ℕ} (g : NormalizedThresholdGate m) (y : Fin m → Bool) :
    g.eval y = true ↔ strictThresholdHolds g.weight (g.threshold - 1) y := by
  unfold NormalizedThresholdGate.eval strictThresholdHolds
  have hs : (∑ i, g.weight i * if y i then 1 else 0) = ∑ i, g.weight i * bitInt (y i) := rfl
  rw [hs, decide_eq_true_iff]
  omega

/-- lem:exact, sum identity: the gate is the sum of its exact children's indicators. -/
theorem exactChildren_sum {m : ℕ} (g : NormalizedThresholdGate m) (y : Fin m → Bool) :
    ((exactChildren g).map fun c => testValue c y).sum = if g.eval y then 1 else 0 := by
  have h := erratumSafeDisjointChildren_mass g.weight (g.threshold - 1) y
  unfold acceptanceMass at h
  unfold exactChildren testValue
  rw [h]
  by_cases hg : g.eval y = true
  · rw [if_pos ((eval_iff_strict g y).mp hg), if_pos hg]
  · rw [if_neg (fun h' => hg ((eval_iff_strict g y).mpr h')), if_neg hg]

/-- lem:exact, disjointness: at most one child holds on any input. -/
theorem exactChildren_disjoint {m : ℕ} (g : NormalizedThresholdGate m) (y : Fin m → Bool) :
    ((exactChildren g).filter fun c => decide (c.Holds y)).length ≤ 1 := by
  rw [← CompilerSemantics.acceptanceCount_eq_filterLength]
  unfold exactChildren
  rw [erratumSafeDisjointChildren_count]
  split <;> omega

theorem shifted_bound {m : ℕ} (B' : ℕ) (g : NormalizedThresholdGate m) (hg : GateBits B' g) :
    (shiftedTarget g.weight (g.threshold - 1)).toNat < 2 ^ (B' + Nat.clog 2 (m + 1)) := by
  have hneg : negativeMass g.weight ≤ ((m * (2 ^ B' - 1) : ℕ) : ℤ) := by
    unfold negativeMass
    have h2 : ∑ i, (if g.weight i < 0 then (magnitude (g.weight i) : ℤ) else 0) ≤
        ∑ _i : Fin m, ((2 ^ B' - 1 : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      have hw := hg.1 i
      split
      · unfold magnitude; exact_mod_cast (by omega : (g.weight i).natAbs ≤ 2 ^ B' - 1)
      · positivity
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    push_cast at h2 ⊢
    exact h2
  have hθ : g.threshold ≤ ((2 ^ B' - 1 : ℕ) : ℤ) := by
    have := hg.2
    have h1 : g.threshold.natAbs ≤ 2 ^ B' - 1 := by omega
    have h2 := Int.le_natAbs (a := g.threshold)
    omega
  have hpos : 0 < 2 ^ B' := Nat.pow_pos (by norm_num)
  have hclog : m + 1 ≤ 2 ^ Nat.clog 2 (m + 1) := Nat.le_pow_clog (by norm_num) _
  have hlt : shiftedTarget g.weight (g.threshold - 1) < (((m + 1) * 2 ^ B' : ℕ) : ℤ) := by
    unfold shiftedTarget
    have : ((m * (2 ^ B' - 1) : ℕ) : ℤ) + ((2 ^ B' - 1 : ℕ) : ℤ) < (((m + 1) * 2 ^ B' : ℕ) : ℤ) := by
      have e1 : m * (2 ^ B' - 1) + (2 ^ B' - 1) < (m + 1) * 2 ^ B' := by
        have : m * (2 ^ B' - 1) ≤ m * 2 ^ B' := Nat.mul_le_mul_left _ (by omega)
        rw [add_mul, one_mul]; omega
      exact_mod_cast e1
    linarith
  have hle : (m + 1) * 2 ^ B' ≤ 2 ^ (B' + Nat.clog 2 (m + 1)) := by
    rw [pow_add, mul_comm]; exact Nat.mul_le_mul_left _ hclog
  have hpos2 : 0 < 2 ^ (B' + Nat.clog 2 (m + 1)) := Nat.pow_pos (by norm_num)
  rw [Int.toNat_lt' hpos2]
  have : (((m + 1) * 2 ^ B' : ℕ) : ℤ) ≤ ((2 ^ (B' + Nat.clog 2 (m + 1)) : ℕ) : ℤ) := by exact_mod_cast hle
  push_cast at this hlt ⊢
  linarith

theorem height_bound {m : ℕ} (B' : ℕ) (g : NormalizedThresholdGate m) (hg : GateBits B' g) :
    compilerInputHeight g.weight (g.threshold - 1) < 2 ^ blockBits m B' := by
  have hmono : 2 ^ B' ≤ 2 ^ blockBits m B' := Nat.pow_le_pow_right (by norm_num) (by unfold blockBits; omega)
  have hmono2 : 2 ^ (B' + Nat.clog 2 (m + 1)) ≤ 2 ^ blockBits m B' :=
    Nat.pow_le_pow_right (by norm_num) (by unfold blockBits; omega)
  have hmax : maximumMagnitude g.weight < 2 ^ blockBits m B' := by
    unfold maximumMagnitude
    rw [Finset.sup_lt_iff (by simp)]
    intro i _
    exact (hg.1 i).trans_le hmono
  have h1 : 1 < 2 ^ blockBits m B' := Nat.one_lt_two_pow (by unfold blockBits; omega)
  have hs := (shifted_bound B' g hg).trans_le hmono2
  unfold compilerInputHeight
  exact max_lt h1 (max_lt hmax hs)

/-- lem:exact, child count: at most `m_T` children. -/
theorem exactChildren_length_le {m : ℕ} (B' : ℕ) (g : NormalizedThresholdGate m) (hg : GateBits B' g) :
    (exactChildren g).length ≤ mT m B' := by
  have hlen := erratumSafeDisjointChildren_encodingLength g.weight (g.threshold - 1)
  have hsize : Nat.size (compilerInputHeight g.weight (g.threshold - 1)) ≤ blockBits m B' := by
    exact Nat.size_le.mpr (height_bound B' g hg)
  unfold exactChildren
  refine hlen.trans ?_
  unfold mT
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hhalf : 1 ≤ (m + 1) / 2 := by omega
    have : m * Nat.size (compilerInputHeight g.weight (g.threshold - 1)) ≤
        blockBits m B' * m * ((m + 1) / 2) := by
      calc m * Nat.size _ ≤ m * blockBits m B' := Nat.mul_le_mul_left _ hsize
        _ = blockBits m B' * m * 1 := by ring
        _ ≤ blockBits m B' * m * ((m + 1) / 2) := Nat.mul_le_mul_left _ hhalf
    omega

/-- The coefficient envelope of lem:exact: `(2 m² B_b + m + 5) 2^{B_b}`; its bit length is `O(B' + log(m+1))`
(line 1305). -/
def childBound (m B' : ℕ) : ℕ :=
  (2 * m * m * blockBits m B' + m + 5) * 2 ^ blockBits m B'

/-- lem:exact, coefficients: every child weight and target has magnitude at most `childBound m B'`. -/
theorem exactChildren_params {m : ℕ} (B' : ℕ) (g : NormalizedThresholdGate m) (hg : GateBits B' g)
    (c : ExactEquation m) (hc : c ∈ exactChildren g) :
    (∀ i, (c.weights i).natAbs ≤ childBound m B') ∧ c.target.natAbs ≤ childBound m B' := by
  have hw := erratumSafeDisjointChildren_parameters g.weight (g.threshold - 1) c hc
  have henv := compilerParameterBound_le_encodingEnvelope g.weight (g.threshold - 1)
  have hsize : Nat.size (compilerInputHeight g.weight (g.threshold - 1)) ≤ blockBits m B' :=
    Nat.size_le.mpr (height_bound B' g hg)
  have hmono : (2 * m * m * Nat.size (compilerInputHeight g.weight (g.threshold - 1)) + m + 5) *
        2 ^ Nat.size (compilerInputHeight g.weight (g.threshold - 1)) ≤ childBound m B' := by
    unfold childBound
    apply Nat.mul_le_mul
    · have := Nat.mul_le_mul_left (2 * m * m) hsize
      omega
    · exact Nat.pow_le_pow_right (by norm_num) hsize
  have hB := henv.trans hmono
  refine ⟨fun i => ?_, ?_⟩
  · have := hw.1 i
    rw [Int.abs_eq_natAbs] at this
    have : (c.weights i).natAbs ≤ compilerParameterBound g.weight (g.threshold - 1) := by exact_mod_cast this
    omega
  · have := hw.2
    rw [Int.abs_eq_natAbs] at this
    have : c.target.natAbs ≤ compilerParameterBound g.weight (g.threshold - 1) := by exact_mod_cast this
    omega

open scoped BigOperators
open NearCubicWires NearCubicWires.ThresholdCompiler NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.MatrixScoreBatch

/-! ## The printer's half split of the outer coordinates -/

theorem halves_card (s : ℕ) : (s + 1) / 2 + s / 2 = s := by omega

/-- Row coordinates first (`⌈s/2⌉` of them), then column coordinates. -/
def halves (s : ℕ) : Fin ((s + 1) / 2) ⊕ Fin (s / 2) ≃ Fin s :=
  finSumFinEquiv.trans (finCongr (halves_card s))

@[simp] theorem halves_inl_val (s : ℕ) (i : Fin ((s + 1) / 2)) : (halves s (.inl i)).val = i.val := by
  simp [halves]

@[simp] theorem halves_inr_val (s : ℕ) (j : Fin (s / 2)) : (halves s (.inr j)).val = (s + 1) / 2 + j.val := by
  simp [halves]

/-- The outer assignment `y` printed at cell `(row, column)`: outer coordinate `t` is bit `t` of `row` when
`t < ⌈s/2⌉`, otherwise bit `t - ⌈s/2⌉` of `column` (lem:signed-printer, line 1390). -/
def outerPoint (s row column : ℕ) : Fin s → Bool := fun t =>
  if t.val < (s + 1) / 2 then row.testBit t.val else column.testBit (t.val - (s + 1) / 2)

theorem outerPoint_halves (s row column : ℕ) (u : Fin ((s + 1) / 2) ⊕ Fin (s / 2)) :
    outerPoint s row column (halves s u) = RowBinLift.assignment row column u := by
  cases u with
  | inl i => simp [outerPoint, RowBinLift.assignment, i.isLt]
  | inr j =>
    have : ¬((s + 1) / 2 + j.val < (s + 1) / 2) := by omega
    simp [outerPoint, RowBinLift.assignment, this]

/-- An exact test on the outer coordinates, read on the printer's row and column bits. -/
def toHalves {s : ℕ} (c : ExactEquation s) : RowBinLift.Equation ((s + 1) / 2) (s / 2) where
  weights u := c.weights (halves s u)
  target := c.target

theorem toHalves_holds {s : ℕ} (c : ExactEquation s) (row column : ℕ) :
    (toHalves c).Holds (RowBinLift.assignment row column) ↔ c.Holds (outerPoint s row column) := by
  unfold LabelledEquation.Holds LabelledEquation.difference LabelledEquation.score ExactEquation.Holds
  have hsum : (∑ u, (toHalves c).weights u * bitInt (RowBinLift.assignment row column u)) =
      ∑ t, c.weights t * bitInt (outerPoint s row column t) := by
    rw [← Equiv.sum_comp (halves s) (fun t => c.weights t * bitInt (outerPoint s row column t))]
    apply Finset.sum_congr rfl
    intro u _
    simp only [toHalves, outerPoint_halves]
  rw [hsum, sub_eq_zero]
  rfl

/-! ## Tuples of children -/

theorem listSum_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ℤ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (m : ℕ)
    (h : ∀ a ∈ l, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih (fun b hb => h b (by simp [hb])), List.length_cons]
    ring

/-- All tuples choosing one element from each list, in lexicographic order. -/
def tuples {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | L :: Ls => L.flatMap fun a => (tuples Ls).map (a :: ·)

theorem tuples_length {α : Type} (Ls : List (List α)) :
    (tuples Ls).length = (Ls.map List.length).prod := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    rw [tuples, length_flatMap_const L _ (tuples Ls).length (fun a _ => List.length_map _),
      ih, List.map_cons, List.prod_cons]

theorem mem_tuples_length {α : Type} (Ls : List (List α)) (es : List α) (h : es ∈ tuples Ls) :
    es.length = Ls.length := by
  induction Ls generalizing es with
  | nil => simp [tuples] at h; simp [h]
  | cons L Ls ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, _, es', hes', rfl⟩ := h
    simp [ih es' hes']

theorem mem_tuples_mem {α : Type} (Ls : List (List α)) (es : List α) (h : es ∈ tuples Ls) :
    ∀ e ∈ es, ∃ L ∈ Ls, e ∈ L := by
  induction Ls generalizing es with
  | nil => simp [tuples] at h; simp [h]
  | cons L Ls ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, es', hes', rfl⟩ := h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨L, by simp, ha⟩
    · obtain ⟨L', hL', heL'⟩ := ih es' hes' e he
      exact ⟨L', by simp [hL'], heL'⟩

theorem toNat_and (a b : Bool) : ((a && b).toNat : ℤ) = (a.toNat : ℤ) * (b.toNat : ℤ) := by
  cases a <;> cases b <;> rfl

/-- Expanding a product of sums: summing the conjunction over all tuples gives the product of the sums. -/
theorem tuples_sum {α : Type} (f : α → Bool) (Ls : List (List α)) :
    ((tuples Ls).map fun es => ((es.all f).toNat : ℤ)).sum =
      (Ls.map fun L => (L.map fun a => ((f a).toNat : ℤ)).sum).prod := by
  induction Ls with
  | nil => simp [tuples]
  | cons L Ls ih =>
    rw [tuples, listSum_flatMap, List.map_cons, List.prod_cons, ← ih]
    have hrow : ∀ a : α, (((tuples Ls).map (a :: ·)).map fun es => ((es.all f).toNat : ℤ)).sum =
        ((f a).toNat : ℤ) * ((tuples Ls).map fun es => ((es.all f).toNat : ℤ)).sum := by
      intro a
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro es _
      simp only [Function.comp_apply, List.all_cons, toNat_and]
    simp only [hrow]
    rw [List.sum_map_mul_right]

theorem prod_toNat {β : Type} (b : β → Bool) (l : List β) :
    (l.map fun v => ((b v).toNat : ℤ)).prod = if ∀ v ∈ l, b v = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.mem_cons, forall_eq_or_imp]
    cases b v <;> simp

/-! ## The data of lem:print -/

/-- A formal variable stands for gate `gate` at `(y,x)`, or at the reference point `(y,0^I)` if `reference`. -/
structure Role (G : ℕ) where
  gate : Fin G
  reference : Bool

/-- The data of lem:print (lines 1433-1446). -/
structure Tabulation (n k s G V : ℕ) where
  gates : Fin G → NormalizedThresholdGate n
  layout : Fin n ≃ Fin k ⊕ Fin s
  H : Finset (Fin k → Bool)
  role : Fin V → Role G
  Q : Terms V

/-- The inner assignment a role reads: `x`, or `0^I` for a reference variable. -/
def roleInner {k G : ℕ} (x : Fin k → Bool) (ρ : Role G) : Fin k → Bool :=
  if ρ.reference then fun _ => false else x

/-- The inner assignment with index `c`: `x_j` is bit `j` of `c`. -/
def innerPoint (k : ℕ) (c : Fin (2 ^ k)) : Fin k → Bool := fun j => c.val.testBit j.val

namespace Tabulation

variable {n k s G V : ℕ} (T : Tabulation n k s G V)

/-- The Boolean value of formal variable `v` at `(y,x)`. -/
def value (y : Fin s → Bool) (x : Fin k → Bool) (v : Fin V) : Bool :=
  (T.gates (T.role v).gate).eval (joinPoint T.layout y (roleInner x (T.role v)))

/-- The tabulated integer `∑_{x ∈ H} Q(y,x)` (line 1452). -/
def target (y : Fin s → Bool) : ℤ := ∑ x ∈ T.H, Terms.eval (T.value y x) T.Q

/-- The exact children of variable `v` at the inner assignment `x`, on the printer's halves. -/
def kids (x : Fin k → Bool) (v : Fin V) : List (RowBinLift.Equation ((s + 1) / 2) (s / 2)) :=
  (exactChildren (restrict (T.gates (T.role v).gate) T.layout (roleInner x (T.role v)))).map toHalves

/-- One monomial at one `x`: one packed exact cut per tuple of children (line 1458). -/
def termCuts (x : Fin k → Bool) (t : Finset (Fin V) × ℤ) : List Cut :=
  (tuples ((t.1.sort (· ≤ ·)).map (T.kids x))).map fun es =>
    RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)

def pointCuts (x : Fin k → Bool) : List Cut := T.Q.flatMap (T.termCuts x)

/-- All signed exact cuts: for `x = 0, …, 2^k-1` in `H`, every monomial, every tuple (line 1462). -/
def exactCuts : List Cut :=
  (List.finRange (2 ^ k)).flatMap fun c => if innerPoint k c ∈ T.H then T.pointCuts (innerPoint k c) else []

/-! ### The value identity -/

theorem kids_sum (x : Fin k → Bool) (v : Fin V) (row column : ℕ) :
    ((T.kids x v).map fun e =>
        ((decide (e.Holds (RowBinLift.assignment row column))).toNat : ℤ)).sum =
      ((T.value (outerPoint s row column) x v).toNat : ℤ) := by
  have h := exactChildren_sum (restrict (T.gates (T.role v).gate) T.layout (roleInner x (T.role v)))
    (outerPoint s row column)
  rw [restrict_eval] at h
  unfold kids value
  rw [List.map_map]
  have hc : ((fun e : RowBinLift.Equation ((s + 1) / 2) (s / 2) =>
      ((decide (e.Holds (RowBinLift.assignment row column))).toNat : ℤ)) ∘ toHalves) =
      fun c => testValue c (outerPoint s row column) := by
    funext c
    simp only [Function.comp_apply, testValue]
    by_cases hh : c.Holds (outerPoint s row column)
    · rw [if_pos hh, decide_eq_true ((toHalves_holds c row column).mpr hh)]; rfl
    · rw [if_neg hh, decide_eq_false (fun h' => hh ((toHalves_holds c row column).mp h'))]; rfl
  rw [hc, h]
  cases (T.gates (T.role v).gate).eval (joinPoint T.layout (outerPoint s row column) (roleInner x (T.role v)))
    <;> rfl

theorem termCuts_value (x : Fin k → Bool) (t : Finset (Fin V) × ℤ) (row column : ℕ) :
    ((T.termCuts x t).map fun c => EquationRow.exactValue c row column).sum =
      t.2 * monomialValue (T.value (outerPoint s row column) x) t.1 := by
  unfold termCuts
  rw [List.map_map]
  have hc : ((fun c => EquationRow.exactValue c row column) ∘
      fun (es : List (RowBinLift.Equation ((s + 1) / 2) (s / 2))) =>
        RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)) =
      fun es => t.2 * (((es.all fun e => decide (e.Holds (RowBinLift.assignment row column)))).toNat : ℤ) := by
    funext es
    simp only [Function.comp_apply, RowBinLift.split_value, RowBinLift.stack_all]
  rw [hc, List.sum_map_mul_left, tuples_sum, List.map_map]
  congr 1
  have hk : ((fun L : List (RowBinLift.Equation ((s + 1) / 2) (s / 2)) =>
      (L.map fun e => ((decide (e.Holds (RowBinLift.assignment row column))).toNat : ℤ)).sum) ∘ T.kids x) =
      fun v => ((T.value (outerPoint s row column) x v).toNat : ℤ) := by
    funext v
    exact T.kids_sum x v row column
  rw [hk, prod_toNat]
  unfold monomialValue
  simp only [Finset.mem_sort]

theorem pointCuts_value (x : Fin k → Bool) (row column : ℕ) :
    ((T.pointCuts x).map fun c => EquationRow.exactValue c row column).sum =
      Terms.eval (T.value (outerPoint s row column) x) T.Q := by
  unfold pointCuts Terms.eval
  rw [listSum_flatMap]
  congr 1
  apply List.map_congr_left
  intro t _
  exact T.termCuts_value x t row column

theorem sum_innerPoint (F : (Fin k → Bool) → ℤ) :
    (∑ c : Fin (2 ^ k), F (innerPoint k c)) = ∑ x, F x :=
  Equiv.sum_comp (SupplierEstimator.bitInputIndexEquiv k) F

/-- **The value identity** (lem:print): the signed exact-cut sum at `(row, column)` is `∑_{x ∈ H} Q(y,x)`. -/
theorem exactCuts_value (row column : ℕ) :
    (T.exactCuts.map fun c => EquationRow.exactValue c row column).sum = T.target (outerPoint s row column) := by
  unfold exactCuts target
  rw [listSum_flatMap]
  have hterm : ∀ c : Fin (2 ^ k),
      (((if innerPoint k c ∈ T.H then T.pointCuts (innerPoint k c) else []).map
        fun c => EquationRow.exactValue c row column).sum) =
      if innerPoint k c ∈ T.H then Terms.eval (T.value (outerPoint s row column) (innerPoint k c)) T.Q else 0 := by
    intro c
    split
    · exact T.pointCuts_value _ row column
    · rfl
  rw [List.map_congr_left (fun c _ => hterm c), ← Fin.sum_univ_def,
    sum_innerPoint (fun x => if x ∈ T.H then Terms.eval (T.value (outerPoint s row column) x) T.Q else 0),
    Finset.sum_ite_mem, Finset.univ_inter]

/-! ### The count -/

theorem termCuts_length_le (B : ℕ) (hB : ∀ i, GateBits B (T.gates i)) (x : Fin k → Bool)
    (t : Finset (Fin V) × ℤ) :
    (T.termCuts x t).length ≤ mT s (B + Nat.clog 2 (n + 1)) ^ t.1.card := by
  unfold termCuts
  rw [List.length_map, tuples_length, List.map_map]
  have h := List.prod_le_pow_card ((t.1.sort (· ≤ ·)).map (List.length ∘ T.kids x))
    (mT s (B + Nat.clog 2 (n + 1))) (by
      intro a ha
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
      simp only [Function.comp_apply, kids, List.length_map]
      exact exactChildren_length_le _ _ (restrict_bits B _ T.layout _ (hB _)))
  rwa [List.length_map, Finset.length_sort] at h

/-- **The count** (line 1465): at most `2^k ∑_{d ≤ D} C(V,d) m_T^d` exact cuts. -/
theorem exactCuts_length_le (B D : ℕ) (hB : ∀ i, GateBits B (T.gates i)) (hnd : (Terms.keys T.Q).Nodup)
    (hD : ∀ S ∈ Terms.keys T.Q, S.card ≤ D) :
    T.exactCuts.length ≤
      2 ^ k * ∑ d ∈ Finset.range (D + 1), V.choose d * mT s (B + Nat.clog 2 (n + 1)) ^ d := by
  have hpoint : ∀ x, (T.pointCuts x).length ≤
      ∑ d ∈ Finset.range (D + 1), V.choose d * mT s (B + Nat.clog 2 (n + 1)) ^ d := by
    intro x
    unfold pointCuts
    rw [List.length_flatMap]
    refine le_trans ?_ (Terms.sum_card_le D (fun d => mT s (B + Nat.clog 2 (n + 1)) ^ d) T.Q hnd hD)
    apply List.sum_le_sum
    intro t _
    exact T.termCuts_length_le B hB x t
  unfold exactCuts
  rw [List.length_flatMap]
  have h := List.sum_le_card_nsmul ((List.finRange (2 ^ k)).map fun c =>
      (if innerPoint k c ∈ T.H then T.pointCuts (innerPoint k c) else []).length)
    (∑ d ∈ Finset.range (D + 1), V.choose d * mT s (B + Nat.clog 2 (n + 1)) ^ d) (by
      intro a ha
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
      split
      · exact hpoint _
      · simp)
  simpa using h

theorem exactCuts_length_le_pow (B D : ℕ) (hB : ∀ i, GateBits B (T.gates i)) (hnd : (Terms.keys T.Q).Nodup)
    (hD : ∀ S ∈ Terms.keys T.Q, S.card ≤ D) :
    T.exactCuts.length ≤ 2 ^ k * (1 + V * mT s (B + Nat.clog 2 (n + 1))) ^ D :=
  (T.exactCuts_length_le B D hB hnd hD).trans (Nat.mul_le_mul_left _ (sum_choose_mul_pow_le _ _ _))

/-- Every cut has `⌈s/2⌉` left (row) weights and `⌊s/2⌋` right (column) weights. -/
theorem exactCuts_lengths (c : Cut) (hc : c ∈ T.exactCuts) :
    c.leftWeights.length = (s + 1) / 2 ∧ c.rightWeights.length = s / 2 := by
  unfold exactCuts at hc
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
  split at hi
  · obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hi
    obtain ⟨es, _, rfl⟩ := List.mem_map.mp ht
    simp [RowBinLift.split]
  · simp at hi

end Tabulation

end NearCubicGates.Close.Tabulator
