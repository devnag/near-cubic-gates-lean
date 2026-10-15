import Mathlib
import Proof.Gates.ResidueCounts

set_option autoImplicit false

namespace NearCubicGates.Close.Tabulator

open scoped BigOperators

/-- An integer arithmetic formula over the formal variables `Fin V`. -/
inductive Formula (V : ℕ) where
  | const : ℤ → Formula V
  | var : Fin V → Formula V
  | add : Formula V → Formula V → Formula V
  | neg : Formula V → Formula V
  | sub : Formula V → Formula V → Formula V
  | mul : Formula V → Formula V → Formula V
  | pow : Formula V → ℕ → Formula V

namespace Formula

variable {V : ℕ}

/-- Evaluation at an integer assignment of the formal variables. -/
def eval (β : Fin V → ℤ) : Formula V → ℤ
  | const a => a
  | var v => β v
  | add f g => f.eval β + g.eval β
  | neg f => -f.eval β
  | sub f g => f.eval β - g.eval β
  | mul f g => f.eval β * g.eval β
  | pow f e => f.eval β ^ e

/-- Formal degree (lem:print, line 1445). -/
def degree : Formula V → ℕ
  | const _ => 0
  | var _ => 1
  | add f g => max f.degree g.degree
  | neg f => f.degree
  | sub f g => max f.degree g.degree
  | mul f g => f.degree + g.degree
  | pow f e => e * f.degree

/-- Formula size, exponents counted in unary. -/
def size : Formula V → ℕ
  | const _ => 1
  | var _ => 1
  | add f g => f.size + g.size + 1
  | neg f => f.size + 1
  | sub f g => f.size + g.size + 1
  | mul f g => f.size + g.size + 1
  | pow f e => f.size + e + 1

/-- Absolute-value evaluation at the all-ones point with every sign made positive: it bounds every
intermediate and every expanded coefficient. -/
def mass : Formula V → ℕ
  | const a => a.natAbs
  | var _ => 1
  | add f g => f.mass + g.mass
  | neg f => f.mass
  | sub f g => f.mass + g.mass
  | mul f g => f.mass * g.mass
  | pow f e => f.mass ^ e

/-- A syntactic bit weight: constants contribute their bit length, a sum one carry bit, a product the sum of
the weights. -/
def weight : Formula V → ℕ
  | const a => Nat.size a.natAbs
  | var _ => 1
  | add f g => max f.weight g.weight + 1
  | neg f => f.weight
  | sub f g => max f.weight g.weight + 1
  | mul f g => f.weight + g.weight
  | pow f e => e * f.weight

theorem mass_le_two_pow_weight (F : Formula V) : F.mass ≤ 2 ^ F.weight := by
  induction F with
  | const a => exact (Nat.lt_size_self a.natAbs).le
  | var v => simp [mass, weight]
  | add f g hf hg =>
    simp only [mass, weight, pow_succ]
    have h1 : 2 ^ f.weight ≤ 2 ^ max f.weight g.weight :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ g.weight ≤ 2 ^ max f.weight g.weight :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  | neg f hf => exact hf
  | sub f g hf hg =>
    simp only [mass, weight, pow_succ]
    have h1 : 2 ^ f.weight ≤ 2 ^ max f.weight g.weight :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2 : 2 ^ g.weight ≤ 2 ^ max f.weight g.weight :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  | mul f g hf hg =>
    simp only [mass, weight, pow_add]
    exact Nat.mul_le_mul hf hg
  | pow f e hf =>
    simp only [mass, weight]
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hf e

end Formula

/-! ## Multilinear terms -/

/-- A Boolean-multilinear polynomial: monomials (sets of formal variables) with integer coefficients. -/
abbrev Terms (V : ℕ) := List (Finset (Fin V) × ℤ)

/-- The `0/1` integer point of a Boolean assignment. -/
def boolPoint {V : ℕ} (b : Fin V → Bool) : Fin V → ℤ := fun v => if b v then 1 else 0

/-- The value of a multilinear monomial at a Boolean point. -/
def monomialValue {V : ℕ} (b : Fin V → Bool) (S : Finset (Fin V)) : ℤ :=
  if ∀ v ∈ S, b v = true then 1 else 0

namespace Terms

variable {V : ℕ}

def eval (b : Fin V → Bool) (P : Terms V) : ℤ :=
  (P.map fun t => t.2 * monomialValue b t.1).sum

def keys (P : Terms V) : List (Finset (Fin V)) := P.map Prod.fst

/-- Sum of the absolute values of the coefficients. -/
def absSum (P : Terms V) : ℕ := (P.map fun t => t.2.natAbs).sum

/-- Add one term, merging it into an existing monomial with the same variable set. -/
def insertTerm (t : Finset (Fin V) × ℤ) : Terms V → Terms V
  | [] => [t]
  | u :: us => if u.1 = t.1 then (u.1, u.2 + t.2) :: us else u :: insertTerm t us

/-- Merge equal monomials. -/
def normalize (P : Terms V) : Terms V := P.foldr insertTerm []

def neg (P : Terms V) : Terms V := P.map fun t => (t.1, -t.2)

/-- The unmerged Boolean-multilinear product: `x_v^2 = x_v` makes the product of two monomials their union. -/
def rawMul (P Q : Terms V) : Terms V :=
  P.flatMap fun s => Q.map fun t => (s.1 ∪ t.1, s.2 * t.2)

def mul (P Q : Terms V) : Terms V := normalize (rawMul P Q)

def one : Terms V := [(∅, 1)]

def pow (P : Terms V) : ℕ → Terms V
  | 0 => one
  | e + 1 => mul (pow P e) P

@[simp] theorem eval_nil (b : Fin V → Bool) : eval b ([] : Terms V) = 0 := rfl

@[simp] theorem eval_cons (b : Fin V → Bool) (t : Finset (Fin V) × ℤ) (P : Terms V) :
    eval b (t :: P) = t.2 * monomialValue b t.1 + eval b P := by
  simp [eval]

theorem eval_append (b : Fin V → Bool) (P Q : Terms V) : eval b (P ++ Q) = eval b P + eval b Q := by
  simp [eval]

@[simp] theorem keys_nil : keys ([] : Terms V) = [] := rfl

@[simp] theorem keys_cons (t : Finset (Fin V) × ℤ) (P : Terms V) : keys (t :: P) = t.1 :: keys P := rfl

theorem keys_append (P Q : Terms V) : keys (P ++ Q) = keys P ++ keys Q := by simp [keys]

@[simp] theorem absSum_nil : absSum ([] : Terms V) = 0 := rfl

@[simp] theorem absSum_cons (t : Finset (Fin V) × ℤ) (P : Terms V) :
    absSum (t :: P) = t.2.natAbs + absSum P := by
  simp [absSum]

theorem absSum_append (P Q : Terms V) : absSum (P ++ Q) = absSum P + absSum Q := by
  simp [absSum]

theorem monomialValue_union (b : Fin V → Bool) (S T : Finset (Fin V)) :
    monomialValue b (S ∪ T) = monomialValue b S * monomialValue b T := by
  unfold monomialValue
  by_cases hS : ∀ v ∈ S, b v = true
  · by_cases hT : ∀ v ∈ T, b v = true
    · have hST : ∀ v ∈ S ∪ T, b v = true := by
        intro v hv
        rcases Finset.mem_union.mp hv with h | h
        · exact hS v h
        · exact hT v h
      rw [if_pos hST, if_pos hS, if_pos hT]; rfl
    · have hST : ¬∀ v ∈ S ∪ T, b v = true :=
        fun h => hT (fun v hv => h v (Finset.mem_union_right S hv))
      rw [if_neg hST, if_neg hT, mul_zero]
  · have hST : ¬∀ v ∈ S ∪ T, b v = true :=
      fun h => hS (fun v hv => h v (Finset.mem_union_left T hv))
    rw [if_neg hST, if_neg hS, zero_mul]

/-! ### `insertTerm` and `normalize` -/

theorem eval_insertTerm (b : Fin V → Bool) (t : Finset (Fin V) × ℤ) (P : Terms V) :
    eval b (insertTerm t P) = t.2 * monomialValue b t.1 + eval b P := by
  induction P with
  | nil => simp [insertTerm]
  | cons u us ih =>
    by_cases h : u.1 = t.1
    · simp only [insertTerm, h, ↓reduceIte, eval_cons]
      ring
    · simp only [insertTerm, h, ↓reduceIte, eval_cons, ih]
      ring

theorem keys_insertTerm (t : Finset (Fin V) × ℤ) (P : Terms V) :
    ∀ S ∈ keys (insertTerm t P), S = t.1 ∨ S ∈ keys P := by
  induction P with
  | nil => simp [insertTerm]
  | cons u us ih =>
    intro S hS
    by_cases h : u.1 = t.1
    · simp only [insertTerm, h, ↓reduceIte, keys_cons] at hS
      right
      simpa [h] using hS
    · simp only [insertTerm, h, ↓reduceIte, keys_cons, List.mem_cons] at hS
      rcases hS with rfl | hS
      · right; simp
      · rcases ih S hS with h' | h'
        · left; exact h'
        · right; simp [h']

theorem nodup_insertTerm (t : Finset (Fin V) × ℤ) (P : Terms V) (h : (keys P).Nodup) :
    (keys (insertTerm t P)).Nodup := by
  induction P with
  | nil => simp [insertTerm]
  | cons u us ih =>
    rw [keys_cons, List.nodup_cons] at h
    by_cases hu : u.1 = t.1
    · simp only [insertTerm, hu, ↓reduceIte, keys_cons, List.nodup_cons]
      exact ⟨hu ▸ h.1, h.2⟩
    · simp only [insertTerm, hu, ↓reduceIte, keys_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hmem
      rcases keys_insertTerm t us u.1 hmem with h' | h'
      · exact hu h'
      · exact h.1 h'

theorem absSum_insertTerm (t : Finset (Fin V) × ℤ) (P : Terms V) :
    absSum (insertTerm t P) ≤ t.2.natAbs + absSum P := by
  induction P with
  | nil => simp [insertTerm]
  | cons u us ih =>
    by_cases h : u.1 = t.1
    · simp only [insertTerm, h, ↓reduceIte, absSum_cons]
      have := Int.natAbs_add_le u.2 t.2
      omega
    · simp only [insertTerm, h, ↓reduceIte, absSum_cons]
      omega

@[simp] theorem normalize_nil : normalize ([] : Terms V) = [] := rfl

@[simp] theorem normalize_cons (t : Finset (Fin V) × ℤ) (P : Terms V) :
    normalize (t :: P) = insertTerm t (normalize P) := rfl

theorem eval_normalize (b : Fin V → Bool) (P : Terms V) : eval b (normalize P) = eval b P := by
  induction P with
  | nil => rfl
  | cons t P ih => rw [normalize_cons, eval_insertTerm, ih, eval_cons]

theorem keys_normalize (P : Terms V) : ∀ S ∈ keys (normalize P), S ∈ keys P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    intro S hS
    rw [normalize_cons] at hS
    rcases keys_insertTerm t (normalize P) S hS with h | h
    · simp [h]
    · simp [ih S h]

theorem nodup_normalize (P : Terms V) : (keys (normalize P)).Nodup := by
  induction P with
  | nil => simp
  | cons t P ih => exact nodup_insertTerm t _ ih

theorem absSum_normalize (P : Terms V) : absSum (normalize P) ≤ absSum P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    rw [normalize_cons, absSum_cons]
    exact (absSum_insertTerm t _).trans (by omega)

/-! ### Negation, product, power -/

theorem eval_neg (b : Fin V → Bool) (P : Terms V) : eval b (neg P) = -eval b P := by
  induction P with
  | nil => simp [neg]
  | cons t P ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    ring

theorem keys_neg (P : Terms V) : keys (neg P) = keys P := by
  simp [neg, keys, Function.comp_def]

theorem absSum_neg (P : Terms V) : absSum (neg P) = absSum P := by
  simp [neg, absSum, Function.comp_def]

theorem eval_rawMul_row (b : Fin V → Bool) (s : Finset (Fin V) × ℤ) (Q : Terms V) :
    eval b (Q.map fun t => (s.1 ∪ t.1, s.2 * t.2)) = s.2 * monomialValue b s.1 * eval b Q := by
  induction Q with
  | nil => simp
  | cons t Q ihQ =>
    rw [List.map_cons, eval_cons, ihQ, eval_cons, monomialValue_union]
    ring

theorem eval_rawMul (b : Fin V → Bool) (P Q : Terms V) :
    eval b (rawMul P Q) = eval b P * eval b Q := by
  induction P with
  | nil => simp [rawMul]
  | cons s P ih =>
    simp only [rawMul, List.flatMap_cons] at ih ⊢
    rw [eval_append, eval_rawMul_row, ih, eval_cons]
    ring

theorem eval_mul (b : Fin V → Bool) (P Q : Terms V) : eval b (mul P Q) = eval b P * eval b Q := by
  rw [mul, eval_normalize, eval_rawMul]

theorem keys_rawMul (P Q : Terms V) :
    ∀ S ∈ keys (rawMul P Q), ∃ A ∈ keys P, ∃ B ∈ keys Q, S = A ∪ B := by
  intro S hS
  simp only [keys, rawMul, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map,
    Function.comp_apply] at hS
  obtain ⟨s, hs, t, ht, rfl⟩ := hS
  exact ⟨s.1, List.mem_map_of_mem hs, t.1, List.mem_map_of_mem ht, rfl⟩

theorem absSum_rawMul_row (s : Finset (Fin V) × ℤ) (Q : Terms V) :
    absSum (Q.map fun t => (s.1 ∪ t.1, s.2 * t.2)) = s.2.natAbs * absSum Q := by
  induction Q with
  | nil => simp
  | cons t Q ihQ =>
    rw [List.map_cons, absSum_cons, ihQ, absSum_cons, Int.natAbs_mul]
    ring

theorem absSum_rawMul (P Q : Terms V) : absSum (rawMul P Q) ≤ absSum P * absSum Q := by
  induction P with
  | nil => simp [rawMul]
  | cons s P ih =>
    simp only [rawMul, List.flatMap_cons] at ih ⊢
    rw [absSum_append, absSum_rawMul_row, absSum_cons]
    nlinarith

theorem absSum_mul (P Q : Terms V) : absSum (mul P Q) ≤ absSum P * absSum Q :=
  (absSum_normalize _).trans (absSum_rawMul P Q)

theorem eval_one (b : Fin V → Bool) : eval b (one : Terms V) = 1 := by
  simp [one, monomialValue]

theorem eval_pow (b : Fin V → Bool) (P : Terms V) (e : ℕ) : eval b (pow P e) = eval b P ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact eval_one b
  | succ e ih => rw [pow, eval_mul, ih, pow_succ]

theorem absSum_pow (P : Terms V) (e : ℕ) : absSum (pow P e) ≤ absSum P ^ e := by
  induction e with
  | zero => simp [pow, one]
  | succ e ih =>
    rw [pow, pow_succ]
    exact (absSum_mul _ _).trans (Nat.mul_le_mul_right _ ih)

theorem nodup_pow (P : Terms V) (e : ℕ) : (keys (pow P e)).Nodup := by
  cases e with
  | zero => simp [pow, one]
  | succ e => exact nodup_normalize _

/-- Every coefficient is bounded by the absolute sum. -/
theorem coeff_le_absSum (P : Terms V) (t : Finset (Fin V) × ℤ) (ht : t ∈ P) :
    t.2.natAbs ≤ absSum P := by
  induction P with
  | nil => simp at ht
  | cons u P ih =>
    rw [absSum_cons]
    rcases List.mem_cons.mp ht with rfl | h
    · omega
    · have := ih h
      omega

/-! ### Counting distinct monomials -/

/-- Distinct monomials of size at most `D`, weighted by any function of their size: at most
`∑_{d ≤ D} C(V,d) f(d)`. With `f = 1` this is the monomial count of lem:print (line 1468). -/
theorem sum_card_le (D : ℕ) (f : ℕ → ℕ) (P : Terms V) (hnd : (keys P).Nodup)
    (hD : ∀ S ∈ keys P, S.card ≤ D) :
    (P.map fun t => f t.1.card).sum ≤ ∑ d ∈ Finset.range (D + 1), V.choose d * f d := by
  classical
  have hlist : (P.map fun t => f t.1.card).sum = ((keys P).map fun S => f S.card).sum := by
    simp [keys, Function.comp_def]
  rw [hlist, ← List.sum_toFinset _ hnd]
  let s : Finset (Finset (Fin V)) := Finset.univ.filter fun S => S.card ≤ D
  have hsub : (keys P).toFinset ⊆ s := by
    intro S hS
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hD S (List.mem_toFinset.mp hS)
  refine (Finset.sum_le_sum_of_subset hsub).trans ?_
  have hmaps : ∀ S ∈ s, S.card ∈ Finset.range (D + 1) := by
    intro S hS
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro d _
  have hconst : (∑ S ∈ s with S.card = d, f S.card) = ∑ S ∈ s with S.card = d, f d := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_filter.mp hS).2]
  rw [hconst, Finset.sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  have hcard : (s.filter fun S => S.card = d) ⊆ Finset.powersetCard d Finset.univ := by
    intro S hS
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, (Finset.mem_filter.mp hS).2⟩
  have := Finset.card_le_card hcard
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem length_le (D : ℕ) (P : Terms V) (hnd : (keys P).Nodup) (hD : ∀ S ∈ keys P, S.card ≤ D) :
    P.length ≤ ∑ d ∈ Finset.range (D + 1), V.choose d := by
  have h := sum_card_le D (fun _ => 1) P hnd hD
  simpa using h

end Terms

/-- The binomial comparison of lem:print (line 1468): `∑_{d ≤ D} C(V,d) x^d ≤ (1 + V x)^D`. -/
theorem sum_choose_mul_pow_le (V D x : ℕ) :
    ∑ d ∈ Finset.range (D + 1), V.choose d * x ^ d ≤ (1 + V * x) ^ D := by
  rw [add_comm 1 (V * x), add_pow]
  apply Finset.sum_le_sum
  intro d hd
  have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have h1 : V.choose d * x ^ d ≤ (V * x) ^ d := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.choose_le_pow V d)
  have h2 : 1 ≤ D.choose d := Nat.choose_pos hdD
  calc V.choose d * x ^ d ≤ (V * x) ^ d := h1
    _ ≤ (V * x) ^ d * D.choose d := Nat.le_mul_of_pos_right _ h2
    _ = (V * x) ^ d * 1 ^ (D - d) * D.choose d := by simp

/-! ## The expansion of a formula -/

namespace Formula

variable {V : ℕ}

/-- Dense Boolean-multilinear expansion: list-of-terms arithmetic with equal monomials merged. -/
def expand : Formula V → Terms V
  | const a => [(∅, a)]
  | var v => [({v}, 1)]
  | add f g => Terms.normalize (f.expand ++ g.expand)
  | neg f => Terms.neg f.expand
  | sub f g => Terms.normalize (f.expand ++ Terms.neg g.expand)
  | mul f g => Terms.mul f.expand g.expand
  | pow f e => Terms.pow f.expand e

/-- (1) The expansion agrees with the formula at every Boolean point. -/
theorem expand_eval (b : Fin V → Bool) (F : Formula V) :
    Terms.eval b F.expand = F.eval (boolPoint b) := by
  induction F with
  | const a => simp [expand, eval, monomialValue]
  | var v =>
    simp only [expand, Terms.eval_cons, Terms.eval_nil, eval, boolPoint, monomialValue,
      Finset.mem_singleton, forall_eq]
    cases b v <;> simp
  | add f g hf hg => rw [expand, Terms.eval_normalize, Terms.eval_append, hf, hg]; rfl
  | neg f hf => rw [expand, Terms.eval_neg, hf]; rfl
  | sub f g hf hg =>
    rw [expand, Terms.eval_normalize, Terms.eval_append, Terms.eval_neg, hf, hg]
    simp only [eval]
    ring
  | mul f g hf hg => rw [expand, Terms.eval_mul, hf, hg]; rfl
  | pow f e hf => rw [expand, Terms.eval_pow, hf]; rfl

theorem pow_card_le (P : Terms V) (D : ℕ) (hP : ∀ S ∈ Terms.keys P, S.card ≤ D) (e : ℕ) :
    ∀ S ∈ Terms.keys (Terms.pow P e), S.card ≤ e * D := by
  induction e with
  | zero => simp [Terms.pow, Terms.one]
  | succ e ih =>
    intro S hS
    rw [Terms.pow, Terms.mul] at hS
    obtain ⟨A, hA, B, hB, rfl⟩ := Terms.keys_rawMul _ _ S (Terms.keys_normalize _ S hS)
    have h1 := ih A hA
    have h2 := hP B hB
    calc (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ e * D + D := Nat.add_le_add h1 h2
      _ = (e + 1) * D := by ring

/-- (2) Every monomial of the expansion has at most `degree` variables. -/
theorem expand_card_le (F : Formula V) : ∀ S ∈ Terms.keys F.expand, S.card ≤ F.degree := by
  induction F with
  | const a => simp [expand, degree]
  | var v => simp [expand, degree]
  | add f g hf hg =>
    intro S hS
    have h := Terms.keys_normalize _ S hS
    rw [Terms.keys_append, List.mem_append] at h
    simp only [degree]
    rcases h with h | h
    · exact (hf S h).trans (le_max_left _ _)
    · exact (hg S h).trans (le_max_right _ _)
  | neg f hf =>
    intro S hS
    rw [expand, Terms.keys_neg] at hS
    exact hf S hS
  | sub f g hf hg =>
    intro S hS
    have h := Terms.keys_normalize _ S hS
    rw [Terms.keys_append, Terms.keys_neg, List.mem_append] at h
    simp only [degree]
    rcases h with h | h
    · exact (hf S h).trans (le_max_left _ _)
    · exact (hg S h).trans (le_max_right _ _)
  | mul f g hf hg =>
    intro S hS
    obtain ⟨A, hA, B, hB, rfl⟩ := Terms.keys_rawMul _ _ S (Terms.keys_normalize _ S hS)
    exact (Finset.card_union_le A B).trans (Nat.add_le_add (hf A hA) (hg B hB))
  | pow f e hf => exact pow_card_le f.expand f.degree hf e

/-- (3) The monomials of the expansion are distinct. -/
theorem expand_keys_nodup (F : Formula V) : (Terms.keys F.expand).Nodup := by
  cases F with
  | const a => simp [expand]
  | var v => simp [expand]
  | add f g => exact Terms.nodup_normalize _
  | neg f =>
    rw [expand, Terms.keys_neg]
    exact expand_keys_nodup f
  | sub f g => exact Terms.nodup_normalize _
  | mul f g => exact Terms.nodup_normalize _
  | pow f e => exact Terms.nodup_pow _ e

/-- (3) The expansion has at most `∑_{d ≤ degree} C(V,d)` monomials. -/
theorem expand_length_le (F : Formula V) :
    F.expand.length ≤ ∑ d ∈ Finset.range (F.degree + 1), V.choose d :=
  Terms.length_le F.degree F.expand (expand_keys_nodup F) (expand_card_le F)

theorem expand_absSum_le (F : Formula V) : Terms.absSum F.expand ≤ F.mass := by
  induction F with
  | const a => simp [expand, mass]
  | var v => simp [expand, mass]
  | add f g hf hg =>
    rw [expand]
    refine (Terms.absSum_normalize _).trans ?_
    rw [Terms.absSum_append]
    exact Nat.add_le_add hf hg
  | neg f hf => rw [expand, Terms.absSum_neg]; exact hf
  | sub f g hf hg =>
    rw [expand]
    refine (Terms.absSum_normalize _).trans ?_
    rw [Terms.absSum_append, Terms.absSum_neg]
    exact Nat.add_le_add hf hg
  | mul f g hf hg =>
    rw [expand]
    exact (Terms.absSum_mul _ _).trans (Nat.mul_le_mul hf hg)
  | pow f e hf =>
    rw [expand]
    exact (Terms.absSum_pow _ _).trans (Nat.pow_le_pow_left hf e)

/-- (4) Every expanded coefficient is at most `mass ≤ 2 ^ weight`. -/
theorem expand_coeff_le (F : Formula V) (t : Finset (Fin V) × ℤ) (ht : t ∈ F.expand) :
    t.2.natAbs ≤ F.mass :=
  (Terms.coeff_le_absSum _ t ht).trans (expand_absSum_le F)

theorem expand_coeff_le_two_pow (F : Formula V) (t : Finset (Fin V) × ℤ) (ht : t ∈ F.expand) :
    t.2.natAbs ≤ 2 ^ F.weight :=
  (expand_coeff_le F t ht).trans (mass_le_two_pow_weight F)

end Formula

open scoped BigOperators
open NearCubicGates.ResidueCounts

namespace Formula

variable {V : ℕ}

/-- `f_1 + ... + f_m` (the empty sum is `0`). -/
def sumList : List (Formula V) → Formula V
  | [] => const 0
  | f :: fs => add f (sumList fs)

/-- `f_1 ⋯ f_m` (the empty product is `1`). -/
def prodList : List (Formula V) → Formula V
  | [] => const 1
  | f :: fs => mul f (prodList fs)

theorem eval_sumList (β : Fin V → ℤ) (fs : List (Formula V)) :
    (sumList fs).eval β = (fs.map fun f => f.eval β).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [sumList, eval, ih]

theorem eval_prodList (β : Fin V → ℤ) (fs : List (Formula V)) :
    (prodList fs).eval β = (fs.map fun f => f.eval β).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [prodList, eval, ih]

theorem degree_sumList_le (D : ℕ) (fs : List (Formula V)) (h : ∀ f ∈ fs, f.degree ≤ D) :
    (sumList fs).degree ≤ D := by
  induction fs with
  | nil => simp [sumList, degree]
  | cons f fs ih =>
    simp only [sumList, degree]
    exact max_le (h f (by simp)) (ih (fun g hg => h g (by simp [hg])))

theorem degree_prodList_le (fs : List (Formula V)) :
    (prodList fs).degree ≤ (fs.map degree).sum := by
  induction fs with
  | nil => simp [prodList, degree]
  | cons f fs ih =>
    simp only [prodList, degree, List.map_cons, List.sum_cons]
    omega

/-- The literal Beigel–Tarui amplifier `Amp_e(t) = 1 - (1-t)^e ∑_{j<e} C(e-1+j,j) t^j` (lem:amp, line 1484),
applied to a formula. -/
def amp (e : ℕ) (t : Formula V) : Formula V :=
  sub (const 1) (mul (pow (sub (const 1) t) e)
    (sumList ((List.range e).map fun j => mul (const ((e - 1 + j).choose j : ℤ)) (pow t j))))

theorem eval_amp (β : Fin V → ℤ) (e : ℕ) (t : Formula V) :
    (amp e t).eval β = amplifierValue e (t.eval β) := by
  have hsum : ∀ m : ℕ, ((List.range m).map fun j =>
      ((e - 1 + j).choose j : ℤ) * t.eval β ^ j).sum =
      ∑ j ∈ Finset.range m, ((e - 1 + j).choose j : ℤ) * t.eval β ^ j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  simp only [amp, eval, eval_sumList, List.map_map, Function.comp_def, amplifierValue]
  rw [hsum e]

theorem degree_amp_le (e : ℕ) (t : Formula V) : (amp e t).degree ≤ (2 * e - 1) * t.degree := by
  have hs : (sumList ((List.range e).map fun j =>
      mul (const ((e - 1 + j).choose j : ℤ)) (pow t j))).degree ≤ (e - 1) * t.degree := by
    apply degree_sumList_le
    intro f hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    have hje : j ≤ e - 1 := by have := List.mem_range.mp hj; omega
    simp only [degree, zero_add]
    exact Nat.mul_le_mul_right _ hje
  simp only [amp, degree, zero_max] at hs ⊢
  calc e * t.degree + _ ≤ e * t.degree + (e - 1) * t.degree := Nat.add_le_add_left hs _
    _ = (e + (e - 1)) * t.degree := by ring
    _ = (2 * e - 1) * t.degree := by congr 1; omega

end Formula

/-! ## Affine forms in the formal variables -/

/-- An integer affine form `c₀ + ∑_v c_v x_v` in the formal variables (lem:residue-count, line 1505). -/
structure AffineForm (V : ℕ) where
  const : ℤ
  coeff : Fin V → ℤ

namespace AffineForm

variable {V : ℕ}

def eval (L : AffineForm V) (β : Fin V → ℤ) : ℤ := L.const + ∑ v, L.coeff v * β v

def formula (L : AffineForm V) : Formula V :=
  .add (.const L.const)
    (Formula.sumList ((List.finRange V).map fun v => .mul (.const (L.coeff v)) (.var v)))

theorem formula_eval (L : AffineForm V) (β : Fin V → ℤ) : L.formula.eval β = L.eval β := by
  simp only [formula, Formula.eval, Formula.eval_sumList, List.map_map, Function.comp_def, eval]
  rw [Fin.sum_univ_def]

theorem formula_degree_le (L : AffineForm V) : L.formula.degree ≤ 1 := by
  simp only [formula, Formula.degree, Nat.zero_max]
  apply Formula.degree_sumList_le
  intro f hf
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hf
  simp [Formula.degree]

end AffineForm

/-! ## The residue polynomial `Q_{p,ρ}` (lem:residue-count) -/

/-- `∏_i (1 - (L_i - ρ_i)^{p-1})`: the product of the Fermat tests. -/
def fermatFormula {V r : ℕ} (p : ℕ) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ) : Formula V :=
  Formula.prodList ((List.finRange r).map fun i =>
    .sub (.const 1) (.pow (.sub (L i).formula (.const (ρ i))) (p - 1)))

/-- `Q_{p,ρ} = Amp_e(∏_i (1 - (L_i - ρ_i)^{p-1}))` (line 1511). -/
def residueFormula {V r : ℕ} (p e : ℕ) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ) : Formula V :=
  Formula.amp e (fermatFormula p L ρ)

theorem fermatFormula_degree_le {V r : ℕ} (p : ℕ) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ) :
    (fermatFormula p L ρ).degree ≤ r * (p - 1) := by
  refine (Formula.degree_prodList_le _).trans ?_
  have hterm : ∀ i : Fin r,
      (Formula.sub (.const 1) (.pow (.sub (L i).formula (.const (ρ i))) (p - 1))).degree ≤ p - 1 := by
    intro i
    simp only [Formula.degree, Nat.zero_max, max_zero]
    have := (L i).formula_degree_le
    calc (p - 1) * (L i).formula.degree ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ this
      _ = p - 1 := by ring
  rw [List.map_map]
  have hle : ∀ (l : List (Fin r)), (l.map ((Formula.degree) ∘ fun i =>
      Formula.sub (.const 1) (.pow (.sub (L i).formula (.const (ρ i))) (p - 1)))).sum ≤ l.length * (p - 1) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply]
      have := hterm i
      nlinarith
  simpa using hle (List.finRange r)

/-- Formal degree of the residue polynomial: at most `(2e-1) r (p-1)` (line 1515). -/
theorem residueFormula_degree_le {V r : ℕ} (p e : ℕ) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ) :
    (residueFormula p e L ρ).degree ≤ (2 * e - 1) * r * (p - 1) := by
  refine (Formula.degree_amp_le e _).trans ?_
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (fermatFormula_degree_le p L ρ)

theorem residueFormula_eval {V r : ℕ} (p e : ℕ) (L : Fin r → AffineForm V) (ρ : Fin r → ℤ)
    (β : Fin V → ℤ) :
    (residueFormula p e L ρ).eval β = liftedIndicator p e (fun i => (L i).eval β) ρ := by
  simp only [residueFormula, Formula.eval_amp, liftedIndicator, fermatFormula, Formula.eval_prodList,
    List.map_map, Function.comp_def, Formula.eval, AffineForm.formula_eval, fermatProduct]
  rw [Fin.prod_univ_def]

/-- lem:residue-count (line 1517): for every filter `H` with `|H| < p^e`, the remainder of the tabulated sum
modulo `p^e` is the exact joint residue count. `point x` is the Boolean value of every formal variable at the
inner assignment `x` (for a fixed outer assignment `y`). -/
theorem residue_count {V r k : ℕ} (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e)
    (L : Fin r → AffineForm V) (ρ : Fin r → ℤ) (H : Finset (Fin k → Bool))
    (point : (Fin k → Bool) → Fin V → Bool) (hH : H.card < p ^ e) :
    (∑ x ∈ H, (residueFormula p e L ρ).eval (boolPoint (point x))) % ((p : ℤ) ^ e) =
      ((H.filter fun x => ∀ i, (L i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  have hmod : (∑ x ∈ H, (residueFormula p e L ρ).eval (boolPoint (point x))) ≡
      ∑ x ∈ H, (if ∀ i, (L i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)] then (1 : ℤ) else 0)
        [ZMOD (p : ℤ) ^ e] := by
    apply Int.ModEq.sum
    intro x _
    rw [residueFormula_eval]
    convert liftedIndicator_modEq p hp e he (fun i => (L i).eval (boolPoint (point x))) ρ using 2
  rw [Finset.sum_boole] at hmod
  have hcard : (H.filter fun x => ∀ i, (L i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card < p ^ e :=
    (Finset.card_filter_le _ _).trans_lt hH
  have hlt : (((H.filter fun x => ∀ i, (L i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card : ℕ) : ℤ)
      < (p : ℤ) ^ e := by exact_mod_cast hcard
  exact hmod.eq.trans (Int.emod_eq_of_lt (by positivity) hlt)

/-! ## The moment polynomial `(∑_t c_t (g_t - g_t^ref))^{2k}` -/

/-- `(∑_t c_t (x_{a t} - x_{r t}))^{2k}`: `a t` is the formal variable of gate `t` at `(y,x)`, `r t` the one at the
reference point `(y,0^I)` (lines 1665-1666 with line 861). -/
def momentFormula {V G : ℕ} (c : Fin G → ℤ) (a r : Fin G → Fin V) (k : ℕ) : Formula V :=
  .pow (Formula.sumList ((List.finRange G).map fun t =>
    .mul (.const (c t)) (.sub (.var (a t)) (.var (r t))))) (2 * k)

theorem momentFormula_eval {V G : ℕ} (c : Fin G → ℤ) (a r : Fin G → Fin V) (k : ℕ) (β : Fin V → ℤ) :
    (momentFormula c a r k).eval β = (∑ t, c t * (β (a t) - β (r t))) ^ (2 * k) := by
  simp only [momentFormula, Formula.eval, Formula.eval_sumList, List.map_map, Function.comp_def]
  rw [Fin.sum_univ_def]

/-- Formal degree of the moment polynomial: at most `2k` (line 1674). -/
theorem momentFormula_degree_le {V G : ℕ} (c : Fin G → ℤ) (a r : Fin G → Fin V) (k : ℕ) :
    (momentFormula c a r k).degree ≤ 2 * k := by
  simp only [momentFormula, Formula.degree]
  have h : (Formula.sumList ((List.finRange G).map fun t =>
      Formula.mul (.const (c t)) (.sub (.var (a t)) (.var (r t))))).degree ≤ 1 := by
    apply Formula.degree_sumList_le
    intro f hf
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
    simp [Formula.degree]
  calc 2 * k * _ ≤ 2 * k * 1 := Nat.mul_le_mul_left _ h
    _ = 2 * k := by ring

end NearCubicGates.Close.Tabulator
