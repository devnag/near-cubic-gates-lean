import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open scoped BigOperators

/-! ## Möbius inversion on the cube -/

section Mobius
variable {V : ℕ}

/-- The indicator point of a set. -/
def ind (T : Finset (Fin V)) : Fin V → Bool := fun v => decide (v ∈ T)

theorem monomialValue_ind (U T : Finset (Fin V)) :
    monomialValue (ind T) U = if U ⊆ T then 1 else 0 := by
  unfold monomialValue
  by_cases h : U ⊆ T
  · rw [if_pos h, if_pos (fun v hv => by simpa [ind] using h hv)]
  · rw [if_neg h, if_neg (fun h' => h (fun v hv => by simpa [ind] using h' v hv))]

/-- The coefficient of the monomial `S` in a term list (entries with key `S` summed). -/
def coeff (P : Terms V) (S : Finset (Fin V)) : ℤ := (P.map fun t => if t.1 = S then t.2 else 0).sum

@[simp] theorem coeff_nil (S : Finset (Fin V)) : coeff ([] : Terms V) S = 0 := rfl

theorem coeff_cons (t : Finset (Fin V) × ℤ) (P : Terms V) (S : Finset (Fin V)) :
    coeff (t :: P) S = (if t.1 = S then t.2 else 0) + coeff P S := by
  simp [coeff]

/-- The alternating sum over the interval `[U, S]` of the subset lattice. -/
theorem alt_sum (U S : Finset (Fin V)) (hUS : U ⊆ S) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card * (if U ⊆ T then 1 else 0) = if U = S then 1 else 0 := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [Finset.sum_nbij' (fun T => S \ T) (fun R => S \ R) (t := (S \ U).powerset)
    (g := fun R => (-1 : ℤ) ^ R.card)]
  · rw [Finset.sum_powerset_neg_one_pow_card]
    by_cases h : U = S
    · subst h; simp
    · have : S \ U ≠ ∅ := by
        intro he
        exact h (Finset.Subset.antisymm hUS (Finset.sdiff_eq_empty_iff_subset.mp he))
      rw [if_neg this, if_neg h]
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    simp only [Finset.mem_powerset]
    exact Finset.sdiff_subset_sdiff (le_refl S) hT.2
  · intro R hR
    simp only [Finset.mem_powerset] at hR
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.sdiff_subset, fun u hu => ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨hUS hu, fun hR' => ?_⟩
    have := hR hR'
    rw [Finset.mem_sdiff] at this
    exact this.2 hu
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.sdiff_sdiff_eq_self hT.1
  · intro R hR
    simp only [Finset.mem_powerset] at hR
    exact Finset.sdiff_sdiff_eq_self (hR.trans Finset.sdiff_subset)
  · intro T _
    rfl

/-- **Möbius inversion**: the alternating sum of the values on the subsets of `S` is the coefficient of `S`. -/
theorem mob_eval (P : Terms V) (S : Finset (Fin V)) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card * Terms.eval (ind T) P = coeff P S := by
  induction P with
  | nil => simp
  | cons t P ih =>
    simp only [Terms.eval_cons, mul_add, Finset.sum_add_distrib, ih, coeff_cons, monomialValue_ind]
    congr 1
    have e : ∀ T ∈ S.powerset, (-1 : ℤ) ^ (S \ T).card * (t.2 * if t.1 ⊆ T then 1 else 0) =
        t.2 * ((-1 : ℤ) ^ (S \ T).card * if t.1 ⊆ T then 1 else 0) := by
      intro T _; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    by_cases h : t.1 ⊆ S
    · rw [alt_sum t.1 S h]
      by_cases h' : t.1 = S
      · rw [if_pos h', if_pos h', mul_one]
      · rw [if_neg h', if_neg h', mul_zero]
    · have h' : t.1 ≠ S := fun e => h (e ▸ le_refl _)
      rw [if_neg h', Finset.sum_eq_zero, mul_zero]
      intro T hT
      rw [Finset.mem_powerset] at hT
      rw [if_neg (fun hT' => h (hT'.trans hT)), mul_zero]

/-- Over any repetition-free list of sets containing every key, the coefficients rebuild the value. -/
theorem sum_coeff_eval (P : Terms V) (L : List (Finset (Fin V))) (hL : L.Nodup)
    (hkeys : ∀ S ∈ Terms.keys P, S ∈ L) (b : Fin V → Bool) :
    (L.map fun S => coeff P S * monomialValue b S).sum = Terms.eval b P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    have hP : ∀ S ∈ Terms.keys P, S ∈ L := fun S hS => hkeys S (by simp [hS])
    have ht : t.1 ∈ L := hkeys t.1 (by simp)
    simp only [coeff_cons, add_mul, Terms.eval_cons]
    rw [List.sum_map_add, ih hP]
    congr 1
    have : ∀ (l : List (Finset (Fin V))), l.Nodup →
        (l.map fun S => (if t.1 = S then t.2 else 0) * monomialValue b S).sum =
          if t.1 ∈ l then t.2 * monomialValue b t.1 else 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons S l ihl =>
        rw [List.nodup_cons] at hl
        rw [List.map_cons, List.sum_cons, ihl hl.2]
        by_cases hS : t.1 = S
        · subst hS
          rw [if_pos rfl, if_neg hl.1, if_pos (List.mem_cons_self), add_zero]
        · rw [if_neg hS, zero_mul, zero_add]
          by_cases hm : t.1 ∈ l
          · rw [if_pos hm, if_pos (List.mem_cons_of_mem S hm)]
          · rw [if_neg hm, if_neg]
            intro hc
            rcases List.mem_cons.mp hc with hc | hc
            · exact hS hc
            · exact hm hc
    rw [this L hL, if_pos ht]

/-- Over a repetition-free list, the absolute coefficients sum to at most the absolute sum of the entries. -/
theorem sum_coeff_abs_le (P : Terms V) (L : List (Finset (Fin V))) (hL : L.Nodup) :
    (L.map fun S => (coeff P S).natAbs).sum ≤ Terms.absSum P := by
  induction P with
  | nil => simp
  | cons t P ih =>
    simp only [coeff_cons, Terms.absSum_cons]
    have h1 : ∀ S, ((if t.1 = S then t.2 else 0) + coeff P S).natAbs ≤
        (if t.1 = S then t.2.natAbs else 0) + (coeff P S).natAbs := by
      intro S
      refine (Int.natAbs_add_le _ _).trans ?_
      by_cases h : t.1 = S
      · simp [h]
      · simp [h]
    have h2 : ∀ (l : List (Finset (Fin V))), l.Nodup →
        (l.map fun S => if t.1 = S then t.2.natAbs else 0).sum ≤ t.2.natAbs := by
      intro l hl
      induction l with
      | nil => simp
      | cons S l ihl =>
        rw [List.nodup_cons] at hl
        rw [List.map_cons, List.sum_cons]
        by_cases hS : t.1 = S
        · subst hS
          have hz : (l.map fun S => if t.1 = S then t.2.natAbs else 0).sum = 0 := by
            apply List.sum_eq_zero
            intro x hx
            obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hx
            rw [if_neg]
            rintro rfl
            exact hl.1 hS'
          rw [if_pos rfl, hz, add_zero]
        · rw [if_neg hS, zero_add]
          exact ihl hl.2
    calc (L.map fun S => ((if t.1 = S then t.2 else 0) + coeff P S).natAbs).sum
        ≤ (L.map fun S => (if t.1 = S then t.2.natAbs else 0) + (coeff P S).natAbs).sum :=
          List.sum_le_sum (fun S _ => h1 S)
      _ = (L.map fun S => if t.1 = S then t.2.natAbs else 0).sum + (L.map fun S => (coeff P S).natAbs).sum :=
          List.sum_map_add
      _ ≤ t.2.natAbs + Terms.absSum P := Nat.add_le_add (h2 L hL) ih

theorem mem_keys_of_coeff_ne (P : Terms V) (S : Finset (Fin V)) (h : coeff P S ≠ 0) : S ∈ Terms.keys P := by
  induction P with
  | nil => simp at h
  | cons t P ih =>
    rw [coeff_cons] at h
    by_cases ht : t.1 = S
    · simp [ht]
    · rw [if_neg ht, zero_add] at h
      simp [ih h]

end Mobius

/-! ## The family of sets of size at most `D`, as characteristic numbers -/

/-- The set of a characteristic number: the variables whose bit is set. -/
def setOf (V s : ℕ) : Finset (Fin V) := Finset.univ.filter fun v => s.testBit v.val

/-- The sets of size `d`: from each set of size `d`, add one variable at or above its bit length. -/
def level (V : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | d + 1 => (level V d).flatMap fun s => ((List.range V).filter fun v => Nat.size s ≤ v).map fun v => s + 2 ^ v

/-- All sets of size at most `D`, level by level. -/
def fam (V D : ℕ) : List ℕ := (List.range (D + 1)).flatMap (level V)

theorem testBit_add_two_pow (s v u : ℕ) (hs : s < 2 ^ v) :
    (s + 2 ^ v).testBit u = (s.testBit u || decide (u = v)) := by
  rw [add_comm]
  rcases lt_trichotomy u v with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h, decide_eq_false (Nat.ne_of_lt h), Bool.or_false]
  · subst h
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hs]
    simp
  · have h1 : 2 ^ v + s < 2 ^ u := by
      have : 2 ^ (v + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at this
      omega
    have h2 : s < 2 ^ u := lt_of_le_of_lt (Nat.le_add_left _ _) h1
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2, decide_eq_false (Nat.ne_of_gt h)]
    rfl

theorem size_add_two_pow (s v : ℕ) (hs : s < 2 ^ v) : Nat.size (s + 2 ^ v) = v + 1 := by
  apply le_antisymm
  · rw [Nat.size_le, pow_succ]; omega
  · exact Nat.lt_size.mpr (Nat.le_add_left _ _)

theorem setOf_add_two_pow (V s v : ℕ) (hv : v < V) (hs : s < 2 ^ v) :
    setOf V (s + 2 ^ v) = insert ⟨v, hv⟩ (setOf V s) := by
  ext u
  simp only [setOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, testBit_add_two_pow s v u hs,
    Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff]
  tauto

theorem not_mem_setOf (V s v : ℕ) (hv : v < V) (hs : s < 2 ^ v) : (⟨v, hv⟩ : Fin V) ∉ setOf V s := by
  simp [setOf, Nat.testBit_eq_false_of_lt hs]

/-- Members of level `d`: below `2^V`, with `d` set bits. -/
theorem level_mem (V : ℕ) : ∀ d, ∀ s ∈ level V d, s < 2 ^ V ∧ (setOf V s).card = d
  | 0, s, hs => by
    simp only [level, List.mem_singleton] at hs
    subst hs
    refine ⟨Nat.two_pow_pos V, ?_⟩
    simp [setOf]
  | d + 1, s, hs => by
    simp only [level, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hs
    obtain ⟨s0, hs0, v, ⟨hvV, hsv⟩, rfl⟩ := hs
    have h0 := level_mem V d s0 hs0
    have hlt : s0 < 2 ^ v := Nat.size_le.mp hsv
    refine ⟨?_, ?_⟩
    · have : 2 ^ (v + 1) ≤ 2 ^ V := Nat.pow_le_pow_right (by norm_num) hvV
      rw [pow_succ] at this
      omega
    · rw [setOf_add_two_pow V s0 v hvV hlt, Finset.card_insert_of_notMem (not_mem_setOf V s0 v hvV hlt), h0.2]

theorem level_nodup (V : ℕ) : ∀ d, (level V d).Nodup
  | 0 => by simp [level]
  | d + 1 => by
    rw [level, List.nodup_flatMap]
    refine ⟨fun s _ => ?_, ?_⟩
    · apply List.Nodup.map (fun a b h => by simpa using h)
      exact (List.nodup_range).filter _
    · apply (level_nodup V d).imp_of_mem
      intro a b ha hb hab
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hxa hxb
      simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hxa hxb
      obtain ⟨v, ⟨_, hav⟩, rfl⟩ := hxa
      obtain ⟨w, ⟨_, hbw⟩, hx⟩ := hxb
      have h1 := size_add_two_pow a v (Nat.size_le.mp hav)
      have h2 := size_add_two_pow b w (Nat.size_le.mp hbw)
      rw [hx] at h2
      have hvw : v = w := by omega
      subst hvw
      exact hab (by omega)

theorem fam_mem (V D s : ℕ) (hs : s ∈ fam V D) : s < 2 ^ V ∧ (setOf V s).card ≤ D := by
  simp only [fam, List.mem_flatMap, List.mem_range] at hs
  obtain ⟨d, hd, hs⟩ := hs
  have := level_mem V d s hs
  exact ⟨this.1, by omega⟩

theorem fam_nodup (V D : ℕ) : (fam V D).Nodup := by
  rw [fam, List.nodup_flatMap]
  refine ⟨fun d _ => level_nodup V d, ?_⟩
  apply (List.nodup_range).imp_of_mem
  intro a b _ _ hab
  simp only [Function.onFun]
  rw [List.disjoint_left]
  intro x hxa hxb
  exact hab ((level_mem V a x hxa).2.symm.trans (level_mem V b x hxb).2)

theorem setOf_inj (V s t : ℕ) (hs : s < 2 ^ V) (ht : t < 2 ^ V) (h : setOf V s = setOf V t) : s = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < V
  · have := congrArg (fun S => (⟨i, hi⟩ : Fin V) ∈ S) h
    simp only [setOf, Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hsi : s.testBit i <;> cases hti : t.testBit i <;> simp_all
  · have hp : 2 ^ V ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs hp), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht hp)]

/-- The family as sets. -/
def famS (V D : ℕ) : List (Finset (Fin V)) := (fam V D).map (setOf V)

theorem famS_nodup (V D : ℕ) : (famS V D).Nodup := by
  apply (fam_nodup V D).map_on
  intro s hs t ht h
  exact setOf_inj V s t (fam_mem V D s hs).1 (fam_mem V D t ht).1 h

theorem famS_card (V D : ℕ) (S : Finset (Fin V)) (hS : S ∈ famS V D) : S.card ≤ D := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
  exact (fam_mem V D s hs).2

/-- Every set of size `d` is in level `d`. -/
theorem level_complete (V : ℕ) : ∀ d, ∀ S : Finset (Fin V), S.card = d → ∃ s ∈ level V d, setOf V s = S
  | 0, S, hS => ⟨0, by simp [level], by rw [Finset.card_eq_zero] at hS; subst hS; simp [setOf]⟩
  | d + 1, S, hS => by
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set m := S.max' hne with hm
    have hmS : m ∈ S := Finset.max'_mem S hne
    obtain ⟨s0, hs0, he⟩ := level_complete V d (S.erase m) (by rw [Finset.card_erase_of_mem hmS]; omega)
    have hbits : ∀ i ≥ m.val, s0.testBit i = false := by
      intro i hi
      by_contra hc
      have hc' : s0.testBit i = true := by simpa using hc
      have hiV : i < V := by
        by_contra hiV
        have := Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (level_mem V d s0 hs0).1 (Nat.pow_le_pow_right (by norm_num) (by omega : V ≤ i)))
        rw [this] at hc'
        exact Bool.false_ne_true hc'
      have hmem : (⟨i, hiV⟩ : Fin V) ∈ S.erase m := by
        rw [← he]; simp [setOf, hc']
      rw [Finset.mem_erase] at hmem
      have hle : (⟨i, hiV⟩ : Fin V) ≤ m := Finset.le_max' S _ hmem.2
      have : i ≤ m.val := hle
      have : i = m.val := by omega
      exact hmem.1 (Fin.ext this)
    have hlt : s0 < 2 ^ m.val := Nat.lt_pow_two_of_testBit s0 hbits
    refine ⟨s0 + 2 ^ m.val, ?_, ?_⟩
    · simp only [level, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨s0, hs0, m.val, ⟨m.isLt, Nat.size_le.mpr hlt⟩, rfl⟩
    · rw [setOf_add_two_pow V s0 m.val m.isLt hlt, he]
      exact Finset.insert_erase hmS

theorem fam_complete (V D : ℕ) (S : Finset (Fin V)) (hS : S.card ≤ D) : S ∈ famS V D := by
  obtain ⟨s, hs, he⟩ := level_complete V S.card S rfl
  refine List.mem_map.mpr ⟨s, ?_, he⟩
  simp only [fam, List.mem_flatMap, List.mem_range]
  exact ⟨S.card, by omega, hs⟩

theorem level_length_le (V : ℕ) : ∀ d, (level V d).length ≤ V ^ d
  | 0 => by simp [level]
  | d + 1 => by
    rw [level, List.length_flatMap, pow_succ]
    have h : ∀ s ∈ level V d, (((List.range V).filter fun v => Nat.size s ≤ v).map fun v => s + 2 ^ v).length ≤ V :=
      fun s _ => by
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
    calc ((level V d).map fun s => (((List.range V).filter fun v => Nat.size s ≤ v).map
          fun v => s + 2 ^ v).length).sum ≤ ((level V d).map fun _ => V).sum := List.sum_le_sum (fun s hs => h s hs)
      _ = (level V d).length * V := by simp
      _ ≤ V ^ d * V := Nat.mul_le_mul_right _ (level_length_le V d)

/-- The family has at most `(V+1)^D` members (line 1469's count). -/
theorem fam_length_le (V D : ℕ) : (fam V D).length ≤ (V + 1) ^ D := by
  have key : ∀ D, (fam V D).length ≤ ∑ d ∈ Finset.range (D + 1), V ^ d := by
    intro D
    rw [fam, List.length_flatMap]
    induction D with
    | zero => simp [level]
    | succ D ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Nat.add_le_add ih (level_length_le V (D + 1))
  refine (key D).trans ?_
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ', pow_zero, pow_succ]
    have e : ∑ d ∈ Finset.range (D + 1), V ^ (d + 1) = V * ∑ d ∈ Finset.range (D + 1), V ^ d := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
    rw [e]
    have := Nat.mul_le_mul_left V ih
    nlinarith [Nat.one_le_pow D (V + 1) (by omega)]

/-! ## The coefficients from values on the family -/

section Coeff
variable {V : ℕ}

/-- **The interpolation formula on the family**: for `|S| ≤ D`, the coefficient of `S` in the expansion is the
alternating sum of the values `F(1_T)` over the members `T ⊆ S` of the family. -/
theorem coeff_eq_fam (F : Formula V) (D : ℕ) (S : Finset (Fin V)) (hS : S.card ≤ D) :
    coeff F.expand S = ((famS V D).map fun T =>
      if T ⊆ S then (-1 : ℤ) ^ (S \ T).card * F.eval (boolPoint (ind T)) else 0).sum := by
  classical
  rw [← mob_eval, ← List.sum_toFinset _ (famS_nodup V D), ← Finset.sum_filter]
  have hset : (famS V D).toFinset.filter (fun T => T ⊆ S) = S.powerset := by
    ext T
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨fam_complete V D T ((Finset.card_le_card h).trans hS), h⟩⟩
  rw [hset]
  apply Finset.sum_congr rfl
  intro T _
  rw [Formula.expand_eval]

end Coeff

/-! ## The expansion the engine prints -/

section Out
variable {V : ℕ}

theorem sum_filter_of_zero {α : Type} (l : List α) (p : α → Bool) (g : α → ℤ)
    (h : ∀ x ∈ l, ¬ p x = true → g x = 0) : ((l.filter p).map g).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    by_cases hx : p x = true
    · simp [hx, ih']
    · simp [hx, ih', h x List.mem_cons_self hx]

/-- The members of the family with nonzero coefficient, with their coefficients, in family order. -/
def expandM (F : Formula V) : Terms V :=
  ((famS V F.degree).filter fun S => coeff F.expand S ≠ 0).map fun S => (S, coeff F.expand S)

theorem expandM_keys (F : Formula V) :
    Terms.keys (expandM F) = (famS V F.degree).filter fun S => coeff F.expand S ≠ 0 := by
  simp [expandM, Terms.keys, Function.comp_def]

theorem expandM_ok (F : Formula V) : ExpandOK F (expandM F) where
  eval b := by
    rw [← Formula.expand_eval]
    have hkeys : ∀ S ∈ Terms.keys F.expand, S ∈ famS V F.degree :=
      fun S hS => fam_complete V F.degree S (Formula.expand_card_le F S hS)
    rw [← sum_coeff_eval F.expand (famS V F.degree) (famS_nodup V F.degree) hkeys b]
    unfold Terms.eval expandM
    rw [List.map_map]
    simp only [Function.comp_def]
    exact sum_filter_of_zero _ _ _ (fun S _ hS => by
      simp only [ne_eq, decide_eq_true_eq, not_not] at hS
      rw [hS, zero_mul])
  nodup := by
    rw [expandM_keys]
    exact (famS_nodup V F.degree).filter _
  degree S hS := by
    rw [expandM_keys] at hS
    exact famS_card V F.degree S (List.mem_filter.mp hS).1
  mass := by
    unfold Terms.absSum expandM
    rw [List.map_map]
    refine le_trans ?_ ((sum_coeff_abs_le F.expand ((famS V F.degree).filter fun S => coeff F.expand S ≠ 0)
      ((famS_nodup V F.degree).filter _)).trans (Formula.expand_absSum_le F))
    simp [Function.comp_def]

/-- Every printed coefficient is at most `mass` in absolute value. -/
theorem expandM_coeff_le (F : Formula V) (S : Finset (Fin V)) :
    (coeff F.expand S).natAbs ≤ F.mass := by
  have := sum_coeff_abs_le F.expand [S] (by simp)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  exact this.trans (Formula.expand_absSum_le F)

end Out

end NearCubicGates.Close.Expand
