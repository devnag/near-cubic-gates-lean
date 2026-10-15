import Proof.Gates.Tabulator.Print

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.ThresholdCompiler

/-- `x` with its bits below `b` cleared. -/
def clr (x b : ℕ) : ℕ := x - x % 2 ^ b

theorem clr_succ (x b : ℕ) : clr x b = clr x (b + 1) + if x.testBit b then 2 ^ b else 0 := by
  unfold clr
  have h := lowBits_succ x b
  unfold lowBits at h
  have h1 : x % 2 ^ (b + 1) ≤ x := Nat.mod_le _ _
  rw [h]; split_ifs at h ⊢ <;> omega

theorem clr_large (x b : ℕ) (h : x < 2 ^ b) : clr x b = 0 := by
  unfold clr; rw [Nat.mod_eq_of_lt h]; simp

section Closed
variable {n : ℕ} (w : Fin n → ℤ) (sh : ℕ)

/-- The coefficient vector after the visit's update, by a predicate of visited indices. -/
def cf (P : Fin n → Bool) (bit : ℕ) : Fin n → ℕ :=
  fun j => if P j then clr (magnitude (w j)) bit else clr (magnitude (w j)) (bit + 1)

/-- The coefficients at the visit `(bit, i)`. -/
def coefAt (bit : ℕ) (i : Fin n) : Fin n → ℕ :=
  fun j => if i ≤ j then clr (magnitude (w j)) bit else clr (magnitude (w j)) (bit + 1)

/-- The children of one level, along a list of indices, with visited predicate `P`. -/
def levelChildren (bit : ℕ) : (Fin n → Bool) → List (Fin n) → List (ExactEquation n)
  | _, [] => []
  | P, i :: l =>
    (if (magnitude (w i)).testBit bit then [crossingChild w sh (cf w (fun j => P j || decide (j = i)) bit) i bit]
      else []) ++ levelChildren bit (fun j => P j || decide (j = i)) l

theorem level_eq (bit : ℕ) : ∀ (l : List (Fin n)) (P : Fin n → Bool) (st : CrossingState n), l.Nodup →
    (∀ i ∈ l, P i = false) → (∀ j, st.coefficients j = cf w P bit j) →
    compileCrossingLevel w sh bit l st =
      ⟨cf w (fun j => P j || decide (j ∈ l)) bit, st.children ++ levelChildren w sh bit P l⟩
  | [], P, st, _, _, hc => by
    simp only [compileCrossingLevel, levelChildren, List.append_nil, List.not_mem_nil, decide_false, Bool.or_false]
    cases st with
    | mk c ch => simp only [CrossingState.mk.injEq, and_true]; funext j; exact hc j
  | i :: l, P, st, hnd, hP, hc => by
    have hil : i ∉ l := (List.nodup_cons.mp hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    set P' : Fin n → Bool := fun j => P j || decide (j = i) with hP'
    have hP'l : ∀ k ∈ l, P' k = false := by
      intro k hk
      have hki : k ≠ i := fun e => hil (e ▸ hk)
      simp [hP', hP k (List.mem_cons_of_mem _ hk), hki]
    have hfin : (fun j => P' j || decide (j ∈ l)) = (fun j => P j || decide (j ∈ i :: l)) := by
      funext j; simp only [hP', List.mem_cons]; by_cases h1 : j = i <;> simp [h1]
    have hPi : P i = false := hP i (by simp)
    by_cases hb : (magnitude (w i)).testBit bit = true
    · have hnext : ∀ j, addCrossingBit st.coefficients i bit j = cf w P' bit j := by
        intro j
        unfold addCrossingBit cf
        rw [hc j]
        by_cases hj : j = i
        · subst hj; unfold cf; simp [hPi, hP', clr_succ _ bit, hb]
        · unfold cf; simp [hP', hj]
      simp only [compileCrossingLevel, hb, if_true]
      rw [level_eq bit l P' _ hnd' hP'l (by intro j; exact hnext j), hfin]
      simp only [levelChildren, hb, if_true, List.singleton_append, List.append_assoc, CrossingState.mk.injEq,
        true_and]
      have hcf : (fun j => addCrossingBit st.coefficients i bit j) = cf w P' bit := funext hnext
      simp [hcf, hP']
    · have hb' : (magnitude (w i)).testBit bit = false := by simpa using hb
      have hsame : ∀ j, st.coefficients j = cf w P' bit j := by
        intro j
        rw [hc j]
        by_cases hj : j = i
        · subst hj; unfold cf; simp [hPi, hP', clr_succ _ bit, hb']
        · unfold cf; simp [hP', hj]
      simp only [compileCrossingLevel, hb', Bool.false_eq_true, if_false]
      rw [level_eq bit l P' st hnd' hP'l hsame, hfin]
      simp [levelChildren, hb', hP']

/-- All levels from the zero state: the children are the levels' children in order. -/
theorem levels_eq : ∀ (k : ℕ) (st : CrossingState n), (∀ j, st.coefficients j = clr (magnitude (w j)) k) →
    (compileCrossingLevels w sh k st).children =
      st.children ++ (List.range k).reverse.flatMap fun bit =>
        levelChildren w sh bit (fun _ => false) (List.finRange n).reverse
  | 0, st, _ => by simp [compileCrossingLevels]
  | k + 1, st, hc => by
    simp only [compileCrossingLevels]
    have hl := level_eq w sh k (List.finRange n).reverse (fun _ => false) st
      (List.nodup_reverse.mpr (List.nodup_finRange n)) (by simp) (by intro j; rw [hc j]; simp [cf])
    rw [hl, levels_eq k _ (by intro j; simp [cf])]
    simp [List.range_succ, List.append_assoc]

/-- The descending indices `[m−1, …, 0]`. -/
def downFrom : (m : ℕ) → m ≤ n → List (Fin n)
  | 0, _ => []
  | m + 1, h => ⟨m, h⟩ :: downFrom m (by omega)

theorem downFrom_length : ∀ (m : ℕ) (h : m ≤ n), (downFrom (n := n) m h).length = m
  | 0, _ => rfl
  | m + 1, h => by simp [downFrom, downFrom_length m]

theorem downFrom_getElem : ∀ (m : ℕ) (h : m ≤ n) (k : ℕ) (hk : k < (downFrom (n := n) m h).length),
    ((downFrom m h)[k]).val = m - 1 - k
  | 0, _, k, hk => by simp [downFrom] at hk
  | m + 1, h, 0, _ => by simp [downFrom]
  | m + 1, h, k + 1, hk => by
    simp only [downFrom, List.getElem_cons_succ]
    rw [downFrom_getElem m (by omega) k (by simp [downFrom, downFrom_length] at hk ⊢; omega)]
    omega

theorem downFrom_full : downFrom (n := n) n le_rfl = (List.finRange n).reverse := by
  apply List.ext_getElem
  · simp [downFrom_length]
  · intro k h1 h2
    apply Fin.ext
    rw [downFrom_getElem, List.getElem_reverse, List.getElem_finRange]
    simp

theorem level_closed (bit : ℕ) : ∀ (m : ℕ) (h : m ≤ n),
    levelChildren w sh bit (fun j => decide (m ≤ j.val)) (downFrom m h) =
      (downFrom m h).filterMap fun i =>
        if (magnitude (w i)).testBit bit then some (crossingChild w sh (coefAt w bit i) i bit) else none
  | 0, _ => rfl
  | m + 1, h => by
    have hP : (fun j : Fin n => decide (m + 1 ≤ j.val) || decide (j = ⟨m, h⟩)) = fun j => decide (m ≤ j.val) := by
      funext j
      by_cases hj : j = ⟨m, h⟩
      · subst hj; simp
      · have : j.val ≠ m := fun e => hj (Fin.ext e)
        simp [hj]; omega
    have hcf : cf w (fun j => decide (m + 1 ≤ j.val) || decide (j = ⟨m, h⟩)) bit = coefAt w bit ⟨m, h⟩ := by
      rw [hP]; funext j; unfold cf coefAt
      simp [Fin.le_def]
    simp only [downFrom, levelChildren, List.filterMap_cons]
    rw [hcf, hP, level_closed bit m (by omega)]
    split <;> simp

/-- The children of the main branch, in closed form. -/
def closedChildren (L : ℕ) : List (ExactEquation n) :=
  (List.range L).reverse.flatMap fun bit => (List.finRange n).reverse.filterMap fun i =>
    if (magnitude (w i)).testBit bit then some (crossingChild w sh (coefAt w bit i) i bit) else none

/-- **The compiler's children in closed form** (all magnitudes below `2^L`). -/
theorem children_closed (L : ℕ) (hL : ∀ j, magnitude (w j) < 2 ^ L) :
    (compileCrossingLevels w sh L ⟨fun _ => 0, []⟩).children = closedChildren w sh L := by
  rw [levels_eq w sh L _ (by intro j; simp [clr_large _ _ (hL j)])]
  simp only [List.nil_append, closedChildren]
  congr 1
  funext bit
  have h0 : (fun _ : Fin n => false) = fun j : Fin n => decide (n ≤ j.val) := by
    funext j; simp [j.isLt]
  rw [h0, ← downFrom_full, level_closed]

end Closed

/-! ## List forms -/

/-- A child equation as a list: its weights in order, then its target. -/
def kidL {n : ℕ} (c : ExactEquation n) : List ℤ := List.ofFn c.weights ++ [c.target]

/-- The literal coefficient of index `j` at the visit `(bit, i)`. -/
def litW (ws : List ℤ) (bit i j : ℕ) : ℕ :=
  2 * (if i ≤ j then clr (ws.getD j 0).natAbs bit else clr (ws.getD j 0).natAbs (bit + 1)) + if j = i then 1 else 0

/-- The child at the visit `(bit, i)`, computed from the weight list. -/
def childL (ws : List ℤ) (sh bit i : ℕ) : List ℤ :=
  (List.range ws.length).map (fun j => if ws.getD j 0 < 0 then -(litW ws bit i j : ℤ) else (litW ws bit i j : ℤ)) ++
    [2 * 2 ^ bit * ((sh / 2 ^ bit + 1 : ℕ) : ℤ) + 1 -
      ((List.range ws.length).map fun j => if ws.getD j 0 < 0 then (litW ws bit i j : ℤ) else 0).sum]

/-- `n` zero weights and a target. -/
def zeroL (n : ℕ) (t : ℤ) : List ℤ := List.replicate n 0 ++ [t]

def negMassL (ws : List ℤ) : ℤ := (ws.map fun z => if z < 0 then (z.natAbs : ℤ) else 0).sum
def totalL (ws : List ℤ) : ℕ := (ws.map Int.natAbs).sum
def maxL (ws : List ℤ) : ℕ := (ws.map Int.natAbs).foldr max 0

/-- **The exact children as lists** (lem:exact, the machine's specification). -/
def compileL (ws : List ℤ) (t : ℤ) : List (List ℤ) :=
  if t + negMassL ws < 0 then [zeroL ws.length 0]
  else if (totalL ws : ℤ) ≤ t + negMassL ws then [zeroL ws.length 1]
  else (List.range (max 1 (Nat.size (max (maxL ws) (t + negMassL ws).toNat)))).reverse.flatMap fun bit =>
    (List.range ws.length).reverse.filterMap fun i =>
      if (ws.getD i 0).natAbs.testBit bit then some (childL ws (t + negMassL ws).toNat bit i) else none

section ListForm
variable {n : ℕ}

theorem ofFn_getD (w : Fin n → ℤ) (j : Fin n) : (List.ofFn w).getD j.val 0 = w j := by
  rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem sum_ofFn_eq (f : Fin n → ℤ) : (List.ofFn f).sum = ∑ j, f j := List.sum_ofFn

theorem range_map_ofFn (f : ℕ → ℤ) : (List.range n).map f = List.ofFn fun j : Fin n => f j.val := by
  apply List.ext_getElem <;> simp

theorem negMassL_ofFn (w : Fin n → ℤ) : negMassL (List.ofFn w) = negativeMass w := by
  unfold negMassL negativeMass
  rw [List.map_ofFn, sum_ofFn_eq]; rfl

theorem totalL_ofFn (w : Fin n → ℤ) : totalL (List.ofFn w) = totalMagnitude w := by
  unfold totalL totalMagnitude
  rw [List.map_ofFn, List.sum_ofFn]; rfl

theorem maxL_ofFn (w : Fin n → ℤ) : maxL (List.ofFn w) = maximumMagnitude w := by
  unfold maxL maximumMagnitude
  rw [List.map_ofFn]
  have key : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih x hx).trans (le_max_right _ _)
  have key2 : ∀ (l : List ℕ) (B : ℕ), (∀ x ∈ l, x ≤ B) → l.foldr max 0 ≤ B := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro B h
      exact max_le (h a (by simp)) (ih B (fun x hx => h x (by simp [hx])))
  apply le_antisymm
  · apply key2
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact Finset.le_sup (f := fun i => magnitude (w i)) (Finset.mem_univ i)
  · apply Finset.sup_le
    intro i _
    exact key _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem kidL_child (w : Fin n → ℤ) (sh bit : ℕ) (i : Fin n) :
    kidL (crossingChild w sh (coefAt w bit i) i bit) = childL (List.ofFn w) sh bit i.val := by
  unfold kidL childL crossingChild expandLiteralEquation negativeLiteralOffset
  simp only [List.length_ofFn]
  have hl : ∀ j : Fin n, litW (List.ofFn w) bit i.val j.val = 2 * coefAt w bit i j + (if j = i then 1 else 0) := by
    intro j
    unfold litW coefAt
    rw [ofFn_getD]
    by_cases hij : i ≤ j <;> by_cases hji : j = i <;> simp [hij, hji, Fin.le_def, Fin.ext_iff, magnitude] <;> omega
  rw [range_map_ofFn, range_map_ofFn, sum_ofFn_eq]
  simp only [ofFn_getD, hl]
  push_cast
  rfl

theorem zero_kidL (t : ℤ) : kidL (zeroEquation n t) = zeroL n t := by
  unfold kidL zeroL zeroEquation
  simp [List.ofFn_const]

/-- **The exact children as lists.** -/
theorem compileL_eq (w : Fin n → ℤ) (t : ℤ) :
    (erratumSafeDisjointChildren w t).map kidL = compileL (List.ofFn w) t := by
  unfold erratumSafeDisjointChildren compileL shiftedTarget
  dsimp only
  rw [negMassL_ofFn, totalL_ofFn, maxL_ofFn, List.length_ofFn]
  split_ifs with h1 h2
  · simp [zero_kidL]
  · simp [zero_kidL]
  · set L := crossingLevelCount w t with hL
    have hLe : max 1 (Nat.size (max (maximumMagnitude w) (t + negativeMass w).toNat)) = L := by
      rw [hL]; unfold crossingLevelCount shiftedTarget; rfl
    rw [hLe, children_closed w _ L (by
      intro j
      have h1 : magnitude (w j) ≤ maximumMagnitude w :=
        Finset.le_sup (f := fun i => magnitude (w i)) (Finset.mem_univ j)
      have h2 : maximumMagnitude w < 2 ^ Nat.size (max (maximumMagnitude w) (t + negativeMass w).toNat) :=
        lt_of_le_of_lt (le_max_left _ _) (Nat.lt_size_self _)
      have h3 : 2 ^ Nat.size (max (maximumMagnitude w) (t + negativeMass w).toNat) ≤ 2 ^ L := by
        apply Nat.pow_le_pow_right (by norm_num); rw [← hLe]; exact le_max_right _ _
      omega)]
    unfold closedChildren
    rw [List.map_flatMap]
    congr 1
    funext bit
    rw [List.map_filterMap]
    have hrange : (List.range n).reverse = ((List.finRange n).reverse).map Fin.val := by
      rw [List.map_reverse, List.map_coe_finRange_eq_range]
    rw [hrange, List.filterMap_map]
    congr 1
    funext i
    simp only [Function.comp_apply, ofFn_getD]
    by_cases hb : (magnitude (w i)).testBit bit = true
    · have hb' : (w i).natAbs.testBit bit = true := hb
      simp [hb, hb', kidL_child]
    · have hb' : (w i).natAbs.testBit bit = false := by simpa [magnitude] using hb
      simp [hb', magnitude]

end ListForm

end NearCubicGates.Close.TabMachine
