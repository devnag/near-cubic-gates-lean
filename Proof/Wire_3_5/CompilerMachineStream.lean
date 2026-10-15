import Proof.Wire_3_5.CompilerMachineRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs

/-! ## Polarization in counter order -/

/-- `polarizeTerm` with the sub-lists in counter order: sub-list `j` takes factor `i` exactly when bit `i` of `j` is set. -/
def polarizeTermM (m : ℕ) (c : ℤ) (ps : List (F2Poly ℕ)) : List (ℤ × F2Poly ℕ) :=
  if ps = [] then [(2 ^ (m - 1) * c, [[]])]
  else ps.sublists.map fun J => (c * 2 ^ (m - ps.length) * -(-1 : ℤ) ^ J.length, J.flatten)

/-- The polarization stage in counter order. -/
def polarizeM (m : ℕ) (V : IntExpression ℕ) : List (ℤ × F2Poly ℕ) :=
  V.flatMap fun t => polarizeTermM m t.1 t.2

theorem polarizeM_perm (m : ℕ) (V : IntExpression ℕ) : (polarizeM m V).Perm (polarize m V) := by
  unfold polarizeM polarize
  apply List.Perm.flatMap_left
  intro t _
  unfold polarizeTermM polarizeTerm
  split_ifs
  · exact List.Perm.refl _
  · exact (List.sublists_perm_sublists' t.2).map _

/-! ## The masks of a monomial, atom by atom -/

/-- One atom of a monomial: every running mask takes each child label of the atom. -/
def maskStep (pool : List (List SynEq)) (L : List ℕ) (a : ℕ) : List ℕ :=
  L.flatMap fun U => (labelsOf pool a).map fun c => U ||| 2 ^ c

theorem foldl_maskStep (pool : List (List SynEq)) : ∀ (mono L : List ℕ),
    mono.foldl (maskStep pool) L = L.flatMap fun U => (monoMasks pool mono).map fun u => U ||| u
  | [], L => by simp [monoMasks]
  | a :: as, L => by
    rw [List.foldl_cons, foldl_maskStep pool as]
    simp [maskStep, monoMasks, List.flatMap_assoc, List.map_flatMap, List.flatMap_map, Function.comp_def, Nat.or_assoc]

/-- **The atom-by-atom masks are `monoMasks`**, in the same order. -/
theorem monoMasks_foldl (pool : List (List SynEq)) (mono : List ℕ) :
    mono.foldl (maskStep pool) [0] = monoMasks pool mono := by
  rw [foldl_maskStep]
  simp

/-! ## Cancellation by symmetric difference -/

/-- Insert a mask by symmetric difference: an equal mask already present is removed with it. -/
def symInsert (G : List ℕ) (x : ℕ) : List ℕ := if x ∈ G then G.filter (· ≠ x) else G ++ [x]

/-- **The cancelled substitution, streaming**: every mask of every monomial, inserted by symmetric difference. -/
def oddMasksM (pool : List (List SynEq)) (p : F2Poly ℕ) : List ℕ :=
  (p.flatMap (monoMasks pool)).foldl symInsert []

theorem symInsert_nodup (G : List ℕ) (x : ℕ) (h : G.Nodup) : (symInsert G x).Nodup := by
  unfold symInsert
  split_ifs with hx
  · exact h.filter _
  · rw [← List.concat_eq_append]
    exact List.Nodup.concat hx h

theorem count_symInsert_mod (G : List ℕ) (x y : ℕ) (h : G.Nodup) :
    (symInsert G x).count y % 2 = (G.count y + [x].count y) % 2 := by
  unfold symInsert
  split_ifs with hx
  · by_cases hy : y = x
    · subst hy
      rw [List.count_eq_zero.mpr (by simp), h.count, if_pos hx]
      simp
    · rw [List.count_filter (by simpa using hy), List.count_singleton]
      simp [Ne.symm hy]
  · rw [List.count_append]

theorem foldl_symInsert_nodup : ∀ (M G : List ℕ), G.Nodup → (M.foldl symInsert G).Nodup
  | [], _, h => h
  | x :: M, G, h => foldl_symInsert_nodup M _ (symInsert_nodup G x h)

theorem mem_foldl_symInsert : ∀ (M G : List ℕ), G.Nodup → ∀ y,
    (y ∈ M.foldl symInsert G ↔ (G.count y + M.count y) % 2 = 1)
  | [], G, h, y => by
    rw [List.foldl_nil, h.count]
    split_ifs with hy <;> simp [hy]
  | x :: M, G, h, y => by
    rw [List.foldl_cons, mem_foldl_symInsert M _ (symInsert_nodup G x h) y, List.count_cons]
    have h1 := count_symInsert_mod G x y h
    rw [List.count_singleton] at h1
    constructor <;> intro h2 <;> split_ifs at h1 ⊢ <;> simp_all <;> omega

theorem oddMasksM_nodup (pool : List (List SynEq)) (p : F2Poly ℕ) : (oddMasksM pool p).Nodup :=
  foldl_symInsert_nodup _ [] List.nodup_nil

theorem mem_oddMasksM (pool : List (List SynEq)) (p : F2Poly ℕ) (y : ℕ) :
    y ∈ oddMasksM pool p ↔ (p.flatMap (monoMasks pool)).count y % 2 = 1 := by
  unfold oddMasksM
  rw [mem_foldl_symInsert _ [] List.nodup_nil y]
  simp

/-- On a sorted list, `cancelSorted` keeps one copy of every value of odd multiplicity. -/
theorem count_cancelSorted : ∀ l : List ℕ, l.Pairwise (· ≤ ·) → ∀ y, (cancelSorted l).count y = l.count y % 2
  | [], _, y => by simp [cancelSorted]
  | [x], _, y => by
    simp only [cancelSorted, List.count_singleton]
    split_ifs <;> simp
  | x :: z :: l, h, y => by
    have hzl : (z :: l).Pairwise (· ≤ ·) := h.of_cons
    unfold cancelSorted
    split_ifs with hxz
    · subst hxz
      rw [count_cancelSorted l hzl.of_cons y, List.count_cons, List.count_cons]
      split_ifs <;> omega
    · rw [List.count_cons, count_cancelSorted (z :: l) hzl y]
      conv_rhs => rw [List.count_cons]
      by_cases hy : x = y
      · subst hy
        have h0 : (z :: l).count x = 0 := by
          apply List.count_eq_zero.mpr
          intro hx
          have hxz' : x ≤ z := List.rel_of_pairwise_cons h (List.mem_cons_self)
          rcases List.mem_cons.mp hx with h1 | h1
          · exact hxz h1
          · have := List.rel_of_pairwise_cons hzl h1
            omega
        rw [h0]
        simp
      · simp [hy]

theorem mem_oddMasks (pool : List (List SynEq)) (p : F2Poly ℕ) (y : ℕ) :
    y ∈ oddMasks pool p ↔ (p.flatMap (monoMasks pool)).count y % 2 = 1 := by
  unfold oddMasks
  have hs : ((p.flatMap (monoMasks pool)).mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (p.flatMap (monoMasks pool))
    simpa using this
  rw [← List.count_pos_iff, count_cancelSorted _ hs y, (List.mergeSort_perm _ _).count_eq]
  omega

/-- **The streaming cancellation lists the same masks as the sorted one.** -/
theorem oddMasksM_perm (pool : List (List SynEq)) (p : F2Poly ℕ) : (oddMasksM pool p).Perm (oddMasks pool p) :=
  (List.perm_ext_iff_of_nodup (oddMasksM_nodup pool p) (oddMasks_nodup pool p)).mpr fun y => by
    rw [mem_oddMasksM, mem_oddMasks]

/-! ## The unions, incrementally -/

theorem combosFrom_perm {G G' : List ℕ} (h : G.Perm G') : ∀ ℓ, (combosFrom G ℓ).Perm (combosFrom G' ℓ) := by
  induction h with
  | nil => intro ℓ; exact List.Perm.refl _
  | cons x _ ih =>
    intro ℓ
    cases ℓ with
    | zero => simp [combosFrom]
    | succ ℓ =>
      simp only [combosFrom]
      exact ((ih ℓ).map _).append (ih (ℓ + 1))
  | swap x y l =>
    intro ℓ
    rcases ℓ with _ | _ | ℓ
    · simp [combosFrom]
    · simp only [combosFrom, List.map_cons, List.map_nil, Nat.or_zero, List.singleton_append]
      exact List.Perm.swap x y _
    · simp only [combosFrom, List.map_append, List.map_map, List.append_assoc]
      have e : (combosFrom l ℓ).map ((y ||| ·) ∘ (x ||| ·)) = (combosFrom l ℓ).map ((x ||| ·) ∘ (y ||| ·)) := by
        apply List.map_congr_left
        intro u _
        simp only [Function.comp, ← Nat.or_assoc, Nat.or_comm x y]
      rw [e]
      exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)
  | trans _ _ ih1 ih2 => intro ℓ; exact (ih1 ℓ).trans (ih2 ℓ)

/-- Appending a monomial: the new unions are the old ones and the old ones one size smaller, joined with it. -/
theorem combosFrom_snoc (g : ℕ) : ∀ (G : List ℕ) (ℓ : ℕ),
    (combosFrom (G ++ [g]) (ℓ + 1)).Perm (combosFrom G (ℓ + 1) ++ (combosFrom G ℓ).map (· ||| g))
  | [], ℓ => by
    cases ℓ with
    | zero => simp [combosFrom]
    | succ ℓ => simp [combosFrom]
  | h :: G, 0 => by
    simp only [List.cons_append, combosFrom, List.map_cons, List.map_nil, Nat.or_zero, Nat.zero_or]
    exact (combosFrom_snoc g G 0).trans (by simp [combosFrom]) |>.cons h
  | h :: G, ℓ + 1 => by
    simp only [List.cons_append, combosFrom]
    refine (((combosFrom_snoc g G ℓ).map _).append (combosFrom_snoc g G (ℓ + 1))).trans ?_
    simp only [List.map_append, List.map_map, List.append_assoc]
    have e : (combosFrom G ℓ).map ((h ||| ·) ∘ (· ||| g)) = (combosFrom G ℓ).map ((· ||| g) ∘ (h ||| ·)) := by
      apply List.map_congr_left
      intro u _
      simp only [Function.comp, Nat.or_assoc]
    rw [e]
    exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

/-- One monomial `g` of the lift: the old unions, the old unions below size `Q'` joined with `g`, and `g` alone.
Entries are `(size, union)`. -/
def liftStep (Q : ℕ) (E : List (ℕ × ℕ)) (g : ℕ) : List (ℕ × ℕ) :=
  E ++ ((E.filter fun e => decide (e.1 < Q)).map fun e => (e.1 + 1, e.2 ||| g)) ++ (if 0 < Q then [(1, g)] else [])

/-- **The unions of at most `Q'` distinct monomials, streaming**, with their sizes. -/
def unionsM (Q : ℕ) (G : List ℕ) : List (ℕ × ℕ) := G.foldl (liftStep Q) []

/-- The unions of `combosFrom`, with their sizes. -/
def combosAll (Q : ℕ) (G : List ℕ) : List (ℕ × ℕ) :=
  (List.range Q).flatMap fun j => (combosFrom G (j + 1)).map fun U => (j + 1, U)

theorem liftStep_perm (Q g : ℕ) {E E' : List (ℕ × ℕ)} (h : E.Perm E') : (liftStep Q E g).Perm (liftStep Q E' g) := by
  unfold liftStep
  exact (h.append ((h.filter _).map _)).append (List.Perm.refl _)

theorem combosAll_perm (Q : ℕ) {G G' : List ℕ} (h : G.Perm G') : (combosAll Q G).Perm (combosAll Q G') :=
  List.Perm.flatMap_left _ fun j _ => (combosFrom_perm h (j + 1)).map _

theorem combosAll_snoc (Q g : ℕ) (G : List ℕ) : (combosAll Q (G ++ [g])).Perm (liftStep Q (combosAll Q G) g) := by
  unfold combosAll liftStep
  refine (List.Perm.flatMap_left _ fun j _ => (combosFrom_snoc g G j).map _).trans ?_
  simp only [List.map_append]
  refine (List.flatMap_append_perm _ _ _).symm.trans ?_
  rw [List.append_assoc]
  refine List.Perm.append_left _ ?_
  cases Q with
  | zero => simp
  | succ Q =>
    rw [if_pos (Nat.succ_pos Q)]
    have e1 : (List.range (Q + 1)).flatMap (fun j => ((combosFrom G j).map (· ||| g)).map fun U => (j + 1, U)) =
        [(1, g)] ++ (List.range Q).flatMap fun j => (combosFrom G (j + 1)).map fun U => (j + 2, U ||| g) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp [combosFrom, Function.comp_def, List.map_map]
    have e2 : ((((List.range (Q + 1)).flatMap fun j => (combosFrom G (j + 1)).map fun U => (j + 1, U)).filter
        fun e => decide (e.1 < Q + 1)).map fun e => (e.1 + 1, e.2 ||| g)) =
        (List.range Q).flatMap fun j => (combosFrom G (j + 1)).map fun U => (j + 2, U ||| g) := by
      rw [List.range_succ, List.flatMap_append, List.filter_append, List.map_append]
      have hlast : (([Q].flatMap fun j => (combosFrom G (j + 1)).map fun U => (j + 1, U)).filter
          fun e => decide (e.1 < Q + 1)) = [] := by
        simp
      rw [hlast, List.map_nil, List.append_nil, List.filter_flatMap, List.map_flatMap]
      apply List.flatMap_congr
      intro j hj
      have hj' : j < Q := List.mem_range.mp hj
      rw [List.filter_map, List.map_map]
      have : (combosFrom G (j + 1)).filter ((fun e : ℕ × ℕ => decide (e.1 < Q + 1)) ∘ fun U => (j + 1, U)) =
          combosFrom G (j + 1) := by
        apply List.filter_eq_self.mpr
        intro U _
        simp only [Function.comp, decide_eq_true_eq]
        omega
      rw [this]
      rfl
    rw [e1, e2]
    exact List.perm_append_comm

/-- **The streaming lift lists the unions of `combosFrom`.** -/
theorem unionsM_perm (Q : ℕ) (G : List ℕ) : (unionsM Q G).Perm (combosAll Q G) := by
  induction G using List.reverseRecOn with
  | nil => simp [unionsM, combosAll, combosFrom]
  | append_singleton G g ih =>
    have e : unionsM Q (G ++ [g]) = liftStep Q (unionsM Q G) g := by
      simp [unionsM, List.foldl_append]
    rw [e]
    exact (liftStep_perm Q g ih).trans (combosAll_snoc Q g G).symm

/-! ## The streaming reference -/

/-- The occurrence of one union of size `k`: coefficient `w·(-2)^{k-1}`, the stacked conjunction of its labels. -/
def occOf (pool : List (List SynEq)) (H w : ℤ) (e : ℕ × ℕ) : Occurrence :=
  ⟨w * (-2) ^ (e.1 - 1), (conjSyn pool H e.2).1, (conjSyn pool H e.2).2⟩

theorem liftSyn_eq (pool : List (List SynEq)) (H : ℤ) (Q : ℕ) (w : ℤ) (G : List ℕ) :
    liftSyn pool H Q w G = (combosAll Q G).map (occOf pool H w) := by
  unfold liftSyn combosAll
  rw [List.map_flatMap]
  simp [List.map_map, Function.comp_def, occOf]

/-- **The compiler stages' streaming reference**: polarize in counter order, substitute atom by atom and cancel by
symmetric difference, lift incrementally, stack. -/
def compileRefM (pool : List (List SynEq)) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) : List Occurrence :=
  (polarizeM m V).flatMap fun w => (unionsM Q (oddMasksM pool w.2)).map (occOf pool H w.1)

/-- **The streaming reference lists the occurrences of `compileRef`.** -/
theorem compileRefM_perm (pool : List (List SynEq)) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) :
    (compileRefM pool H m Q V).Perm (compileRef pool H m Q V) := by
  unfold compileRefM compileRef
  refine (polarizeM_perm m V).flatMap ?_
  intro w _
  rw [liftSyn_eq]
  exact ((unionsM_perm Q _).trans (combosAll_perm Q (oddMasksM_perm pool w.2))).map _

theorem occTable_perm {a b : List Occurrence} (h : a.Perm b) (zL zR : ℕ) : occTable a zL zR = occTable b zL zR :=
  (h.map _).sum_eq

theorem compileRefM_modEq (pool : List (List SynEq)) (H Vb : ℤ) (hH : Vb < H) (m Q : ℕ) (hm : 1 ≤ m)
    (V : IntExpression ℕ) (hVm : ∀ t ∈ V, t.2.length ≤ m) (zL zR : ℕ)
    (hV : ∀ e ∈ pool.flatten, |e.value zL zR| ≤ Vb) (ρ : ℕ → Bool) (hex : PoolExact pool zL zR ρ) :
    occTable (compileRefM pool H m Q V) zL zR ≡ 2 ^ (m - 1) * IntExpression.eval V ρ [ZMOD (2 : ℤ) ^ Q] := by
  rw [occTable_perm (compileRefM_perm pool H m Q V)]
  exact compileRef_modEq pool H Vb hH m Q hm V hVm zL zR hV ρ hex

theorem compileRefM_length_le (pool : List (List SynEq)) (H : ℤ) (m Q d : ℕ) (V : IntExpression ℕ)
    (hVm : ∀ t ∈ V, t.2.length ≤ m) (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    (compileRefM pool H m Q V).length ≤ V.length * 2 ^ m * (Q * (pool.flatten.length + 1) ^ (Q * d)) := by
  rw [(compileRefM_perm pool H m Q V).length_eq]
  exact compileRef_length_le pool H m Q d V hVm hd

/-! ## Twins -/

/-- A pool of two atoms with two and one children (labels 0, 1 and 2). -/
def twinPool : List (List SynEq) := [[zeroSyn, zeroSyn], [zeroSyn]]

theorem twin_masks : monoMasks twinPool [0, 1] = [5, 6] ∧ [0, 1].foldl (maskStep twinPool) [0] = [5, 6] := by
  decide

/-- The polynomial `x₀x₁ + x₀x₁ + x₀`: the repeated monomial cancels, leaving the masks of `x₀`. -/
theorem twin_cancel : oddMasksM twinPool [[0, 1], [0, 1], [0]] = [1, 2] := by
  decide

theorem twin_unions : unionsM 2 [1, 2, 4] = [(1, 1), (2, 3), (1, 2), (2, 5), (2, 6), (1, 4)] := by
  decide

end NearCubicWires.WireExponent3_5.CompilerMachine
