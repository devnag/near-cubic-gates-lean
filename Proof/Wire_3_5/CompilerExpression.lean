import Proof.Wire_3_5.CompilerSubstitute
import Proof.Wire_3_5.CompilerStackLift

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {α ZL ZR : Type}

def conjEquation (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (U : Finset ℕ) : SeparatedEquation ZL ZR :=
  stackEquations H ((U.sort (· ≤ ·)).map eqs)

/-- The labels of a product of monomials. -/
def supportUnion (J : List (Finset ℕ)) : Finset ℕ := J.foldr (· ∪ ·) ∅

def liftOccurrences (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (Q : ℕ) (w : ℤ) (P : ChildPoly) :
    SignedOccurrenceList ZL ZR :=
  (List.range Q).flatMap fun j =>
    ((listSupports P).sublistsLen (j + 1)).map fun J => (w * (-2) ^ j, conjEquation eqs H (supportUnion J))

def compileExpression (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (m Q : ℕ)
    (V : IntExpression α) : SignedOccurrenceList ZL ZR :=
  (polarize m V).flatMap fun w => liftOccurrences eqs H Q w.1 (substitute children w.2)

/-! ## The congruence -/

theorem value_append (S S' : SignedOccurrenceList ZL ZR) (zl : ZL) (zr : ZR) :
    SignedOccurrenceList.value (S ++ S') zl zr = SignedOccurrenceList.value S zl zr + SignedOccurrenceList.value S' zl zr := by
  simp [SignedOccurrenceList.value, List.sum_append]

theorem value_flatMap {β : Type} (L : List β) (f : β → SignedOccurrenceList ZL ZR) (zl : ZL) (zr : ZR) :
    SignedOccurrenceList.value (L.flatMap f) zl zr = (L.map fun b => SignedOccurrenceList.value (f b) zl zr).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => rw [List.flatMap_cons, value_append, ih]; rfl

theorem mem_supportUnion (J : List (Finset ℕ)) (c : ℕ) : c ∈ supportUnion J ↔ ∃ S ∈ J, c ∈ S := by
  induction J with
  | nil => simp [supportUnion]
  | cons S J ih => simp only [supportUnion, List.foldr_cons, Finset.mem_union] at ih ⊢; rw [ih]; simp

/-- A stacked conjunction holds exactly when every monomial of the product holds. -/
theorem conjEquation_holds (eqs : ℕ → SeparatedEquation ZL ZR) (H Vb : ℤ) (hH : Vb < H) (zl : ZL) (zr : ZR)
    (hV : ∀ c, |eqValue (eqs c) zl zr| ≤ Vb) (J : List (Finset ℕ)) :
    (conjEquation eqs H (supportUnion J)).holds zl zr = J.all (monoVal fun c => (eqs c).holds zl zr) := by
  unfold conjEquation
  have hiff := stack_holds_iff H Vb hH (((supportUnion J).sort (· ≤ ·)).map eqs) zl zr (by
    intro E hE; simp only [List.mem_map] at hE; obtain ⟨c, _, rfl⟩ := hE; exact hV c)
  apply Bool.eq_iff_iff.mpr
  rw [hiff, List.all_eq_true]
  simp only [List.mem_map, Finset.mem_sort, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, monoVal,
    decide_eq_true_eq]
  constructor
  · intro h S hS c hc; exact h c ((mem_supportUnion J c).mpr ⟨S, hS, hc⟩)
  · intro h c hc; obtain ⟨S, hS, hcS⟩ := (mem_supportUnion J c).mp hc; exact h S hS c hcS

theorem liftOccurrences_value (eqs : ℕ → SeparatedEquation ZL ZR) (H Vb : ℤ) (hH : Vb < H) (Q : ℕ) (w : ℤ)
    (P : ChildPoly) (zl : ZL) (zr : ZR) (hV : ∀ c, |eqValue (eqs c) zl zr| ≤ Vb) :
    SignedOccurrenceList.value (liftOccurrences eqs H Q w P) zl zr =
      w * binLiftValue Q (monoVal fun c => (eqs c).holds zl zr) (listSupports P) := by
  unfold liftOccurrences binLiftValue
  induction Q with
  | zero => simp [SignedOccurrenceList.value]
  | succ Q ih =>
    rw [List.range_succ, List.flatMap_append, value_append, ih, Finset.sum_range_succ, mul_add]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, SignedOccurrenceList.value, List.map_map]
    rw [show ((fun p : ℤ × SeparatedEquation ZL ZR => p.1 * bitZ (p.2.holds zl zr)) ∘
        fun J => (w * (-2) ^ Q, conjEquation eqs H (supportUnion J))) =
        fun J => w * (-2) ^ Q * bitZ (J.all (monoVal fun c => (eqs c).holds zl zr)) by
      funext J; simp only [Function.comp, conjEquation_holds eqs H Vb hH zl zr hV J]]
    rw [List.sum_map_mul_left]; ring

theorem modEq_list_sum {β : Type} (L : List β) (f g : β → ℤ) (n : ℤ) (h : ∀ b ∈ L, f b ≡ g b [ZMOD n]) :
    (L.map f).sum ≡ (L.map g).sum [ZMOD n] := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h b List.mem_cons_self).add (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem compileExpression_modEq (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H Vb : ℤ) (hH : Vb < H)
    (m Q : ℕ) (hm : 1 ≤ m) (V : IntExpression α) (hVm : ∀ t ∈ V, t.2.length ≤ m) (zl : ZL) (zr : ZR)
    (hV : ∀ c, |eqValue (eqs c) zl zr| ≤ Vb) (ρ : α → Bool)
    (hexact : ExactChildren children (fun c => (eqs c).holds zl zr) ρ) :
    SignedOccurrenceList.value (compileExpression children eqs H m Q V) zl zr ≡
      2 ^ (m - 1) * IntExpression.eval V ρ [ZMOD (2 : ℤ) ^ Q] := by
  rw [← polarize_value m hm V hVm ρ]
  unfold compileExpression signedValue
  rw [value_flatMap]
  apply modEq_list_sum
  intro w _
  rw [liftOccurrences_value eqs H Vb hH Q w.1 _ zl zr hV]
  apply Int.ModEq.mul_left
  refine (binLiftValue_modEq Q _ _).trans ?_
  rw [listSupports_filter_length, ← substitute_eval children _ ρ hexact w.2]
  unfold ChildPoly.eval
  rcases Nat.mod_two_eq_zero_or_one
      ((substitute children w.2).filter fun S => monoVal (fun c => (eqs c).holds zl zr) S).card with h | h <;>
    simp [h, bitZ]

/-! ## The occurrence bound -/

theorem liftOccurrences_length (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (Q : ℕ) (w : ℤ) (P : ChildPoly) :
    (liftOccurrences eqs H Q w P).length = ∑ j ∈ Finset.range Q, P.card.choose (j + 1) := by
  unfold liftOccurrences
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp [List.length_sublistsLen, listSupports_length]

theorem compileExpression_length_le (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (m Q d : ℕ)
    (V : IntExpression α) (pool : Finset ℕ) (hVm : ∀ t ∈ V, t.2.length ≤ m)
    (hpool : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, ∀ a ∈ mono, ∀ c ∈ children a, c ∈ pool)
    (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    (compileExpression children eqs H m Q V).length ≤ V.length * 2 ^ m * (Q * (pool.card + 1) ^ (Q * d)) := by
  unfold compileExpression
  rw [List.length_flatMap]
  have hterm : ∀ w ∈ polarize m V, (liftOccurrences eqs H Q w.1 (substitute children w.2)).length ≤
      Q * (pool.card + 1) ^ (Q * d) := by
    intro w hw
    rw [liftOccurrences_length]
    have hcard : (substitute children w.2).card ≤ (pool.card + 1) ^ d := by
      apply substitute_card_le children w.2 pool d
      · intro mono hmono a ha c hc
        rcases polarize_mono_mem m V w hw mono hmono with h | ⟨t, ht, p, hp, hm⟩
        · subst h; simp at ha
        · exact hpool t ht p hp mono hm a ha c hc
      · intro mono hmono
        rcases polarize_mono_mem m V w hw mono hmono with h | ⟨t, ht, p, hp, hm⟩
        · subst h; simp
        · exact hd t ht p hp mono hm
    calc ∑ j ∈ Finset.range Q, (substitute children w.2).card.choose (j + 1)
        ≤ Q * max 1 (substitute children w.2).card ^ Q := binLift_count_le Q _
      _ ≤ Q * ((pool.card + 1) ^ d) ^ Q := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_left
          exact max_le (Nat.one_le_pow _ _ (by omega)) hcard
      _ = Q * (pool.card + 1) ^ (Q * d) := by rw [← pow_mul, mul_comm d Q]
  calc ((polarize m V).map fun w => (liftOccurrences eqs H Q w.1 (substitute children w.2)).length).sum
      ≤ ((polarize m V).map fun _ => Q * (pool.card + 1) ^ (Q * d)).sum := by
        apply List.sum_le_sum; intro w hw; exact hterm w hw
    _ = (polarize m V).length * (Q * (pool.card + 1) ^ (Q * d)) := by simp
    _ ≤ V.length * 2 ^ m * (Q * (pool.card + 1) ^ (Q * d)) :=
        Nat.mul_le_mul_right _ (polarize_length_le m V hVm)

/-- The least nonnegative residue modulo `2^q`. -/
def recoverColumn (q : ℕ) (r : ℤ) : ℤ := r % 2 ^ q

/-- **`alg:recovery`, first case**: `0 ≤ W < 2^q` is recovered as the least nonnegative residue. -/
theorem recoverColumn_eq (q : ℕ) (W r : ℤ) (h : r ≡ W [ZMOD (2 : ℤ) ^ q]) (h0 : 0 ≤ W) (h1 : W < 2 ^ q) :
    recoverColumn q r = W := by
  unfold recoverColumn
  rw [h]
  exact Int.emod_eq_of_lt h0 h1

/-- The representative in `[−2^{q−1}, 2^{q−1})`. -/
def recoverSigned (q : ℕ) (r : ℤ) : ℤ := if r % 2 ^ q < 2 ^ (q - 1) then r % 2 ^ q else r % 2 ^ q - 2 ^ q

/-- **`alg:recovery`, second case**: `|W| ≤ J` with `2^q > 2J` is recovered as the symmetric representative. -/
theorem recoverSigned_eq (q : ℕ) (hq : 1 ≤ q) (W r J : ℤ) (h : r ≡ W [ZMOD (2 : ℤ) ^ q]) (hJ : |W| ≤ J)
    (hq2 : 2 * J < 2 ^ q) : recoverSigned q r = W := by
  have hpow : (2 : ℤ) ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (q - 1) := by positivity
  rw [abs_le] at hJ
  unfold recoverSigned
  rw [h]
  rcases le_or_gt 0 W with hW | hW
  · have h1 : W < 2 ^ q := by linarith
    rw [Int.emod_eq_of_lt hW h1, if_pos (by linarith)]
  · have h3 : (W + 2 ^ q) % 2 ^ q = W + 2 ^ q := Int.emod_eq_of_lt (by linarith) (by linarith)
    have h2 : W % 2 ^ q = W + 2 ^ q := by rw [← h3]; exact (Int.add_modEq_right (a := W) (n := 2 ^ q)).symm
    have hnot : ¬ (W + 2 ^ q < 2 ^ (q - 1)) := by rw [not_lt]; linarith
    rw [h2, if_neg hnot]; ring

theorem compileExpression_recover (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H Vb : ℤ) (hH : Vb < H)
    (m Q : ℕ) (hm : 1 ≤ m) (V : IntExpression α) (hVm : ∀ t ∈ V, t.2.length ≤ m) (zl : ZL) (zr : ZR)
    (hV : ∀ c, |eqValue (eqs c) zl zr| ≤ Vb) (ρ : α → Bool)
    (hexact : ExactChildren children (fun c => (eqs c).holds zl zr) ρ) (J : ℤ)
    (h0 : 0 ≤ IntExpression.eval V ρ) (hJ : IntExpression.eval V ρ ≤ J) (hQ : 2 ^ (m - 1) * J < 2 ^ Q) :
    recoverColumn Q (SignedOccurrenceList.value (compileExpression children eqs H m Q V) zl zr) =
      2 ^ (m - 1) * IntExpression.eval V ρ := by
  apply recoverColumn_eq Q _ _ (compileExpression_modEq children eqs H Vb hH m Q hm V hVm zl zr hV ρ hexact)
  · positivity
  · calc 2 ^ (m - 1) * IntExpression.eval V ρ ≤ 2 ^ (m - 1) * J := by gcongr
      _ < 2 ^ Q := hQ

theorem supportUnion_card_le (J : List (Finset ℕ)) (d : ℕ) (hJ : ∀ S ∈ J, S.card ≤ d) :
    (supportUnion J).card ≤ J.length * d := by
  induction J with
  | nil => simp [supportUnion]
  | cons S J ih =>
    simp only [supportUnion, List.foldr_cons, List.length_cons] at ih ⊢
    calc (S ∪ J.foldr (· ∪ ·) ∅).card ≤ S.card + (J.foldr (· ∪ ·) ∅).card := Finset.card_union_le _ _
      _ ≤ d + J.length * d := Nat.add_le_add (hJ S List.mem_cons_self)
          (ih fun S' hS' => hJ S' (List.mem_cons_of_mem _ hS'))
      _ = (J.length + 1) * d := by ring

end NearCubicWires.WireExponent3_5.Compiler
