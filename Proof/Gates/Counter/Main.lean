import Proof.Gates.Counter.Sound
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Proof.Gates.Counter.Complete
import Bindings.Williams14_Corollary4_4
import Proof.Gates.Counter.Eventual
import Proof.Gates.SavedClockArithmetic

/-!
# The `W = 0` branch (paper v2 lines 1636–1640)

"If `W = 0`, the circuits are constant and the call is evaluated exactly, using the fact that a nonempty parity has
probability `1/2`." For an admitted call with `W = 0` every top coefficient vanishes, so (by well-formedness, nonzero
coefficients) both circuits have no gates and evaluate their table at score `0`. `parity_half`: an input parity whose
effective index set (indices of odd multiplicity) is nonempty is true on exactly half of the cube.
`zeroWeightValue_exact`: the branch returns the exact probability.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

theorem foldl_xor_count (bs : List Bool) : bs.foldl xor false = decide (bs.count true % 2 = 1) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, Bool.false_xor, foldl_xor_acc, ih, List.count_cons]
    cases b
    · simp
    · rcases Nat.mod_two_eq_zero_or_one (List.count true bs) with h | h <;> simp [Nat.add_mod, h]

theorem count_true_map {α : Type*} (l : List α) (g : α → Bool) : (l.map g).count true = l.countP g := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.count_cons, List.countP_cons, ih]
    cases g a <;> simp

/-- The bit of index `i` of an input (false beyond the arity). -/
def bitAt {n : ℕ} (z : BitInput n) (i : ℕ) : Bool := if h : i < n then z ⟨i, h⟩ else false

theorem parityOf_eq (c : Call) (z : BitInput c.n) :
    c.parityOf z = decide ((c.parity.countP (bitAt z)) % 2 = 1) := by
  unfold Call.parityOf
  rw [foldl_xor_count, count_true_map]
  rfl

/-- All multiplicities even: the parity is constantly false. -/
theorem parityOf_even (c : Call) (heven : ∀ i, i < c.n → c.parity.count i % 2 = 0) (hlt : ∀ i ∈ c.parity, i < c.n)
    (z : BitInput c.n) : c.parityOf z = false := by
  rw [parityOf_eq, ← List.sum_map_count_dedup_filter_eq_countP]
  have heach : ∀ x ∈ (c.parity.dedup.filter (bitAt z)).map (fun x => c.parity.count x), x % 2 = 0 := by
    intro x hx
    simp only [List.mem_map, List.mem_filter, List.mem_dedup] at hx
    obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hx
    exact heven i (hlt i hi)
  have hsum : ∀ (l : List ℕ), (∀ x ∈ l, x % 2 = 0) → l.sum % 2 = 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.sum_cons]
      have h1 := hl a (by simp)
      have h2 := ih (fun x hx => hl x (by simp [hx]))
      omega
  have := hsum _ heach
  simp [this]

/-- Flipping one coordinate. -/
def flipAt {n : ℕ} (i0 : Fin n) (z : BitInput n) : BitInput n := Function.update z i0 (!z i0)

theorem flipAt_flipAt {n : ℕ} (i0 : Fin n) (z : BitInput n) : flipAt i0 (flipAt i0 z) = z := by
  funext i
  by_cases h : i = i0
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

theorem foldl_xor_indicator (l : List ℕ) (a : ℕ) :
    (l.map fun i => decide (i = a)).foldl xor false = decide (l.count a % 2 = 1) := by
  rw [foldl_xor_count, count_true_map]
  congr 2

/-- Flipping a coordinate of odd multiplicity negates the parity. -/
theorem parityOf_flip (c : Call) (i0 : Fin c.n) (hodd : c.parity.count i0.val % 2 = 1) (z : BitInput c.n) :
    c.parityOf (flipAt i0 z) = !c.parityOf z := by
  unfold Call.parityOf
  have hpt : ∀ i ∈ c.parity, (if h : i < c.n then flipAt i0 z ⟨i, h⟩ else false) =
      xor (if h : i < c.n then z ⟨i, h⟩ else false) (decide (i = i0.val)) := by
    intro i _
    by_cases h : i < c.n
    · simp only [dif_pos h]
      by_cases hi : (⟨i, h⟩ : Fin c.n) = i0
      · have hv : i = i0.val := by rw [← hi]
        subst hi
        simp [flipAt]
      · have hv : i ≠ i0.val := fun e => hi (Fin.ext e)
        simp [flipAt, Function.update_of_ne hi, hv]
    · simp only [dif_neg h]
      have hv : i ≠ i0.val := by have := i0.isLt; omega
      simp [hv]
  rw [List.map_congr_left hpt, foldl_xor_map, foldl_xor_indicator, hodd]
  simp

open Classical in
/-- A parity with an index of odd multiplicity is true on exactly half of the cube. -/
theorem parity_half (c : Call) (i0 : Fin c.n) (hodd : c.parity.count i0.val % 2 = 1) (b : Bool) :
    ((Finset.univ.filter fun z : BitInput c.n => c.parityOf z = b).card : ℚ) = 2 ^ c.n / 2 := by
  have hbij : ((Finset.univ.filter fun z : BitInput c.n => c.parityOf z = b).card) =
      ((Finset.univ.filter fun z : BitInput c.n => c.parityOf z = !b).card) := by
    apply Finset.card_nbij' (flipAt i0) (flipAt i0)
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      rw [parityOf_flip c i0 hodd, hz]
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      rw [parityOf_flip c i0 hodd, hz, Bool.not_not]
    · intro z _; exact flipAt_flipAt i0 z
    · intro z _; exact flipAt_flipAt i0 z
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitInput c.n)))
    (fun z => c.parityOf z = b)
  have hnot : ((Finset.univ : Finset (BitInput c.n)).filter fun z => ¬ c.parityOf z = b) =
      (Finset.univ.filter fun z : BitInput c.n => c.parityOf z = !b) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases c.parityOf z <;> cases b <;> simp
  rw [hnot, ← hbij, Finset.card_univ] at htot
  have hcard : Fintype.card (BitInput c.n) = 2 ^ c.n := by simp
  rw [hcard] at htot
  have : ((Finset.univ.filter fun z : BitInput c.n => c.parityOf z = b).card : ℚ) * 2 = 2 ^ c.n := by
    exact_mod_cast (by omega : (Finset.univ.filter fun z : BitInput c.n => c.parityOf z = b).card * 2 = 2 ^ c.n)
  linarith

/-! ## The exact value -/

theorem coeffs_nil_of_topWeight {n : ℕ} (C : NCircuit n) (hnz : ∀ a ∈ C.coeffs, a ≠ 0) (hW : C.topWeight = 0) :
    C.coeffs = [] := by
  unfold NCircuit.topWeight at hW
  cases h : C.coeffs with
  | nil => rfl
  | cons a as =>
    rw [h] at hW hnz
    simp only [List.map_cons, List.sum_cons] at hW
    have : a.natAbs = 0 := by omega
    exact absurd (Int.natAbs_eq_zero.mp this) (hnz a (by simp))

theorem eval_of_zero {n : ℕ} (C : NCircuit n) (hlen : C.gates.length = C.coeffs.length)
    (hnz : ∀ a ∈ C.coeffs, a ≠ 0) (hW : C.topWeight = 0) (z : BitInput n) : C.eval z = topLookup C 0 := by
  have hc := coeffs_nil_of_topWeight C hnz hW
  have hg : C.gates = [] := by rw [hc] at hlen; exact List.eq_nil_of_length_eq_zero hlen
  rw [eval_eq_topLookup, score_eq_linForm, hg, hc]
  rfl

open Classical in
theorem prob_const (c : Call) (b : Bool) (h : ∀ z, c.predicate z = b) : c.prob = if b then 1 else 0 := by
  unfold Call.prob
  have hcard : Fintype.card (BitInput c.n) = 2 ^ c.n := by simp
  cases b
  · have : (Finset.univ.filter fun z : BitInput c.n => c.predicate z = true) = ∅ := by
      ext z; simp [h z]
    rw [this]; simp
  · have : (Finset.univ.filter fun z : BitInput c.n => c.predicate z = true) = Finset.univ := by
      ext z; simp [h z]
    rw [this, Finset.card_univ, hcard]
    simp

/-- The `W = 0` branch is exact (lines 1636–1640). -/
theorem zeroWeightValue_exact {B1 B2 : ℕ} (c : Call) (hadm : c.Admitted B1 B2) (hW : c.W = 0) :
    (zeroWeightValue c).1 = c.prob := by
  classical
  have hW1 : c.first.topWeight = 0 := by unfold Call.W at hW; omega
  have hW2 : c.second.topWeight = 0 := by unfold Call.W at hW; omega
  have he1 := eval_of_zero c.first hadm.2.1.1 hadm.2.1.2.1 hW1
  have he2 := eval_of_zero c.second hadm.2.2.1.1 hadm.2.2.1.2.1 hW2
  rcases kind_cases c with hk | hk | hk
  · rw [prob_const c (topLookup c.first 0) (fun z => by simp [Call.predicate, hk, he1])]
    simp [zeroWeightValue, hk]
  · rw [prob_const c (xor (topLookup c.first 0) (topLookup c.second 0))
      (fun z => by simp [Call.predicate, hk, he1, he2])]
    simp [zeroWeightValue, hk]
  · have hlt : ∀ i ∈ c.parity, i < c.n := hadm.2.2.2.2.2.1
    by_cases hodd : oddIndices c = []
    · have heven : ∀ i, i < c.n → c.parity.count i % 2 = 0 := by
        intro i hi
        have := List.filter_eq_nil_iff.mp hodd i (List.mem_range.mpr hi)
        simp only [decide_eq_true_eq] at this
        omega
      rw [prob_const c (topLookup c.first 0)
        (fun z => by simp [Call.predicate, hk, he1, parityOf_even c heven hlt z])]
      simp [zeroWeightValue, hk, hodd]
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hodd
      simp only [oddIndices, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
      have hhalf := parity_half c ⟨i, hi.1⟩ hi.2 (!topLookup c.first 0)
      unfold Call.prob
      have hfilter : (Finset.univ.filter fun z : BitInput c.n => c.predicate z = true) =
          (Finset.univ.filter fun z : BitInput c.n => c.parityOf z = !topLookup c.first 0) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Call.predicate, hk, he1]
        cases topLookup c.first 0 <;> cases c.parityOf z <;> simp
      rw [hfilter, hhalf]
      simp only [zeroWeightValue, hk, hodd, if_false]
      field_simp

end NearCubicGates.Close.Counter

/-!
# prop:sound for every call and every witness; dyadic outputs (paper v2 lines 1561–1562, 1741–1767)

`counterOnCall_sound`: for every call `c` (admitted or not) and every witness word `w`, the returned interval
contains `Pr[C(z) = 1]`. `counterOnCall_dyadic`: both returned numbers are dyadic.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

theorem length_readBlock (bits : List Bool) (ws : List ℕ) : (readBlock bits ws).1.length = ws.length := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih => simp [readBlock, ih]

theorem filterMap_fin_length {n : ℕ} (l : List ℕ) (hl : ∀ i ∈ l, i < n) :
    (l.filterMap fun i => if h : i < n then some (⟨i, h⟩ : Fin n) else none).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := hl a (by simp)
    simp only [List.filterMap_cons, dif_pos ha, List.length_cons]
    rw [ih (fun i hi => hl i (by simp [hi]))]

theorem filterMap_fin_nodup {n : ℕ} (l : List ℕ) (hl : l.Nodup) :
    (l.filterMap fun i => if h : i < n then some (⟨i, h⟩ : Fin n) else none).Nodup := by
  apply hl.filterMap
  intro a a' b ha ha'
  by_cases h1 : a < n
  · by_cases h2 : a' < n
    · simp only [dif_pos h1, dif_pos h2, Option.mem_def, Option.some.injEq] at ha ha'
      rw [← ha] at ha'
      exact congrArg Fin.val ha'.symm
    · simp [dif_neg h2] at ha'
  · simp [dif_neg h1] at ha

/-- A decoded witness has exactly `k` inner coordinates. -/
theorem decodeWitness_card (c : Call) (p : Params) (w : List Bool) (wt : Wit c.n)
    (h : decodeWitness c p w = some wt) : wt.I.card = p.k := by
  unfold decodeWitness at h
  simp only at h
  split_ifs at h with hok
  cases h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hlt, hnd⟩, _⟩ := hok
  rw [List.toFinset_card_of_nodup (filterMap_fin_nodup _ hnd), filterMap_fin_length _ hlt, length_readBlock,
    List.length_replicate]

theorem prob_bounds (c : Call) : 0 ≤ c.prob ∧ c.prob ≤ 1 := by
  classical
  unfold Call.prob
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (BitInput c.n)) (fun z => c.predicate z = true)
  rw [Finset.card_univ] at h
  have hcard : Fintype.card (BitInput c.n) = 2 ^ c.n := by simp
  rw [hcard] at h
  exact_mod_cast h

theorem defaultValue_sound (c : Call) : |defaultValue.1 - c.prob| ≤ defaultValue.2 := by
  have h := prob_bounds c
  simp only [defaultValue]
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

open Classical in
/-- prop:sound: every call, every witness. -/
theorem counterOnCall_sound (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    |(counterOnCall B1 B2 cT c w).1 - c.prob| ≤ (counterOnCall B1 B2 cT c w).2 := by
  unfold counterOnCall
  by_cases hadm : c.Admitted B1 B2
  · rw [if_pos hadm]
    by_cases hW : c.W = 0
    · rw [if_pos hW, zeroWeightValue_exact c hadm hW, zeroWeightValue_radius, sub_self, abs_zero]
    · rw [if_neg hW]
      cases hsel : selectParams cT (header c) with
      | none => exact defaultValue_sound c
      | some p =>
        simp only
        cases hdec : decodeWitness c p w with
        | none => exact defaultValue_sound c
        | some wt =>
          simp only
          have hs := selectParams_spec cT (header c) p hsel
          exact outputOf_sound c p wt hs (decodeWitness_card c p w wt hdec)
            (k_pos_of hs (by simp only [header]; have := hadm.1; omega))
  · rw [if_neg hadm]
    exact defaultValue_sound c

/-! ## Dyadic outputs -/

theorem isDyadic_of_mul (q : ℚ) (k : ℕ) (z : ℤ) (h : q * 2 ^ k = z) : IsDyadic q :=
  ⟨k, by rw [h]; rfl⟩

theorem isDyadic_of_int (z : ℤ) : IsDyadic (z : ℚ) := ⟨0, by simp⟩

open Classical in
theorem outputOf_dyadic (c : Call) (p : Params) (wt : Wit c.n) :
    IsDyadic (outputOf c p wt).1 ∧ IsDyadic (outputOf c p wt).2 := by
  simp only [outputOf]
  have hint : ∃ z : ℤ, ∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
      cellCount c p wt y = z := by
    have hz : ∀ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
        (cellCount c p wt y : ℚ) = ((cellCount c p wt y).num : ℚ) := by
      intro y hy
      have hden := (Finset.mem_filter.mp hy).2.2.2.1
      exact (Rat.coe_int_num_of_den_eq_one hden).symm
    refine ⟨∑ y ∈ (Finset.univ : Finset (Cells wt.I)).filter (fun y => Certain c p wt y),
      (cellCount c p wt y).num, ?_⟩
    rw [Finset.sum_congr rfl hz]
    push_cast
    rfl
  obtain ⟨z, hz⟩ := hint
  constructor
  · refine isDyadic_of_mul _ c.n (z + 2 ^ (p.k - 1) *
      ((Finset.univ.filter fun y => ¬ Certain c p wt y).card : ℤ)) ?_
    rw [hz]
    push_cast
    field_simp
  · refine isDyadic_of_mul _ c.n (2 ^ (p.k - 1) * ((Finset.univ.filter fun y => ¬ Certain c p wt y).card : ℤ)) ?_
    push_cast
    field_simp

theorem half_dyadic : IsDyadic (1 / 2 : ℚ) := isDyadic_of_mul _ 1 1 (by norm_num)

theorem zeroWeightValue_dyadic (c : Call) : IsDyadic (zeroWeightValue c).1 ∧ IsDyadic (zeroWeightValue c).2 := by
  have h0 : IsDyadic (0 : ℚ) := by simpa using isDyadic_of_int 0
  have h1 : IsDyadic (1 : ℚ) := by simpa using isDyadic_of_int 1
  unfold zeroWeightValue
  split
  · dsimp only; split <;> exact ⟨by assumption, h0⟩
  · dsimp only; split <;> exact ⟨by assumption, h0⟩
  · split
    · dsimp only; split <;> exact ⟨by assumption, h0⟩
    · exact ⟨half_dyadic, h0⟩

open Classical in
theorem counterOnCall_dyadic (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    IsDyadic (counterOnCall B1 B2 cT c w).1 ∧ IsDyadic (counterOnCall B1 B2 cT c w).2 := by
  have hdef : IsDyadic defaultValue.1 ∧ IsDyadic defaultValue.2 := ⟨half_dyadic, half_dyadic⟩
  unfold counterOnCall
  split_ifs
  · exact zeroWeightValue_dyadic c
  · split
    · exact hdef
    · split
      · exact hdef
      · exact outputOf_dyadic c _ _
  · exact hdef

end NearCubicGates.Close.Counter

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires NearCubicWires.RepairRepresentation

/-- `f` is a prefix code: an encoding followed by anything determines the encoded value and the rest. -/
def PrefixCode {α : Type*} (f : α → List Bool) : Prop :=
  ∀ a b (s t : List Bool), f a ++ s = f b ++ t → a = b ∧ s = t

theorem natWord_prefixCode : PrefixCode natWord := by
  intro a b s t h
  have hab : a = b := Bindings.Williams14.natWord_eq_of_prefix (L := natWord a ++ s)
    (List.prefix_append _ _) (by rw [h]; exact List.prefix_append _ _)
  subst hab
  exact ⟨rfl, List.append_cancel_left h⟩

theorem prefixCode_append {α β : Type*} {f : α → List Bool} {g : β → List Bool} (hf : PrefixCode f)
    (hg : PrefixCode g) {a a' : α} {b b' : β} {s t : List Bool}
    (h : f a ++ g b ++ s = f a' ++ g b' ++ t) : a = a' ∧ b = b' ∧ s = t := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨rfl, h2⟩ := hf a a' _ _ h
  obtain ⟨rfl, h3⟩ := hg b b' s t h2
  exact ⟨rfl, rfl, h3⟩

theorem flatMap_prefixCode {α : Type*} {f : α → List Bool} (hf : PrefixCode f) :
    ∀ (xs ys : List α) (s t : List Bool), xs.length = ys.length →
      xs.flatMap f ++ s = ys.flatMap f ++ t → xs = ys ∧ s = t
  | [], [], s, t, _, h => by simpa using h
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | x :: xs, y :: ys, s, t, hl, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := hf x y _ _ h
    obtain ⟨rfl, h3⟩ := flatMap_prefixCode hf xs ys s t (by simpa using hl) h2
    exact ⟨rfl, h3⟩

theorem listWord_prefixCode {α : Type} {f : α → List Bool} (hf : PrefixCode f) : PrefixCode (listWord f) := by
  intro xs ys s t h
  unfold listWord at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hl, h2⟩ := natWord_prefixCode _ _ _ _ h
  exact flatMap_prefixCode hf xs ys s t hl h2

theorem intWord_prefixCode : PrefixCode Interfaces.intWord := by
  intro a b s t h
  unfold Interfaces.intWord at h
  obtain ⟨hsign, habs, hst⟩ := prefixCode_append natWord_prefixCode natWord_prefixCode h
  refine ⟨?_, hst⟩
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp only [ha, hb, if_true, if_false] at hsign <;> omega

theorem bitWord_prefixCode : PrefixCode bitWord := by
  intro a b s t h
  unfold bitWord at h
  obtain ⟨hab, hst⟩ := natWord_prefixCode _ _ _ _ h
  refine ⟨?_, hst⟩
  cases a <;> cases b <;> simp_all

theorem gateWord_prefixCode (n : ℕ) : PrefixCode (gateWord (n := n)) := by
  intro g g' s t h
  unfold gateWord at h
  obtain ⟨hw, hth, hst⟩ := prefixCode_append (listWord_prefixCode intWord_prefixCode) intWord_prefixCode h
  refine ⟨?_, hst⟩
  have hw' : g.weight = g'.weight := List.ofFn_injective hw
  cases g; cases g'
  simp_all

theorem circuitWord_prefixCode (n : ℕ) : PrefixCode (circuitWord (n := n)) := by
  intro C C' s t h
  unfold circuitWord at h
  rw [List.append_assoc (listWord gateWord C.gates ++ _), List.append_assoc (listWord gateWord C'.gates ++ _)] at h
  obtain ⟨hg, hc, h2⟩ := prefixCode_append (listWord_prefixCode (gateWord_prefixCode n))
    (listWord_prefixCode intWord_prefixCode) (by simpa only [List.append_assoc] using h)
  obtain ⟨ht, hst⟩ := listWord_prefixCode bitWord_prefixCode _ _ _ _ h2
  refine ⟨?_, hst⟩
  cases C; cases C'
  simp_all

theorem ratWord_prefixCode : PrefixCode ratWord := by
  intro a b s t h
  unfold ratWord at h
  obtain ⟨hn, hd, hst⟩ := prefixCode_append intWord_prefixCode natWord_prefixCode h
  exact ⟨Rat.ext hn hd, hst⟩

theorem kindTag_injective : Function.Injective kindTag := by
  intro a b h
  cases a <;> cases b <;> simp_all [kindTag]

theorem callWord_injective : Function.Injective callWord := by
  intro c c' h
  obtain ⟨n, kind, first, second, parity, radius⟩ := c
  obtain ⟨n', kind', first', second', parity', radius'⟩ := c'
  unfold callWord at h
  simp only [List.append_assoc] at h
  obtain ⟨rfl, h1⟩ := natWord_prefixCode _ _ _ _ h
  obtain ⟨hk, h2⟩ := natWord_prefixCode _ _ _ _ h1
  obtain ⟨rfl, h3⟩ := circuitWord_prefixCode n _ _ _ _ h2
  obtain ⟨rfl, h4⟩ := circuitWord_prefixCode n _ _ _ _ h3
  obtain ⟨rfl, h5⟩ := listWord_prefixCode natWord_prefixCode _ _ _ _ h4
  obtain ⟨rfl, _⟩ := ratWord_prefixCode _ _ [] [] (by simpa using h5)
  rw [kindTag_injective hk]

open Classical in

noncomputable def value (B1 B2 cT : ℕ) (raw w : List Bool) : ℚ × ℚ :=
  if h : ∃ c : Call, callWord c = raw then counterOnCall B1 B2 cT (Classical.choose h) w else defaultValue

theorem value_callWord (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    value B1 B2 cT (callWord c) w = counterOnCall B1 B2 cT c w := by
  have h : ∃ c' : Call, callWord c' = callWord c := ⟨c, rfl⟩
  unfold value
  rw [dif_pos h, callWord_injective (Classical.choose_spec h)]

theorem value_sound (B1 B2 cT : ℕ) (c : Call) (w : List Bool) :
    |(value B1 B2 cT (callWord c) w).1 - c.prob| ≤ (value B1 B2 cT (callWord c) w).2 := by
  rw [value_callWord]
  exact counterOnCall_sound B1 B2 cT c w

theorem value_dyadic (B1 B2 cT : ℕ) (raw w : List Bool) :
    IsDyadic (value B1 B2 cT raw w).1 ∧ IsDyadic (value B1 B2 cT raw w).2 := by
  unfold value
  split_ifs
  · exact counterOnCall_dyadic B1 B2 cT _ w
  · exact ⟨half_dyadic, half_dyadic⟩

theorem witnessBound_poly : ∃ C k : ℕ, ∀ n, witnessBound n ≤ C * (n + 1) ^ k := ⟨7, 5, fun _ => le_rfl⟩

theorem value_complete
    (hR : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hB : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (hP : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 B2 cT : ℕ) (hB1 : 0 < B1) (hcT : 0 < cT) :
    ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 →
      (c.kind = .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A3 c.n) →
      (c.kind ≠ .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A1 c.n) →
      ∃ w : List Bool, w.length ≤ witnessBound c.n ∧ (value B1 B2 cT (callWord c) w).2 ≤ c.radius := by
  obtain ⟨a, ha, onset, h⟩ := counter_complete hR hB hP B1 B2 cT hB1 hcT
  refine ⟨a, ha, onset, fun c hn hadm hp hs => ?_⟩
  obtain ⟨w, hw, hr⟩ := h c hn hadm hp hs
  exact ⟨w, hw, by rw [value_callWord]; exact hr⟩

end NearCubicGates.Close.Counter

/-!
# prop:time: the counts (paper v2 lines 1813–1859)

The per-step counts the machine budget cites, all in terms of the selected parameters:
* `requestCount_le`: at most `P^{2J+4}` tabulated requests (joint residue counts of `J+1` forms per role for every
  prime and residue vector, the parity split, and the moments; line 1820);
* `card_cells`: `2^{n−k}` cells; `jointCount_le`: every tabulated count is at most `2^k`;
* `digitVectors_card_le`: at most `P^{2J}` digit vectors per cell (line 1823);
* `box_card_le`, `Lw_le`: every reconstruction box has at most `L_w^2 ≤ (1+P²)²` points (`D' ≤ 1+P²`, line 1825);
* `rows_le`: every residue system has at most `P³` rows;
* `P_le_n`, `J_le_Jmax`, `k_le_n`: the elementary bounds `P ≤ n`, `J ≤ J_max`, `k ≤ n` (line 1844);
* `time_budget`: a workload `C · 2^{n−k} n^{2J_max+c₃}` with `C ≤ n²` fits `2^n/n^{μ_n}` once `c_T ≥ c₃ + 2`
  (lines 1838–1849; this is the already-proved `SavedClockArithmetic.workload_fits_clock`).
The prime number theorem is not needed for prop:time: only `P ≤ n` and `J ≤ J_max` enter.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates NearCubicGates.Close.Interfaces NearCubicWires

section Counts

variable {cT : ℕ} (c : Call) (p : Params) (hs : Spec cT (header c) p)
include hs

theorem P_le_n : p.P ≤ c.n := by
  rw [hs.P_eq]; exact (Nat.findGreatest_le _).trans (Nat.min_le_left _ _)

theorem J_le_Jmax : p.J ≤ Jmax c.n := by
  have h1 := (leastUpTo_spec _ _ _ hs.J_eq).2.1
  have h2 := hs.J_pos
  simp only [header, Jmax] at h1 ⊢
  omega

theorem k_le_n : p.k ≤ c.n := hs.k_lt.le

theorem primes_card_le : p.primes.card ≤ p.P := by
  have hsub : p.primes ⊆ Finset.Icc 1 p.P := by
    intro q hq
    rw [Finset.mem_Icc]
    exact ⟨(primes_prime hs q hq).one_lt.le, primes_le hs q hq⟩
  simpa using Finset.card_le_card hsub

theorem window_le : p.window ≤ 1 + p.P ^ 2 := by
  rw [hs.window_eq]
  unfold ScalarWindow.window
  have h : ∑ q ∈ p.primes, (q - 1) ≤ ∑ _q ∈ p.primes, p.P :=
    Finset.sum_le_sum fun q hq => (Nat.sub_le q 1).trans (primes_le hs q hq)
  rw [Finset.sum_const, smul_eq_mul] at h
  have h2 := Nat.mul_le_mul_right p.P (primes_card_le c p hs)
  nlinarith

theorem Lw_le : p.Lw ≤ 1 + p.P ^ 2 := by
  have hw := window_le c p hs
  rw [hs.Lw_eq]
  unfold windowInUse
  split_ifs
  · rw [hs.L2_eq]
    rcases pairSide_le_window p.window with h | h
    · exact h.trans hw
    · omega
  · exact hw

/-- Number of forms whose joint residues are tabulated per part: `J` digits and one score per role. -/
def formCount : ℕ := roleCount c.kind * (p.J + 1)

/-- The tabulated requests: every part, prime and residue vector of all forms, plus the `d(J+1)` moments. -/
def requestCount : ℕ := (parts c).length * (∑ q ∈ p.primes, q ^ formCount c p) + roleCount c.kind * (p.J + 1)

omit hs in
theorem roleCount_le_two : roleCount c.kind ≤ 2 := by cases c.kind <;> decide

omit hs in
theorem parts_length_le : (parts c).length ≤ 2 := by unfold parts; split_ifs <;> simp

omit hs in
theorem formCount_le : formCount c p ≤ 2 * p.J + 2 := by
  unfold formCount
  have := roleCount_le_two c
  nlinarith

/-- At most `P^{2J+4}` tabulations (line 1820). -/
theorem requestCount_le : requestCount c p ≤ p.P ^ (2 * p.J + 4) := by
  have hP := hs.P_large
  have hP1 : 1 ≤ p.P := by omega
  have hsum : ∑ q ∈ p.primes, q ^ formCount c p ≤ p.P * p.P ^ (2 * p.J + 2) := by
    calc ∑ q ∈ p.primes, q ^ formCount c p ≤ ∑ _q ∈ p.primes, p.P ^ (2 * p.J + 2) :=
          Finset.sum_le_sum fun q hq => (Nat.pow_le_pow_left (primes_le hs q hq) _).trans
            (Nat.pow_le_pow_right hP1 (formCount_le c p))
      _ = p.primes.card * p.P ^ (2 * p.J + 2) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ p.P * p.P ^ (2 * p.J + 2) := Nat.mul_le_mul_right _ (primes_card_le c p hs)
  have hmom : roleCount c.kind * (p.J + 1) ≤ p.P ^ (2 * p.J + 2) := by
    have h1 : roleCount c.kind * (p.J + 1) ≤ 2 * (p.J + 1) := Nat.mul_le_mul_right _ (roleCount_le_two c)
    have h2 : 2 * (p.J + 1) ≤ 2 ^ (2 * p.J + 2) := by
      have := Nat.lt_two_pow_self (n := 2 * p.J + 2)
      omega
    exact h1.trans (h2.trans (Nat.pow_le_pow_left (by omega) _))
  unfold requestCount
  have hparts := parts_length_le c
  calc (parts c).length * (∑ q ∈ p.primes, q ^ formCount c p) + roleCount c.kind * (p.J + 1)
      ≤ 2 * (p.P * p.P ^ (2 * p.J + 2)) + p.P ^ (2 * p.J + 2) := by gcongr
    _ ≤ 3 * (p.P * p.P ^ (2 * p.J + 2)) := by
        have : p.P ^ (2 * p.J + 2) ≤ p.P * p.P ^ (2 * p.J + 2) := Nat.le_mul_of_pos_left _ (by omega)
        omega
    _ ≤ p.P * (p.P * p.P ^ (2 * p.J + 2)) := Nat.mul_le_mul_right _ (by omega)
    _ = p.P ^ (2 * p.J + 4) := by ring

/-- At most `P^{2J}` digit vectors per cell (line 1823). -/
theorem digitVectors_card_le (wt : Wit c.n) (y : Cells wt.I) : (digitVectors c p wt y).card ≤ p.P ^ (2 * p.J) := by
  unfold digitVectors
  rw [Fintype.card_piFinset]
  have hP := hs.P_large
  have hE : 2 * p.hE ≤ p.P := by rw [hs.hE_eq]; omega
  calc ∏ rj : Role c × Fin p.J, (Finset.Ioo
        (digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I)) - p.hE)
        (digit c p wt rj.1.val rj.2.val (extend wt.I y (zeroPoint wt.I)) + p.hE)).card
      ≤ ∏ _rj : Role c × Fin p.J, p.P := by
        apply Finset.prod_le_prod'
        intro rj _
        rw [Int.card_Ioo]
        omega
    _ = p.P ^ (roleCount c.kind * p.J) := by simp [Finset.prod_const, Fintype.card_prod]
    _ ≤ p.P ^ (2 * p.J) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (roleCount_le_two c))

/-- Every reconstruction box has at most `L_w^2` points (line 1708). -/
theorem box_card_le (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ) :
    (box c p wt y κ).card ≤ p.Lw ^ 2 := by
  unfold box
  rw [Fintype.card_piFinset]
  have hLw := Lw_pos hs
  calc ∏ r : Role c, (Finset.Icc (boxLo c p wt y κ r) (boxHi c p wt y κ r)).card ≤ ∏ _r : Role c, p.Lw := by
        apply Finset.prod_le_prod'
        intro r _
        rw [Int.card_Icc]
        have := box_width c p wt y hs κ r
        omega
    _ = p.Lw ^ roleCount c.kind := by simp [Finset.prod_const]
    _ ≤ p.Lw ^ 2 := Nat.pow_le_pow_right (by omega) (roleCount_le_two c)

/-- Every residue system has at most `P³` rows. -/
theorem rows_le : ∑ q ∈ p.primes, q ^ roleCount c.kind ≤ p.P ^ 3 := by
  have hP := hs.P_large
  calc ∑ q ∈ p.primes, q ^ roleCount c.kind ≤ ∑ _q ∈ p.primes, p.P ^ 2 :=
        Finset.sum_le_sum fun q hq => (Nat.pow_le_pow_left (primes_le hs q hq) _).trans
          (Nat.pow_le_pow_right (by omega) (roleCount_le_two c))
    _ = p.primes.card * p.P ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ p.P * p.P ^ 2 := Nat.mul_le_mul_right _ (primes_card_le c p hs)
    _ = p.P ^ 3 := by ring

omit hs in
/-- Every tabulated count is at most `2^k` (the right sides of the residue systems, line 1830). -/
theorem jointCount_le (wt : Wit c.n) (hk : wt.I.card = p.k) (q : ℕ) (part : Option Bool) (y : Cells wt.I)
    (κ : Role c × Fin p.J → ℤ) (σ : Role c → ℤ) : jointCount c p wt q part y κ σ ≤ 2 ^ p.k := by
  unfold jointCount
  have h := Finset.card_filter_le (Finset.univ : Finset (Points wt.I)) (fun x => inPart c wt part x = true ∧
    (∀ rj : Role c × Fin p.J, digit c p wt rj.1.val rj.2.val (extend wt.I y x) ≡ κ rj [ZMOD (q : ℤ)]) ∧
    ∀ r : Role c, scoreForm c r.val (extend wt.I y x) ≡ σ r [ZMOD (q : ℤ)])
  rw [Finset.card_univ, card_points c p wt hk] at h
  convert h

omit hs in
/-- `2^{n−k}` cells. -/
theorem cells_card (wt : Wit c.n) (hk : wt.I.card = p.k) : Fintype.card (Cells wt.I) = 2 ^ (c.n - p.k) := by
  simp only [Cells, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe, hk]

end Counts

/-- The final exponent bookkeeping of prop:time (lines 1838–1849): with `c_T ≥ c₃ + 2`, a workload
`C · 2^{n−k} n^{2J_max+c₃}` with `C ≤ n²` is within `2^n/n^{μ_n}`. -/
theorem time_budget {cT : ℕ} (c : Call) (p : Params) (hs : Spec cT (header c) p) (c3 C : ℕ)
    (hcT : c3 + 2 ≤ cT) (hC : C ≤ c.n ^ 2) :
    C * (2 ^ (c.n - p.k) * c.n ^ (2 * Jmax c.n + c3)) * c.n ^ Target.mu c.n ≤ 2 ^ c.n := by
  have hk : p.k = SavedClockArithmetic.innerWidth c.n (Jmax c.n) cT := by
    rw [hs.k_eq]; simp [header, inner, SavedClockArithmetic.innerWidth]
  have hn : 0 < c.n := by have : p.k < c.n := hs.k_lt; omega
  have h := SavedClockArithmetic.workload_fits_clock (stages := Jmax c.n) (overhead := c3) hn
    (by rw [← hk]; exact (show p.k < c.n from hs.k_lt).le) hcT hC
  rw [← hk] at h
  unfold SavedClockArithmetic.savedClock at h
  exact (Nat.le_div_iff_mul_le (by positivity)).mp h

/-- The default and guard paths: a polynomial workload fits `2^n/n^{μ_n}` for large `n` (line 1850: "A call that fails
a parsing or public guard stops with the default after polynomially many steps"). -/
theorem poly_fits_clock (C e : ℕ) : ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
    C * (n + 1) ^ e * n ^ Target.mu n ≤ 2 ^ n := by
  obtain ⟨a, ha, hpoly⟩ := polynomial_le_binary (3 * e + 6) 2
  refine ⟨2 ^ (a + C + 4), ?_⟩
  intro n hn
  have hn4 : 4 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ (a + C + 4) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hlow : 2 ^ (Target.lambda n - 1) < n := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have hup : n ≤ 2 ^ Target.lambda n := Nat.le_pow_clog (by decide) n
  have hLa : a + C + 4 ≤ Target.lambda n := by
    have h := Nat.clog_mono_right 2 hn
    simpa only [Nat.clog_pow, show 1 < 2 by decide, if_pos, Target.lambda] using h
  set L := Target.lambda n with hL
  set q := L - 1 with hq
  have hmu : Target.mu n ≤ L := clog_le_self _
  have h1 : (n + 1) ^ e ≤ 2 ^ ((L + 1) * e) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left
    calc n + 1 ≤ 2 ^ L + 2 ^ L := by have := Nat.one_le_two_pow (n := L); omega
      _ = 2 ^ (L + 1) := by ring
  have h2 : n ^ Target.mu n ≤ 2 ^ (L * L) := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left hup _).trans (Nat.pow_le_pow_right (by positivity) hmu)
  have hC : C ≤ 2 ^ L := (Nat.lt_two_pow_self (n := C)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hexp : L + (L + 1) * e + L * L ≤ (3 * e + 6) * q ^ 2 := by
    have hq1 : 1 ≤ q := by omega
    have hLq : L = q + 1 := by omega
    rw [hLq]
    have a1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
    have a2' : q + 1 + 1 ≤ 3 * q ^ 2 := by nlinarith
    have a2 : (q + 1 + 1) * e ≤ 3 * q ^ 2 * e := Nat.mul_le_mul_right e a2'
    have a3 : (q + 1) * (q + 1) ≤ 4 * q ^ 2 := by nlinarith
    nlinarith
  have hbin := hpoly q (by omega)
  calc C * (n + 1) ^ e * n ^ Target.mu n ≤ 2 ^ L * 2 ^ ((L + 1) * e) * 2 ^ (L * L) := by gcongr
    _ = 2 ^ (L + (L + 1) * e + L * L) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ ((3 * e + 6) * q ^ 2) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ 2 ^ (2 ^ q) := Nat.pow_le_pow_right (by decide) hbin
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hlow.le

end NearCubicGates.Close.Counter

namespace NearCubicGates.Close.Counter

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

noncomputable def counterOfMachine
    (hR : PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction)
    (hB : PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (hP : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem)
    (B1 B2 cT : ℕ) (hB1 : 0 < B1) (hcT : 0 < cT)
    (budget : Call → List Bool → ℕ)
    (program : WordFunction (Call × List Bool) (fun r => frame (callWord r.1) ++ frame r.2)
      (fun r => outputWord (counterOnCall B1 B2 cT r.1 r.2)) (fun r => budget r.1 r.2))
    (fast : ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 → ∀ w : List Bool,
      budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n)
    (rest : ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ c.Admitted B1 B2 →
      budget c w ≤ K * ((callWord c).length + 1) ^ e) : Counter B1 B2 where
  value := counterOnCall B1 B2 cT
  budget := budget
  program := program
  dyadic := fun c w => counterOnCall_dyadic B1 B2 cT c w
  sound := counterOnCall_sound B1 B2 cT
  witnessLength := witnessBound
  witnessPoly := witnessBound_poly
  complete := by
    obtain ⟨a, ha, onset, h⟩ := value_complete hR hB hP B1 B2 cT hB1 hcT
    exact ⟨a, ha, onset, fun c hn hadm hp hs => by
      obtain ⟨w, hw, hr⟩ := h c hn hadm hp hs
      exact ⟨w, hw, by rw [value_callWord] at hr; exact hr⟩⟩
  fast := fast
  rest := rest

end NearCubicGates.Close.Counter
