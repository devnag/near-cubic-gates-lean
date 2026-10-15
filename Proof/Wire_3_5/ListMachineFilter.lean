import Proof.Wire_3_5.ListMachineRows
import Proof.Wire_3_5.Shared.GapFilter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk NearCubicWires.SupplierToeplitzCore

/-! ## Pascal's rule at the Boolean level -/

/-- The number of true bits among some polynomials at an assignment. -/
def trueCount (ls : List Poly) (ρ : ℕ → Bool) : ℕ := (ls.filter fun ℓ => F2Poly.eval ℓ ρ).length

theorem binomRefN_eval (ls : List Poly) (a : ℤ) (t : ℕ) (ρ : ℕ → Bool) :
    bitF2 (F2Poly.eval (binomRefN ls a t) ρ) = ((Ring.choose (a + trueCount ls ρ) t : ℤ) : ZMod 2) := by
  induction ls generalizing t with
  | nil => simp [binomRefN, trueCount, bitF2_chooseMod2]
  | cons ℓ ls ih =>
    cases t with
    | zero => simp [binomRefN, bitF2]
    | succ t =>
      simp only [binomRefN, eval_nadd, eval_nmul, bitF2_xor, bitF2_and, ih, trueCount, List.filter_cons]
      cases hℓ : F2Poly.eval ℓ ρ
      · simp [bitF2]
      · simp only [↓reduceIte, List.length_cons, bitF2]
        have hstep : a + (((ls.filter fun ℓ => F2Poly.eval ℓ ρ).length + 1 : ℕ) : ℤ) =
            (a + (((ls.filter fun ℓ => F2Poly.eval ℓ ρ).length : ℕ) : ℤ)) + 1 := by push_cast; ring
        rw [hstep, Ring.choose_succ_succ]
        push_cast
        ring

/-! ## Symmetric Boolean functions: the `𝔽₂` binomial inversion -/

/-- `binom(k, i)` is odd. -/
def chooseOdd (k i : ℕ) : Bool := k.choose i % 2 == 1

theorem bitF2_chooseOdd (k i : ℕ) : bitF2 (chooseOdd k i) = ((k.choose i : ℕ) : ZMod 2) := bitF2_nat_mod _

/-- The coefficient `c_k = ⊕_{i≤k} binom(k,i) f(i)` of `e_k` in the symmetric function `f`. -/
def symCoeff (f : ℕ → Bool) (k : ℕ) : Bool := (List.range (k + 1)).foldr (fun i b => xor (chooseOdd k i && f i) b) false

theorem bitF2_symCoeff (f : ℕ → Bool) (k : ℕ) :
    bitF2 (symCoeff f k) = ∑ i ∈ range (k + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) := by
  unfold symCoeff
  rw [← sum_range_list]
  generalize List.range (k + 1) = l
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, bitF2_xor, bitF2_and, bitF2_chooseOdd, ih, List.map_cons, List.sum_cons]

theorem sum_choose_mul (N n i : ℕ) (hn : n ≤ N) :
    ∑ k ∈ range (N + 1), k.choose i * n.choose k = n.choose i * 2 ^ (n - i) := by
  rcases Nat.lt_or_ge n i with hni | hin
  · rw [Nat.choose_eq_zero_of_lt hni, zero_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.lt_or_ge k i with hk | hk
    · rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (show n < k by omega), mul_zero]
  · rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ N + 1 by omega)]
    rw [Finset.sum_eq_zero (s := range i) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk), zero_mul]), zero_add, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j, (i + j).choose i * n.choose (i + j) = n.choose i * (n - i).choose j := by
      intro j
      rcases Nat.lt_or_ge n (i + j) with hlt | hle
      · rw [Nat.choose_eq_zero_of_lt hlt, mul_zero, Nat.choose_eq_zero_of_lt (show n - i < j by omega), mul_zero]
      · rw [mul_comm, Nat.choose_mul (n := n) (Nat.le_add_right i j), Nat.add_sub_cancel_left]
    simp_rw [hterm, ← Finset.mul_sum]
    congr 1
    rw [← Nat.sum_range_choose (n - i), ← Finset.sum_range_add_sum_Ico _ (show n - i + 1 ≤ N + 1 - i by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n - i + 1) (N + 1 - i)) (fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by have := (Finset.mem_Ico.mp hj).1; omega)]), add_zero]

theorem sum_choose_mul_mod_two (N n i : ℕ) (hn : n ≤ N) :
    ∑ k ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * ((n.choose k : ℕ) : ZMod 2) = if i = n then 1 else 0 := by
  have h := congrArg (fun x : ℕ => (x : ZMod 2)) (sum_choose_mul N n i hn)
  simp only [Nat.cast_sum, Nat.cast_mul] at h
  rw [h]
  rcases Nat.lt_trichotomy i n with hlt | heq | hgt
  · rw [if_neg (by omega), show n - i = (n - i - 1) + 1 by omega, pow_succ]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, mul_zero, mul_zero]
  · subst heq; simp
  · rw [Nat.choose_eq_zero_of_lt hgt, if_neg (by omega)]; simp

/-- **The `𝔽₂` binomial inversion**: `f(n) = Σ_{k≤N} c_k binom(n,k)` in `𝔽₂` for every `n ≤ N`. -/
theorem symInversion (f : ℕ → Bool) (N n : ℕ) (hn : n ≤ N) :
    bitF2 (f n) = ∑ k ∈ range (N + 1), bitF2 (symCoeff f k) * ((n.choose k : ℕ) : ZMod 2) := by
  have hwiden : ∀ k ∈ range (N + 1), bitF2 (symCoeff f k) =
      ∑ i ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) := by
    intro k hk
    rw [bitF2_symCoeff, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ N + 1 by have := Finset.mem_range.mp hk; omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (k + 1) (N + 1)) (fun i hi => by
      rw [Nat.choose_eq_zero_of_lt (by have := (Finset.mem_Ico.mp hi).1; omega)]; simp), add_zero]
  rw [Finset.sum_congr rfl fun k hk => by rw [hwiden k hk]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) * ((n.choose k : ℕ) : ZMod 2) =
      bitF2 (f i) * (if i = n then 1 else 0) := by
    intro i _
    rw [← sum_choose_mul_mod_two N n i hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (range (N + 1)) n, if_pos (Finset.mem_range.mpr (by omega))]

theorem bitF2_inj {a b : Bool} (h : bitF2 a = bitF2 b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **A symmetric Boolean function of `N` polynomial bits**, `f(#{true bits})`, as the explicit polynomial
`Σ_{k ≤ N} c_k·e_k` (reduced). -/
def symPolyRef (f : ℕ → Bool) (N : ℕ) (bs : List Poly) : Poly :=
  nsum ((List.range (N + 1)).map fun k => if symCoeff f k then binomRefN bs 0 k else pzero)

theorem symPolyRef_eval (f : ℕ → Bool) (N : ℕ) (bs : List Poly) (ρ : ℕ → Bool) (hN : trueCount bs ρ ≤ N) :
    F2Poly.eval (symPolyRef f N bs) ρ = f (trueCount bs ρ) := by
  have h := symInversion f N (trueCount bs ρ) hN
  have hb : bitF2 (F2Poly.eval (symPolyRef f N bs) ρ) = bitF2 (f (trueCount bs ρ)) := by
    rw [h]
    unfold symPolyRef
    rw [eval_nsum, eval_psum, ← sum_range_list]
    generalize List.range (N + 1) = l
    induction l with
    | nil => rfl
    | cons k l ih =>
      rw [List.map_cons, List.foldr_cons, bitF2_xor, ih, List.map_cons, List.sum_cons]
      congr 1
      split_ifs with hc
      · rw [binomRefN_eval, zero_add, hc]
        simp [bitF2, Ring.choose_natCast]
      · simp only [Bool.not_eq_true] at hc
        rw [eval_pzero, hc]; simp [bitF2]
  exact bitF2_inj hb

theorem binomRefN_size' (ls : List Poly) (L δ : ℕ) (hd : ∀ ℓ ∈ ls, DegLe ℓ δ) (ha : ∀ ℓ ∈ ls, AtomsLt ℓ L)
    (a : ℤ) (t : ℕ) : DegLe (binomRefN ls a t) (δ * t) ∧ AtomsLt (binomRefN ls a t) L := by
  induction ls generalizing t with
  | nil => exact ⟨degLe_pconst _ _, atomsLt_pconst _ _⟩
  | cons ℓ ls ih =>
    have hd' : ∀ ℓ' ∈ ls, DegLe ℓ' δ := fun ℓ' h => hd ℓ' (List.mem_cons_of_mem _ h)
    have ha' : ∀ ℓ' ∈ ls, AtomsLt ℓ' L := fun ℓ' h => ha ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => exact ⟨degLe_pone _, atomsLt_pone L⟩
    | succ t =>
      have hm := degLe_pmul (hd ℓ (List.mem_cons_self ..)) (ih hd' ha' t).1
      refine ⟨degLe_normalize (degLe_padd (ih hd' ha' (t + 1)).1 (degLe_normalize (hm.mono (by rw [Nat.mul_succ]; omega)))),
        atomsLt_normalize (atomsLt_padd (ih hd' ha' (t + 1)).2
          (atomsLt_normalize (atomsLt_pmul (ha ℓ (List.mem_cons_self ..)) (ih hd' ha' t).2)))⟩

theorem symPolyRef_size (f : ℕ → Bool) (N L δ : ℕ) (bs : List Poly) (hd : ∀ b ∈ bs, DegLe b δ)
    (ha : ∀ b ∈ bs, AtomsLt b L) : DegLe (symPolyRef f N bs) (δ * N) ∧ AtomsLt (symPolyRef f N bs) L := by
  unfold symPolyRef nsum
  refine ⟨degLe_normalize (degLe_psum ?_), atomsLt_normalize (atomsLt_psum ?_)⟩ <;> intro q hq <;>
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq <;> split_ifs
  · exact ((binomRefN_size' bs L δ hd ha 0 k).1).mono (Nat.mul_le_mul_left δ (by have := List.mem_range.mp hk; omega))
  · exact degLe_pzero _
  · exact (binomRefN_size' bs L δ hd ha 0 k).2
  · exact atomsLt_pzero L

/-! ## The filter's pieces -/

section Filter
variable (P : GapParams) {K : Type} (o : BiasOps K)

def parityPoly (c : CopySeed P K) (L : ℕ) : Poly :=
  ((List.range L).filter fun i => selected P c.1 i && biasBit o c.2.1 c.2.2 i).map fun i => [i]

theorem eval_singletons (l : List ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (l.map fun i => [i]) ρ = decide (Odd (l.filter ρ).length) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, eval_cons, ih, List.filter_cons]
    by_cases h : Odd (List.filter ρ l).length <;> cases hi : ρ i <;> simp [hi, h, Nat.odd_add_one]

theorem card_range_filter (L : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ((Finset.range L).filter q).card = ((List.range L).filter fun i => decide (q i)).length := by
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range]

theorem parityPoly_eval (c : CopySeed P K) (L : ℕ) (z : Fin L → Bool) :
    F2Poly.eval (parityPoly P o c L) (ext z) = copyParity P o c (List.ofFn z) := by
  unfold parityPoly copyParity selectedActive
  rw [eval_singletons, List.length_ofFn, Finset.filter_filter, card_range_filter, List.filter_filter]
  have hfil : List.filter (fun a => ext z a && (selected P c.1 a && biasBit o c.2.1 c.2.2 a)) (List.range L) =
      List.filter (fun i => decide (((List.ofFn z).getD i false = true ∧ selected P c.1 i = true) ∧
        biasBit o c.2.1 c.2.2 i = true)) (List.range L) := by
    apply List.filter_congr
    intro i hi
    have hi' := List.mem_range.mp hi
    have hg : (List.ofFn z).getD i false = ext z i := by simp [ext, hi', List.getD_eq_getElem?_getD]
    rw [hg]
    cases ext z i <;> cases selected P c.1 i <;> cases biasBit o c.2.1 c.2.2 i <;> rfl
  rw [hfil]

theorem parityPoly_size (c : CopySeed P K) (L : ℕ) : DegLe (parityPoly P o c L) 1 ∧ AtomsLt (parityPoly P o c L) L := by
  unfold parityPoly
  constructor
  · intro m hm; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm; simp
  · intro m hm j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_singleton] at hj
    subst hj
    exact List.mem_range.mp (List.mem_filter.mp hi).1

theorem trueCount_ofFn {n : ℕ} (g : Fin n → Poly) (ρ : ℕ → Bool) :
    trueCount (List.ofFn g) ρ = (Finset.univ.filter fun j => F2Poly.eval (g j) ρ = true).card := by
  rw [← count_ofFn_true n fun j => F2Poly.eval (g j) ρ, List.count_eq_length_filter, trueCount]
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.filter_map, List.filter_map, List.length_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro j _
  simp

def baseFilterPoly (s : BaseSeed P K) (L : ℕ) : Poly :=
  symPolyRef (fun k => decide (k ≤ 32)) 128 (List.ofFn fun j : Fin 128 => parityPoly P o (s j) L)

theorem baseFilterPoly_eval (s : BaseSeed P K) (L : ℕ) (z : Fin L → Bool) :
    F2Poly.eval (baseFilterPoly P o s L) (ext z) = baseFilter P o s (List.ofFn z) := by
  unfold baseFilterPoly
  rw [symPolyRef_eval _ _ _ _ (by rw [trueCount_ofFn]; exact (Finset.card_filter_le _ _).trans (by simp)),
    trueCount_ofFn]
  unfold baseFilter
  simp_rw [parityPoly_eval]

theorem baseFilterPoly_size (s : BaseSeed P K) (L : ℕ) :
    DegLe (baseFilterPoly P o s L) 128 ∧ AtomsLt (baseFilterPoly P o s L) L := by
  have := symPolyRef_size (fun k => decide (k ≤ 32)) 128 L 1 (List.ofFn fun j : Fin 128 => parityPoly P o (s j) L)
    (fun b hb => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb; exact (parityPoly_size P o (s j) L).1)
    (fun b hb => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb; exact (parityPoly_size P o (s j) L).2)
  unfold baseFilterPoly
  rw [one_mul] at this
  exact this

def gapFilterPoly (kEq : Fin (2 ^ P.fieldBits) ≃ K) (e : MargulisWalkSample P.baseSize P.walkLen) (L : ℕ) : Poly :=
  symPolyRef (fun k => decide ((P.walkLen + 1) / 2 ≤ k)) P.walkLen
    (List.ofFn fun time => baseFilterPoly P o (vertexSeed P kEq (e.vertex time)) L)

theorem gapFilterPoly_eval (kEq : Fin (2 ^ P.fieldBits) ≃ K) (e : MargulisWalkSample P.baseSize P.walkLen) (L : ℕ)
    (z : Fin L → Bool) : F2Poly.eval (gapFilterPoly P o kEq e L) (ext z) = gapFilterWith P o kEq e (List.ofFn z) := by
  unfold gapFilterPoly
  rw [symPolyRef_eval _ _ _ _ (by rw [trueCount_ofFn]; exact (Finset.card_filter_le _ _).trans (by simp)),
    trueCount_ofFn]
  unfold gapFilterWith concreteMajorityFailure concreteBadTimes concreteBadAt majorityThreshold
  simp_rw [baseFilterPoly_eval]

theorem gapFilterPoly_size (kEq : Fin (2 ^ P.fieldBits) ≃ K) (e : MargulisWalkSample P.baseSize P.walkLen) (L : ℕ) :
    DegLe (gapFilterPoly P o kEq e L) (128 * P.walkLen) ∧ AtomsLt (gapFilterPoly P o kEq e L) L := by
  have := symPolyRef_size (fun k => decide ((P.walkLen + 1) / 2 ≤ k)) P.walkLen L 128
    (List.ofFn fun time => baseFilterPoly P o (vertexSeed P kEq (e.vertex time)) L)
    (fun b hb => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb; exact (baseFilterPoly_size P o _ L).1)
    (fun b hb => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb; exact (baseFilterPoly_size P o _ L).2)
  unfold gapFilterPoly
  exact this

end Filter

end NearCubicWires.WireExponent3_5.ListMachine
