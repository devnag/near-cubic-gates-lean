import SourceAdapters.ShortPCP.VerifierDock

/-!
# The single-run verifier on an affine constraint instance: field, subspaces, constraint, acceptance

`V0` of the proof of `thm:short-pcp-ours`, Step 2, is `Request.runVerdict` of `Joins/SingleRun.lean` over
`F = 𝔽₂[X]/(irr)` with `φ = id`. This file proves the facts that connect it to the generic four-case argument of
`ShortPCP/Verifier.lean` (`SubVerifiers`, `ACSPInstance`):
- the domain basis `x^0, …, x^{f−1}` spans `F` (Step 2: the tables `p_0` and `p_1` are "both indexed by `F`"), and
  `GetRandElt` of `f` bits is the element of their word;
- the subspaces `H` and `I` of the request are the instance's (`def:acsp`: "its `i`-th element … is
  `o + Σ_j i_j b_j`, where `i_1, i_2, …` are the binary digits of `i`, least significant first") and are bases;
- the word of a field element (`Request.wordOf`) inverts `GF.rep` below `2^f`;
- the constraint circuit evaluates the constraint polynomial `P` (`def:acsp`: "a constraint polynomial … given by
  an arithmetic circuit"), so the composition `B_A` evaluates pointwise to `P(α, A(N_1(α)), …)`;
- membership in the sense of `ACSPInstance.Mem` is exactly `Instance.Accepts` (`def:acsp`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Verifier

open Finset Polynomial NearCubicWires.WireExponent3_5 NearCubicWires.CanonicalBinary
open NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun

/-! ## Sums over `List.range`, `GetRandElt`, words of bits -/

theorem list_sum_range {M : Type} [AddCommMonoid M] (n : ℕ) (φ : ℕ → M) :
    ((List.range n).map φ).sum = ∑ j ∈ Finset.range n, φ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem getRandElt_range {F : Type} [Field F] [DecidableEq F] (n : ℕ) (g : ℕ → F) (h : ℕ → Bool) (O : F) :
    getRandElt ((List.range n).map g) O ((List.range n).map h) =
      (∑ j ∈ Finset.range n, if h j then g j else 0) + O := by
  unfold getRandElt
  rw [List.zipWith_map, List.zipWith_self, list_sum_range]

theorem getRandElt_ofFn {F : Type} [Field F] [DecidableEq F] (n : ℕ) (g : ℕ → F) (b : Fin n → Bool) (O : F) :
    getRandElt ((List.range n).map g) O (List.ofFn b) =
      (∑ j : Fin n, if b j then g j.val else 0) + O := by
  have : List.ofFn b = (List.range n).map fun j => if h : j < n then b ⟨j, h⟩ else false := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp at h1
    simp [h1]
  rw [this, getRandElt_range, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [j.isLt]

theorem toPoly_eq_sum (a f : ℕ) (ha : a < 2 ^ f) :
    GF.toPoly a = ∑ j ∈ Finset.range f, if a.testBit j then (X : (ZMod 2)[X]) ^ j else 0 := by
  ext i
  rw [GF.coeff_toPoly, finsetSum_coeff]
  simp only [apply_ite (fun q : (ZMod 2)[X] => q.coeff i), coeff_X_pow, coeff_zero]
  rw [Finset.sum_eq_single i]
  · by_cases hi : i < f
    · simp [GF.bitF]
    · have : a.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [GF.bitF, this]
  · intro b _ hb; simp [Ne.symm hb]
  · intro hi
    simp only [Finset.mem_range, not_lt] at hi
    have : a.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))
    simp [this]

/-- `rep a = Σ_{j<f, bit j of a} rep (2^j)` for `a < 2^f`. -/
theorem rep_eq_sum (p a f : ℕ) (ha : a < 2 ^ f) :
    GF.rep p a = ∑ j ∈ Finset.range f, if a.testBit j then GF.rep p (2 ^ j) else 0 := by
  rw [GF.rep, toPoly_eq_sum a f ha, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [GF.rep, GF.toPoly_two_pow]

/-- The word of `f` bits, least significant first. -/
def maskOfBits {f : ℕ} (b : Fin f → Bool) : ℕ := ∑ j : Fin f, if b j then 2 ^ j.val else 0

/-- The bits of `a`, least significant first. -/
def bitsOf (f a : ℕ) : Fin f → Bool := fun j => a.testBit j.val

theorem testBit_maskOfBits {f : ℕ} (b : Fin f → Bool) (j : ℕ) :
    (maskOfBits b).testBit j = if h : j < f then b ⟨j, h⟩ else false := by
  induction f generalizing j with
  | zero => simp [maskOfBits]
  | succ f ih =>
    have hs : maskOfBits b = (if b 0 then 1 else 0) + 2 * maskOfBits (fun i : Fin f => b i.succ) := by
      unfold maskOfBits
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp [Fin.val_succ, pow_succ, mul_comm]
    rw [hs]
    rcases j with _ | j
    · rw [Nat.testBit_zero]; cases h0 : b 0 <;> simp [h0]
    · have hdiv : ((if b 0 = true then 1 else 0) + 2 * maskOfBits (fun i : Fin f => b i.succ)) / 2 =
          maskOfBits (fun i : Fin f => b i.succ) := by split_ifs <;> omega
      rw [Nat.testBit_succ, hdiv, ih]
      by_cases hj : j < f
      · simp [hj, Fin.succ_mk]
      · simp [hj]

theorem maskOfBits_lt {f : ℕ} (b : Fin f → Bool) : maskOfBits b < 2 ^ f := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_maskOfBits]
  simp [show ¬ j < f by omega]

theorem maskOfBits_bitsOf (f a : ℕ) (ha : a < 2 ^ f) : maskOfBits (bitsOf f a) = a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_maskOfBits]
  by_cases hj : j < f
  · simp [hj, bitsOf]
  · simp only [hj, ↓reduceDIte]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem bitsOf_maskOfBits {f : ℕ} (b : Fin f → Bool) : bitsOf f (maskOfBits b) = b := by
  funext j
  simp [bitsOf, testBit_maskOfBits, j.isLt]

theorem bitsValue_append_single (l : List Bool) (b : Bool) :
    bitsValue (l ++ [b]) = bitsValue l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => simp [bitsValue]
  | cons a l ih => simp only [List.cons_append, bitsValue, ih, List.length_cons, pow_succ]; ring

theorem bitsValue_range_map (f : ℕ) (g : ℕ → Bool) :
    bitsValue ((List.range f).map g) = maskOfBits fun j : Fin f => g j.val := by
  induction f with
  | zero => simp [bitsValue, maskOfBits]
  | succ f ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, bitsValue_append_single, ih, maskOfBits,
      maskOfBits, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, List.length_map, List.length_range]
    cases g f <;> simp

theorem map_eq_range_getD {α β : Type} (g : α → β) (d : α) (l : List α) :
    (List.range l.length).map (fun j => g (l.getD j d)) = l.map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp [h1]

/-! ## The field `F = 𝔽₂[X]/(irr)` and the domain basis -/

section Field

variable (c : Instance)

/-- The basis `x^0, …, x^{f−1}` of `F` (`Request.domBasis` at `φ = id`). -/
def monoBasis : List c.Fld := (List.range c.f).map fun j => c.elt (2 ^ j)

theorem length_monoBasis : (monoBasis c).length = c.f := by simp [monoBasis]

variable (hp : GF.ModulusOk c.irr c.f)
include hp

theorem elt_injOn {a b : ℕ} (ha : a < 2 ^ c.f) (hb : b < 2 ^ c.f) (h : c.elt a = c.elt b) : a = b :=
  GF.rep_injOn c.irr c.f a b hp ha hb h

theorem elt_surj (α : c.Fld) : ∃ a, a < 2 ^ c.f ∧ c.elt a = α := GF.rep_surj c.irr c.f hp α

omit hp in
/-- `elt a = Σ_{j<f, bit j of a} elt (2^j)` for `a < 2^f`. -/
theorem elt_eq_sum (a : ℕ) (ha : a < 2 ^ c.f) :
    c.elt a = ∑ j ∈ Finset.range c.f, if a.testBit j then c.elt (2 ^ j) else 0 :=
  rep_eq_sum c.irr a c.f ha

theorem elt_maskOfBits_bijective : Function.Bijective (fun b : Fin c.f → Bool => c.elt (maskOfBits b)) := by
  constructor
  · intro b b' h
    have := elt_injOn c hp (maskOfBits_lt b) (maskOfBits_lt b') h
    rw [← bitsOf_maskOfBits b, ← bitsOf_maskOfBits b', this]
  · intro α
    obtain ⟨a, ha, rfl⟩ := elt_surj c hp α
    exact ⟨bitsOf c.f a, by simp [maskOfBits_bitsOf c.f a ha]⟩

omit hp

variable [Fact (Irreducible c.irrPoly)] [DecidableEq c.Fld]

theorem getRandElt_mono (b : Fin c.f → Bool) :
    getRandElt (monoBasis c) 0 (List.ofFn b) = c.elt (maskOfBits b) := by
  rw [monoBasis, getRandElt_ofFn, add_zero, elt_eq_sum c _ (maskOfBits_lt b),
    ← Fin.sum_univ_eq_sum_range (fun j => if (maskOfBits b).testBit j then c.elt (2 ^ j) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp [testBit_maskOfBits, j.isLt]

theorem eltWithIndex_mono (a : ℕ) (ha : a < 2 ^ c.f) : eltWithIndex (monoBasis c) 0 (a + 1) = c.elt a := by
  have hb : (List.range (monoBasis c).length).map (fun j => (a + 1 - 1).testBit j) =
      List.ofFn (bitsOf c.f a) := by
    apply List.ext_getElem (by simp [monoBasis])
    intro i h1 h2
    simp [bitsOf]
  rw [eltWithIndex, hb, getRandElt_mono, maskOfBits_bitsOf c.f a ha]

include hp in
theorem mem_span_mono (α : c.Fld) : α ∈ span (monoBasis c) 0 := by
  obtain ⟨a, ha, rfl⟩ := elt_surj c hp α
  simp only [span, List.mem_toFinset, List.mem_map, List.mem_range, length_monoBasis]
  exact ⟨a, ha, eltWithIndex_mono c a ha⟩

include hp in
theorem span_mono_univ [Fintype c.Fld] : span (monoBasis c) 0 = univ :=
  Finset.eq_univ_of_forall (mem_span_mono c hp)

include hp in
theorem isBasis_mono : IsBasis (monoBasis c) 0 := by
  unfold IsBasis span
  rw [List.toFinset_card_of_nodup]
  · simp [monoBasis]
  · apply List.Nodup.map_on _ List.nodup_range
    intro i hi i' hi' h
    simp only [List.mem_range, length_monoBasis] at hi hi'
    rw [eltWithIndex_mono c i hi, eltWithIndex_mono c i' hi'] at h
    exact elt_injOn c hp hi hi' h

/-! ## Subspaces given by words: `H` and `I` -/

omit [Fact (Irreducible c.irrPoly)] [DecidableEq c.Fld] in
theorem map_elt_eq (l : List ℕ) :
    l.map c.elt = (List.range l.length).map fun j => c.elt (l.getD j 0) :=
  (map_eq_range_getD c.elt 0 l).symm

theorem eltWithIndex_map (l : List ℕ) (o i : ℕ) :
    eltWithIndex (l.map c.elt) (c.elt o) (i + 1) =
      NearCubicGates.Adapters.ACSP.indexedElt c.irrPoly l.length (fun j => GF.toPoly (l.getD j 0))
        (GF.toPoly o) i := by
  have hb : (List.range (l.map c.elt).length).map (fun j => (i + 1 - 1).testBit j) =
      (List.range l.length).map fun j => i.testBit j := by simp
  rw [eltWithIndex, hb, map_elt_eq, getRandElt_range, add_comm]
  simp only [NearCubicGates.Adapters.ACSP.indexedElt, NearCubicGates.Adapters.ACSP.affineElt]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun j => if i.testBit j then c.elt (l.getD j 0) else 0)]
  rfl

theorem affineElt_eq_eltWithIndex (l : List ℕ) (o : ℕ) (coeff : Fin l.length → Bool) :
    NearCubicGates.Adapters.ACSP.affineElt c.irrPoly l.length (fun j => GF.toPoly (l.getD j 0))
        (GF.toPoly o) coeff =
      eltWithIndex (l.map c.elt) (c.elt o) (maskOfBits coeff + 1) := by
  rw [eltWithIndex_map, NearCubicGates.Adapters.ACSP.indexedElt]
  congr 1
  funext j
  simp [testBit_maskOfBits, j.isLt]

theorem mem_span_map (l : List ℕ) (o : ℕ) (α : c.Fld) :
    α ∈ span (l.map c.elt) (c.elt o) ↔ ∃ coeff : Fin l.length → Bool,
      α = NearCubicGates.Adapters.ACSP.affineElt c.irrPoly l.length (fun j => GF.toPoly (l.getD j 0))
        (GF.toPoly o) coeff := by
  simp only [span, List.mem_toFinset, List.mem_map, List.mem_range, List.length_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨bitsOf l.length i, ?_⟩
    rw [affineElt_eq_eltWithIndex, maskOfBits_bitsOf l.length i hi]
  · rintro ⟨coeff, rfl⟩
    exact ⟨maskOfBits coeff, maskOfBits_lt coeff, (affineElt_eq_eltWithIndex c l o coeff).symm⟩

theorem eltWithIndex_map_injOn (l : List ℕ) (o : ℕ)
    (hind : NearCubicGates.Adapters.ACSP.AffineIndependent c.irrPoly l.length
      (fun j => GF.toPoly (l.getD j 0)) (GF.toPoly o)) :
    Set.InjOn (fun i => eltWithIndex (l.map c.elt) (c.elt o) (i + 1)) (Finset.range (2 ^ l.length) : Set ℕ) := by
  intro i hi i' hi' h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
  have e1 := affineElt_eq_eltWithIndex c l o (bitsOf l.length i)
  have e2 := affineElt_eq_eltWithIndex c l o (bitsOf l.length i')
  rw [maskOfBits_bitsOf l.length i hi] at e1
  rw [maskOfBits_bitsOf l.length i' hi'] at e2
  have := hind (e1.trans (h.trans e2.symm))
  rw [← maskOfBits_bitsOf l.length i hi, ← maskOfBits_bitsOf l.length i' hi', this]

theorem isBasis_map (l : List ℕ) (o : ℕ)
    (hind : NearCubicGates.Adapters.ACSP.AffineIndependent c.irrPoly l.length
      (fun j => GF.toPoly (l.getD j 0)) (GF.toPoly o)) :
    IsBasis (l.map c.elt) (c.elt o) := by
  unfold IsBasis span
  rw [List.toFinset_card_of_nodup, List.length_map]
  · simp
  · apply List.Nodup.map_on _ List.nodup_range
    intro i hi i' hi' h
    exact eltWithIndex_map_injOn c l o hind (by simpa using hi) (by simpa using hi') h

end Field

/-! ## The word of a field element (`Request.wordOf` at `φ = id`) -/

section Words

variable (c : Instance) (xs : List Bool) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)] [DecidableEq c.Fld]

theorem wordOf_lt (a : c.Fld) : (request c xs S).wordOf (RingHom.id c.Fld) a < 2 ^ c.f := by
  unfold Request.wordOf
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact Nat.two_pow_pos _

variable (hp : GF.ModulusOk c.irr c.f)
include hp

theorem elt_wordOf (a : c.Fld) : c.elt ((request c xs S).wordOf (RingHom.id c.Fld) a) = a := by
  unfold Request.wordOf
  have hex : ∃ w, w < 2 ^ (request c xs S).code.f ∧ (request c xs S).elt (RingHom.id c.Fld) w = a := by
    obtain ⟨w, hw, rfl⟩ := elt_surj c hp a
    exact ⟨w, hw, rfl⟩
  rw [dif_pos hex]
  exact (Nat.find_spec hex).2

theorem wordOf_elt (w : ℕ) (hw : w < 2 ^ c.f) : (request c xs S).wordOf (RingHom.id c.Fld) (c.elt w) = w :=
  elt_injOn c hp (wordOf_lt c xs S _) hw (elt_wordOf c xs S hp _)

end Words

/-! ## Randomness and length of the transcribed verifiers as numbers -/

section Resources

variable {F : Type} [Field F] [DecidableEq F]

theorem vGt_rand (T : Tuple) (B : List F) (O : F) (d : ℕ) :
    (vGt T B O d).rand = max (max (randEq T B.length)
      (if mKED B.length T.η d * (dKE B.length T.η + 1) < d + 1 then randEq T B.length else 0)) B.length := by
  show max (max _ (if decide _ = true then _ else _)) _ = _
  simp only [decide_eq_true_eq]

theorem vGt_length (T : Tuple) (B : List F) (O : F) (d : ℕ) :
    (vGt T B O d).length = mKED B.length T.η d * (2 ^ B.length + lengthEq T B.length) +
    (if mKED B.length T.η d * (dKE B.length T.η + 1) < d + 1 then 2 ^ B.length + 2 * lengthEq T B.length else 0) := by
  show _ + (if decide _ = true then _ + (vLt T B O _).length else 0) = _
  simp only [decide_eq_true_eq]
  rfl

theorem vRS_rand_eq (T : Tuple) (B : List F) (O : F) (d : ℕ) :
    (vRS T B O d).rand = randRS T B.length d := by
  by_cases h1 : B.length ≤ T.η
  · rw [vRS, if_pos h1, randRS, if_pos h1]
  · by_cases h2 : d < dKE B.length T.η
    · rw [vRS, if_neg h1, if_pos h2, randRS, if_neg h1, if_pos h2]; rfl
    · by_cases h3 : d = dKE B.length T.η
      · rw [vRS, if_neg h1, if_neg h2, if_pos h3, randRS, if_neg h1, if_neg h2, if_pos h3]; rfl
      · rw [vRS, if_neg h1, if_neg h2, if_neg h3, randRS, if_neg h1, if_neg h2, if_neg h3, vGt_rand]

theorem vRS_length_eq (T : Tuple) (B : List F) (O : F) (d : ℕ) :
    (vRS T B O d).length = lenRS T B.length d := by
  by_cases h1 : B.length ≤ T.η
  · rw [vRS, if_pos h1, lenRS, if_pos h1]
  · by_cases h2 : d < dKE B.length T.η
    · rw [vRS, if_neg h1, if_pos h2, lenRS, if_neg h1, if_pos h2]; rfl
    · by_cases h3 : d = dKE B.length T.η
      · rw [vRS, if_neg h1, if_neg h2, if_pos h3, lenRS, if_neg h1, if_neg h2, if_pos h3]; rfl
      · rw [vRS, if_neg h1, if_neg h2, if_neg h3, lenRS, if_neg h1, if_neg h2, if_neg h3, vGt_length]

theorem vVRS_rand_eq (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) :
    (vVRS T B O BH OH d).rand = randVRS T B.length BH.length d := by
  simp [vVRS, randVRS, vRS_rand_eq]

theorem vVRS_length_eq (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) :
    (vVRS T B O BH OH d).length = lenVRS T B.length BH.length d := by
  simp [vVRS, lenVRS, vRS_length_eq]

end Resources

/-- The same verifier, viewed on an equal evaluation set and an equal code. -/
def strongCongr {F : Type} [DecidableEq F] {S S' : Finset F} {code code' : Set (F → F)} {s : ℝ}
    (hS : S = S') (hc : code = code') (V : StrongPCPP F S code s) : StrongPCPP F S' code' s where
  rand := V.rand
  length := V.length
  accepts := V.accepts
  complete := hc ▸ V.complete
  sound := by subst hS; subst hc; exact V.sound

/-! ## The constraint circuit evaluates `P` -/

section Circuit

variable (q : Request) [Fact (Irreducible q.code.irrPoly)] [DecidableEq q.code.Fld]

/-- The gate conversion of `codeCircuit` (constants read by `GF.toPoly`). -/
def convGate : CodeGate → NearCubicGates.Adapters.ACSP.ArithGate (ZMod 2)[X]
  | .input i => .input i
  | .const v => .const (GF.toPoly v)
  | .add a b => .add a b
  | .mul a b => .mul a b

private theorem getD_map_zero {α β : Type} [Zero α] [Zero β] (g : α → β) (hg : g 0 = 0) (l : List α) (i : ℕ) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hg]

omit [DecidableEq q.code.Fld] in
theorem foldl_gates (m : ℕ) (envN : ℕ → q.code.Fld) (env : Fin m → q.code.Fld)
    (henv : ∀ i (h : i < m), envN i = env ⟨i, h⟩) (gates : List CodeGate)
    (Pp : List (MvPolynomial (Fin m) (ZMod 2)[X])) :
    gates.foldl (fun prior g => prior ++ [q.gateVal (RingHom.id q.code.Fld) m envN prior g])
      (Pp.map (MvPolynomial.eval₂Hom (AdjoinRoot.mk q.code.irrPoly) env)) =
    ((gates.map convGate).foldl (fun prior g => prior ++ [g.poly m prior]) Pp).map
      (MvPolynomial.eval₂Hom (AdjoinRoot.mk q.code.irrPoly) env) := by
  induction gates generalizing Pp with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [← ih]
    congr 1
    rw [List.map_append, List.map_singleton]
    congr 2
    cases g with
    | input i =>
      simp only [Request.gateVal, convGate, NearCubicGates.Adapters.ACSP.ArithGate.poly]
      split_ifs with h
      · simp [henv i h]
      · simp
    | const v =>
      simp only [Request.gateVal, convGate, NearCubicGates.Adapters.ACSP.ArithGate.poly,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rfl
    | add a b =>
      simp only [Request.gateVal, convGate, NearCubicGates.Adapters.ACSP.ArithGate.poly, map_add]
      rw [getD_map_zero _ (map_zero _), getD_map_zero _ (map_zero _)]
    | mul a b =>
      simp only [Request.gateVal, convGate, NearCubicGates.Adapters.ACSP.ArithGate.poly, map_mul]
      rw [getD_map_zero _ (map_zero _), getD_map_zero _ (map_zero _)]

theorem codeCircuit_gates (gates : List CodeGate) : (codeCircuit gates).gates = gates.map convGate := by
  unfold codeCircuit
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

omit [DecidableEq q.code.Fld] in
theorem circuitVal_eq (m : ℕ) (envN : ℕ → q.code.Fld) (env : Fin m → q.code.Fld)
    (henv : ∀ i (h : i < m), envN i = env ⟨i, h⟩) (gates : List CodeGate) :
    q.circuitVal (RingHom.id q.code.Fld) m envN gates =
      MvPolynomial.eval env (NearCubicGates.Adapters.ACSP.fieldPoly q.code.irrPoly (codeCircuit gates) m) := by
  have h := foldl_gates q m envN env henv gates []
  simp only [List.map_nil] at h
  simp only [Request.circuitVal, NearCubicGates.Adapters.ACSP.fieldPoly,
    NearCubicGates.Adapters.ACSP.ArithCircuit.poly, MvPolynomial.eval_map, codeCircuit_gates]
  rw [h, ← map_zero (MvPolynomial.eval₂Hom (AdjoinRoot.mk q.code.irrPoly) env), List.getLastD_map]
  rfl

/-- The constraint of the request is `P` (`def:acsp`). -/
theorem acsp_P (α : q.code.Fld) (ys : Fin q.code.cN → q.code.Fld) :
    (q.acsp (RingHom.id q.code.Fld)).P α ys = MvPolynomial.eval (Fin.cons α ys) q.code.consPoly := by
  simp only [Request.acsp]
  rw [circuitVal_eq q (q.code.cN + 1) _ (Fin.cons α ys) (fun i h => by simp [h])]
  rfl

/-- The neighbors of the request are `N_ν(X) = a_ν X + b_ν` (`def:acsp`). -/
theorem acsp_nbr (ν : Fin q.code.cN) (α : q.code.Fld) :
    (q.acsp (RingHom.id q.code.Fld)).nbr ν α = q.code.nbrFn ν α := rfl

end Circuit

/-! ## `B_A` evaluates pointwise -/

theorem eval_aeval_poly {F : Type} [CommRing F] {σ : Type} (g : σ → F[X]) (p : MvPolynomial σ F) (x : F) :
    (MvPolynomial.aeval g p).eval x = MvPolynomial.eval (fun s => (g s).eval x) p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
  congr 1
  ext a
  simp

/-- "`B_A(X) = P(X, A(N_1(X)), …)`" evaluated at `α` (the paragraph after `def:acsp`). -/
theorem composed_eval (c : Instance) (A : c.Fld[X]) (α : c.Fld) :
    (c.composed A).eval α =
      MvPolynomial.eval (Fin.cons α fun ν : Fin c.cN => A.eval (c.nbrFn ν α)) c.consPoly := by
  rw [Instance.composed, eval_aeval_poly]
  refine congrArg (fun v => MvPolynomial.eval v c.consPoly) ?_
  funext j
  refine Fin.cases ?_ (fun ν => ?_) j
  · simp
  · simp only [Fin.cons_succ]
    rw [eval_comp]
    simp [Instance.nbrFn]

/-! ## Membership is `Instance.Accepts` -/

section Request

variable (c : Instance) (xs : List Bool) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)]

theorem domBasis_eq : (request c xs S).domBasis (RingHom.id c.Fld) = monoBasis c := rfl
theorem hB_eq : (request c xs S).hB (RingHom.id c.Fld) = c.hBasis.map c.elt := rfl
theorem hO_eq : (request c xs S).hO (RingHom.id c.Fld) = c.elt c.hOffset := rfl
theorem iB_eq : (request c xs S).iB (RingHom.id c.Fld) = c.iBasis.map c.elt := rfl
theorem iO_eq : (request c xs S).iO (RingHom.id c.Fld) = c.elt c.iOffset := rfl

variable [DecidableEq c.Fld]

theorem acsp_P' (α : c.Fld) (ys : Fin c.cN → c.Fld) :
    ((request c xs S).acsp (RingHom.id c.Fld)).P α ys = MvPolynomial.eval (Fin.cons α ys) c.consPoly := by
  letI : Fact (Irreducible (request c xs S).code.irrPoly) := ‹Fact (Irreducible c.irrPoly)›
  letI : DecidableEq (request c xs S).code.Fld := ‹DecidableEq c.Fld›
  exact acsp_P (request c xs S) α ys

theorem acsp_H : ((request c xs S).acsp (RingHom.id c.Fld)).H = span (c.hBasis.map c.elt) (c.elt c.hOffset) := rfl
theorem acsp_I : ((request c xs S).acsp (RingHom.id c.Fld)).I = span (c.iBasis.map c.elt) (c.elt c.iOffset) := rfl
theorem acsp_px (α : c.Fld) : ((request c xs S).acsp (RingHom.id c.Fld)).px α =
    (Lagrange.interpolate (Finset.range xs.length) (fun i => eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1))
      (fun i => if xs.getD i false then 1 else 0)).eval α := rfl

end Request

section Mem

theorem natDegree_le_pred_iff {F : Type} [Semiring F] (A : F[X]) (N : ℕ) (hN : 1 ≤ N) :
    A.natDegree ≤ N - 1 ↔ A.degree < (N : WithBot ℕ) := by
  by_cases hA : A = 0
  · subst hA; simp
  · rw [Polynomial.degree_eq_natDegree hA, Nat.cast_lt]; omega

variable {Kc : ℕ} {c : Instance} {xs : List Bool}

theorem indep_I (hG : SingleRun.Good Kc c xs) :
    NearCubicGates.Adapters.ACSP.AffineIndependent c.irrPoly c.iBasis.length
      (fun j => GF.toPoly (c.iBasis.getD j 0)) (GF.toPoly c.iOffset) := hG.valid.2.2.2.1.1

theorem indep_H (hG : SingleRun.Good Kc c xs) :
    NearCubicGates.Adapters.ACSP.AffineIndependent c.irrPoly c.hBasis.length
      (fun j => GF.toPoly (c.hBasis.getD j 0)) (GF.toPoly c.hOffset) := hG.valid.2.1

variable (hG : SingleRun.Good Kc c xs) (S : List (List Bool)) [Fact (Irreducible c.irrPoly)]
  [DecidableEq c.Fld]
include hG

theorem lagrange_injOn :
    Set.InjOn (fun i => eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1))
      (Finset.range xs.length : Set ℕ) := by
  rw [hG.xbar_len]; exact eltWithIndex_map_injOn c c.iBasis c.iOffset (indep_I hG)

/-- The node values of the low-degree extension `A_x` (Step 2, "Completeness": "the polynomial … that interpolates
`x̄` on `I`"). -/
theorem px_node (i : ℕ) (hi : i < 2 ^ c.m) :
    ((request c xs S).acsp (RingHom.id c.Fld)).px (eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1)) =
      if xs.getD i false then 1 else 0 := by
  rw [acsp_px]
  have := Lagrange.eval_interpolate_at_node (s := Finset.range xs.length)
    (v := fun i => eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1))
    (fun i => if xs.getD i false then (1 : c.Fld) else 0) (lagrange_injOn hG)
    (Finset.mem_range.mpr (hG.xbar_len ▸ hi))
  exact this

theorem px_low : ∃ Px : c.Fld[X], Px.natDegree ≤ 2 ^ c.mH - 1 ∧
    ∀ α, ((request c xs S).acsp (RingHom.id c.Fld)).px α = Px.eval α := by
  refine ⟨Lagrange.interpolate (Finset.range xs.length)
    (fun i => eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1))
    (fun i => if xs.getD i false then 1 else 0), ?_, fun α => rfl⟩
  have hd := Lagrange.degree_interpolate_lt (s := Finset.range xs.length)
    (v := fun i => eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1))
    (r := fun i => if xs.getD i false then 1 else 0) (lagrange_injOn hG)
  rw [Finset.card_range] at hd
  have h1 := (natDegree_le_pred_iff _ _ (by rw [hG.xbar_len]; exact Nat.one_le_two_pow)).mpr hd
  have h2 : 2 ^ c.m ≤ 2 ^ c.mH := Nat.pow_le_pow_right (by norm_num) hG.m_lt.le
  have h3 := hG.xbar_len
  omega

/-- **Membership is acceptance** (`def:acsp`): `ACSPInstance.Mem` of the request is `Instance.Accepts`. -/
theorem mem_iff_accepts : ((request c xs S).acsp (RingHom.id c.Fld)).Mem ↔ c.Accepts xs := by
  have hlen := hG.xbar_len
  constructor
  · rintro ⟨A, hdeg, hH, hI⟩
    refine ⟨hlen, A, (natDegree_le_pred_iff A _ Nat.one_le_two_pow).mp hdeg, ?_, ?_⟩
    · intro coeff
      have hmem : c.hElt coeff ∈ ((request c xs S).acsp (RingHom.id c.Fld)).H := by
        rw [acsp_H]; exact (mem_span_map c c.hBasis c.hOffset _).mpr ⟨coeff, rfl⟩
      have := hH _ hmem
      rwa [acsp_P'] at this
    · intro i hi
      have hi' : i < 2 ^ c.m := hlen ▸ hi
      have hmem : eltWithIndex (c.iBasis.map c.elt) (c.elt c.iOffset) (i + 1) ∈
          ((request c xs S).acsp (RingHom.id c.Fld)).I := by
        rw [acsp_I]
        simp only [span, List.mem_toFinset, List.mem_map, List.mem_range, List.length_map]
        exact ⟨i, hi', rfl⟩
      have := hI _ hmem
      rw [px_node hG S i hi', eltWithIndex_map, List.getD_eq_getElem _ _ hi] at this
      exact this
  · rintro ⟨-, A, hdeg, hH, hI⟩
    refine ⟨A, (natDegree_le_pred_iff A _ Nat.one_le_two_pow).mpr hdeg, ?_, ?_⟩
    · intro α hα
      rw [acsp_H] at hα
      obtain ⟨coeff, rfl⟩ := (mem_span_map c c.hBasis c.hOffset α).mp hα
      rw [acsp_P']
      exact hH coeff
    · intro α hα
      rw [acsp_I] at hα
      simp only [span, List.mem_toFinset, List.mem_map, List.mem_range, List.length_map] at hα
      obtain ⟨i, hi, rfl⟩ := hα
      have hA := hI i (hlen ▸ hi)
      rw [px_node hG S i hi, eltWithIndex_map, List.getD_eq_getElem _ _ (hlen ▸ hi)]
      exact hA

end Mem

end NearCubicGates.Adapters.ShortPCP.Verifier
