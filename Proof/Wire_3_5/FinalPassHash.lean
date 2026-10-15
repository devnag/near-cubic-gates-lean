import Proof.Wire_3_5.FinalPassSym

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.Shared

/-! ## Horner's rule in the machine field -/

/-- `Σ_{r<n} f_r·x^r` by Horner's rule with the shift-and-xor product. -/
def hornerBits (p ℓ x : ℕ) : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 ^^^ fmulShift p ℓ x (hornerBits p ℓ x n fun r => f r.succ)

theorem hornerBits_spec (p ℓ : ℕ) (hp : ModulusOk p ℓ) (x : ℕ) (hx : x < 2 ^ ℓ) :
    ∀ (n : ℕ) (f : Fin n → ℕ), (∀ r, f r < 2 ^ ℓ) →
      hornerBits p ℓ x n f < 2 ^ ℓ ∧ rep p (hornerBits p ℓ x n f) = ∑ r : Fin n, rep p (f r) * rep p x ^ (r : ℕ)
  | 0, f, _ => ⟨by simp [hornerBits], by simp [hornerBits]⟩
  | n + 1, f, hf => by
    obtain ⟨h1, h2⟩ := hornerBits_spec p ℓ hp x hx n (fun r => f r.succ) (fun r => hf r.succ)
    obtain ⟨h3, h4⟩ := fmulShift_spec p ℓ x _ hp hx h1
    refine ⟨Nat.xor_lt_two_pow (hf 0) h3, ?_⟩
    simp only [hornerBits]
    rw [rep_xor, h4, h2, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by ring

/-! ## The majorant's hash at a seed code -/

namespace MajorantBits
variable (MP : MajorantParams)

/-- The `r`-th coefficient of a seed code, as a bit vector. -/
def coefVal (s : Fin (2 * MP.t * MP.ell0) → Bool) (r : Fin (2 * MP.t)) : ℕ :=
  decodeVal MP.ell0 fun b => (finTwoEquiv.symm (s (finProdFinEquiv (r, b))) : ZMod 2)

/-- **The hash value of coordinate `i`** at a seed code: Horner's rule at the point `i`. -/
def valueBits (s : Fin (2 * MP.t * MP.ell0) → Bool) (i : ℕ) : ℕ :=
  hornerBits MP.refMod MP.ell0 i (2 * MP.t) (coefVal MP s)

/-- **The level sets** at a seed code: coordinate `i < M` is in `𝓛_j` iff the first `j` bits of its value vanish. -/
def inLevelBits (s : Fin (2 * MP.t * MP.ell0) → Bool) (j i : ℕ) : Bool :=
  if i < MP.M then decide (∀ b < MP.ell0, b < j → (valueBits MP s i).testBit b = false) else true

/-- **The count lists** of the hash at a seed code. -/
def dataBits (s : Fin (2 * MP.t * MP.ell0) → Bool) : ListData := ⟨MP.M, MP.J, MP.W, inLevelBits MP s⟩

theorem coefVal_lt (s : Fin (2 * MP.t * MP.ell0) → Bool) (r : Fin (2 * MP.t)) : coefVal MP s r < 2 ^ MP.ell0 :=
  decodeVal_lt _ _

theorem bitF_testBit_decodeVal {ℓ : ℕ} (G : Fin ℓ → ZMod 2) (b : Fin ℓ) :
    GF.bitF ((decodeVal ℓ G).testBit b) = G b := by
  rw [testBit_decodeVal]
  rcases zmod2_eq_zero_or_one (G b) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem coord_symm_bits (a : ℕ) (ha : a < 2 ^ MP.ell0) :
    letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
    MP.coord.symm (fun b => GF.bitF (a.testBit b)) =
      GF.refAlgEquivGalois MP.refMod MP.ell0 MP.refCert (GF.rep MP.refMod a) := by
  letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
  rw [LinearEquiv.symm_apply_eq]
  funext b
  exact (MP.coord_rep a ha b).symm

theorem seedCode_apply_eq (s : Fin (2 * MP.t * MP.ell0) → Bool) (r : Fin (2 * MP.t)) :
    letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
    MP.seedCode s r = GF.refAlgEquivGalois MP.refMod MP.ell0 MP.refCert (GF.rep MP.refMod (coefVal MP s r)) := by
  letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
  rw [← coord_symm_bits MP _ (coefVal_lt MP s r)]
  show MP.coord.symm (fun b => (finTwoEquiv.symm (s (finProdFinEquiv (r, b))) : ZMod 2)) = _
  congr 1
  funext b
  exact (bitF_testBit_decodeVal (fun b => (finTwoEquiv.symm (s (finProdFinEquiv (r, b))) : ZMod 2)) b).symm

theorem point_eq (i : Fin MP.M) :
    letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
    MP.point i = GF.refAlgEquivGalois MP.refMod MP.ell0 MP.refCert (GF.rep MP.refMod i) := by
  letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
  have hi : (i : ℕ) < 2 ^ MP.ell0 := lt_of_lt_of_le i.isLt MP.M_le_two_pow
  rw [← coord_symm_bits MP _ hi]
  rfl

/-- **The hash value at a seed code** is the field element of `valueBits`. -/
theorem value_seedCode (s : Fin (2 * MP.t * MP.ell0) → Bool) (i : Fin MP.M) :
    letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
    MP.value (MP.seedCode s) i =
      GF.refAlgEquivGalois MP.refMod MP.ell0 MP.refCert (GF.rep MP.refMod (valueBits MP s i)) := by
  letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
  have hi : (i : ℕ) < 2 ^ MP.ell0 := lt_of_lt_of_le i.isLt MP.M_le_two_pow
  obtain ⟨_, hrep⟩ := hornerBits_spec MP.refMod MP.ell0 MP.refCert.2.1 i hi (2 * MP.t) (coefVal MP s)
    (coefVal_lt MP s)
  unfold MajorantParams.value valueBits
  rw [hrep, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [seedCode_apply_eq, point_eq, map_mul, map_pow]

theorem prefixZero_seedCode (s : Fin (2 * MP.t * MP.ell0) → Bool) (j : ℕ) (i : Fin MP.M) :
    MP.PrefixZero j (MP.value (MP.seedCode s) i) ↔
      ∀ b < MP.ell0, b < j → (valueBits MP s i).testBit b = false := by
  letI := GF.fact_irreducible MP.refMod MP.ell0 MP.refCert
  have hv : valueBits MP s i < 2 ^ MP.ell0 := by
    have hi : (i : ℕ) < 2 ^ MP.ell0 := lt_of_lt_of_le i.isLt MP.M_le_two_pow
    exact (hornerBits_spec MP.refMod MP.ell0 MP.refCert.2.1 i hi (2 * MP.t) (coefVal MP s) (coefVal_lt MP s)).1
  unfold MajorantParams.PrefixZero
  rw [value_seedCode]
  constructor
  · intro h b hb hbj
    have := h ⟨b, hb⟩ hbj
    rw [MP.coord_rep _ hv] at this
    cases ht : (valueBits MP s i).testBit b
    · rfl
    · rw [ht] at this; exact absurd this (by decide)
  · intro h b hbj
    rw [MP.coord_rep _ hv, h b b.isLt hbj]
    rfl

/-- **The level sets at a seed code are the bit-level level sets.** -/
theorem inLevel_seedCode (s : Fin (2 * MP.t * MP.ell0) → Bool) (j i : ℕ) :
    MP.inLevel (MP.seedCode s) j i = inLevelBits MP s j i := by
  unfold MajorantParams.inLevel inLevelBits
  by_cases hi : i < MP.M
  · rw [dif_pos hi, if_pos hi]
    exact decide_eq_decide.mpr (prefixZero_seedCode MP s j ⟨i, hi⟩)
  · rw [dif_neg hi, if_neg hi]

/-- **The hash's lists at a seed code are the bit-level lists.** -/
theorem data_seedCode (s : Fin (2 * MP.t * MP.ell0) → Bool) : MP.data (MP.seedCode s) = dataBits MP s := by
  unfold MajorantParams.data dataBits
  congr 1
  funext j i
  exact inLevel_seedCode MP s j i

end MajorantBits

end NearCubicWires.WireExponent3_5.FinalPass
