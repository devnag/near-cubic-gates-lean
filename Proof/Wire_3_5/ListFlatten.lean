import Proof.Wire_3_5.ListBase
import Proof.Wire_3_5.FilterGap
import Proof.Supplier.SupplierWalkBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open Finset

/-! ## Majority as an exact integer sum of indicator products -/

/-- A bit as an integer. -/
def bitInt (b : Bool) : ℤ := if b then 1 else 0

/-- The majority sets `T ⊆ [t]` with `|T| ≥ θ`. -/
def majoritySets (t θ : ℕ) : Finset (Finset (Fin t)) := (Finset.univ : Finset (Finset (Fin t))).filter fun T => θ ≤ T.card

/-- The indicator product of `T`: `Π_{k∈T} y_k Π_{k∉T}(1 − y_k)` (exactly `t` Boolean factors). -/
def indicatorProduct {t : ℕ} (y : Fin t → Bool) (T : Finset (Fin t)) : ℤ :=
  ∏ k : Fin t, if k ∈ T then bitInt (y k) else 1 - bitInt (y k)

theorem indicatorProduct_eq {t : ℕ} (y : Fin t → Bool) (T : Finset (Fin t)) :
    indicatorProduct y T = if T = Finset.univ.filter (fun k => y k = true) then 1 else 0 := by
  unfold indicatorProduct
  split_ifs with hT
  · apply Finset.prod_eq_one; intro k _
    by_cases hk : k ∈ T
    · have : y k = true := by rw [hT] at hk; simpa using hk
      simp [hk, this, bitInt]
    · have : y k = false := by rw [hT] at hk; simpa using hk
      simp [hk, this, bitInt]
  · obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ T ↔ y k = true) := by
      by_contra hall; push Not at hall
      exact hT (by ext k; simp [hall k])
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hkT : k ∈ T
    · have : y k = false := by simpa [hkT] using hk
      simp [hkT, this, bitInt]
    · have : y k = true := by simpa [hkT] using hk
      simp [hkT, this, bitInt]

/-- **The majority as an integer polynomial**: `1[θ ≤ #{k : y_k}] = Σ_{|T| ≥ θ} Π_{k∈T} y_k Π_{k∉T}(1 − y_k)`. -/
theorem majority_expansion {t : ℕ} (θ : ℕ) (y : Fin t → Bool) :
    bitInt (decide (θ ≤ (Finset.univ.filter fun k => y k = true).card)) =
      ∑ T ∈ majoritySets t θ, indicatorProduct y T := by
  simp only [indicatorProduct_eq, majoritySets]
  rw [Finset.sum_ite_eq']
  simp [bitInt]

theorem card_majoritySets_le (t θ : ℕ) : (majoritySets t θ).card ≤ 2 ^ t := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-! ## The amplified list -/

/-- The parameters of `list:flatten`: the range `M`, the cap `B`, and the error exponent (`failure ≤ 2^{−errExp}`). -/
structure FlatListParams where
  M : ℕ
  B : ℕ
  errExp : ℕ

namespace FlatListParams
variable (P : FlatListParams)

/-- The base list of `list:base`. -/
def base : BaseListParams := ⟨P.M, P.B⟩

def walkLen : ℕ := 2 * (P.errExp / 4) + 1

theorem walkLen_odd : Odd P.walkLen := ⟨P.errExp / 4, rfl⟩

/-- The walk's vertex side: Theorem 2.5's smallest square binary vertex set containing the Toeplitz seeds. -/
def side : ℕ := 2 ^ SupplierWalkBridge.toeplitzWalkSideBits P.base.rank

instance instNeZeroSide : NeZero P.side := ⟨by unfold side; positivity⟩

/-- The base seed at a walk vertex: Theorem 2.5's computable `toeplitzWalkEncoding` (the padding bit is dropped). -/
def decode (v : MargulisVertex P.side) : P.base.Seed := (SupplierWalkBridge.toeplitzWalkEncoding P.base.rank v).1

/-- **The seed space** of the amplified list: a powered Margulis walk sample of `t` steps over the base seeds. -/
abbrev FlatSeed : Type := MargulisWalkSample P.side P.walkLen

def visitReport (e : P.FlatSeed) (k : Fin P.walkLen) (Z : List Bool) : ℕ := P.base.report (P.decode (e.vertex k)) Z

/-- The majority state `Maj_t(P^{(1)}_s, …, P^{(t)}_s)`: at least `(t+1)/2` visits report `s`. -/
def majState (e : P.FlatSeed) (Z : List Bool) (s : ℕ) : Bool :=
  concreteMajorityFailure (fun v => decide (P.base.report (P.decode v) Z = s)) e

theorem majState_eq (e : P.FlatSeed) (Z : List Bool) (s : ℕ) :
    P.majState e Z s = decide (majorityThreshold P.walkLen ≤
      (Finset.univ.filter fun k => decide (P.visitReport e k Z = s) = true).card) := rfl

def flatReport (e : P.FlatSeed) (Z : List Bool) : ℕ :=
  (((List.range P.M).map (· + 1)).find? fun s => P.majState e Z s).getD 0

theorem majState_unique (e : P.FlatSeed) (Z : List Bool) {s s' : ℕ} (hs : P.majState e Z s = true)
    (hs' : P.majState e Z s' = true) : s = s' := by
  by_contra hne
  rw [majState_eq, decide_eq_true_eq] at hs hs'
  have hdisj : Disjoint (Finset.univ.filter fun k => decide (P.visitReport e k Z = s) = true)
      (Finset.univ.filter fun k => decide (P.visitReport e k Z = s') = true) := by
    rw [Finset.disjoint_filter]; intro k _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2; exact hne (h1.symm.trans h2)
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle : ((Finset.univ.filter fun k => decide (P.visitReport e k Z = s) = true) ∪
      (Finset.univ.filter fun k => decide (P.visitReport e k Z = s') = true)).card ≤ P.walkLen := by
    refine (Finset.card_le_univ _).trans ?_; simp
  obtain ⟨m, hm⟩ := P.walkLen_odd
  unfold majorityThreshold at hs hs'
  omega

theorem flatReport_eq_of_majState (e : P.FlatSeed) (Z : List Bool) (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ P.M)
    (hs : P.majState e Z s = true) : P.flatReport e Z = s := by
  unfold flatReport
  cases hf : ((List.range P.M).map (· + 1)).find? (fun s => P.majState e Z s) with
  | none =>
    have := List.find?_eq_none.mp hf s (List.mem_map.mpr ⟨s - 1, List.mem_range.mpr (by omega), by omega⟩)
    simp [hs] at this
  | some r =>
    have hr := List.find?_some hf
    simp only [Option.getD_some]
    exact P.majState_unique e Z hr hs

theorem flatReport_zero_of_none (e : P.FlatSeed) (Z : List Bool)
    (hnone : ∀ s, 1 ≤ s → s ≤ P.M → P.majState e Z s = false) : P.flatReport e Z = 0 := by
  unfold flatReport
  cases hf : ((List.range P.M).map (· + 1)).find? (fun s => P.majState e Z s) with
  | none => rfl
  | some r =>
    have hr := List.find?_some hf
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    have := hnone (a + 1) (by omega) (by have := List.mem_range.mp ha; omega)
    rw [this] at hr; exact absurd hr (by simp)

theorem flatReport_spec (e : P.FlatSeed) (Z : List Bool) :
    (P.flatReport e Z = 0 ∧ ∀ s, 1 ≤ s → s ≤ P.M → P.majState e Z s = false) ∨
      (1 ≤ P.flatReport e Z ∧ P.flatReport e Z ≤ P.M ∧ P.majState e Z (P.flatReport e Z) = true) := by
  by_cases h : ∃ s, 1 ≤ s ∧ s ≤ P.M ∧ P.majState e Z s = true
  · obtain ⟨s, h1, h2, h3⟩ := h
    right; rw [P.flatReport_eq_of_majState e Z s h1 h2 h3]; exact ⟨h1, h2, h3⟩
  · push Not at h
    left
    have hn : ∀ s, 1 ≤ s → s ≤ P.M → P.majState e Z s = false := fun s h1 h2 => by simpa using h s h1 h2
    exact ⟨P.flatReport_zero_of_none e Z hn, hn⟩

theorem flatReport_eq_of_majority (e : P.FlatSeed) (Z : List Bool) (w : ℕ) (hwM : w ≤ P.M)
    (hmaj : P.majState e Z w = true) : P.flatReport e Z = w := by
  rcases Nat.eq_zero_or_pos w with h0 | hpos
  · subst h0
    apply P.flatReport_zero_of_none
    intro s hs1 _
    by_contra hs; simp only [Bool.not_eq_false] at hs
    have := P.majState_unique e Z hmaj hs; omega
  · exact P.flatReport_eq_of_majState e Z w hpos hwM hmaj

theorem flatReport_le (e : P.FlatSeed) (Z : List Bool) : P.flatReport e Z ≤ P.M := by
  rcases P.flatReport_spec e Z with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega

theorem booleanMean_decode (f : P.base.Seed → Bool) :
    booleanMean (fun v : MargulisVertex P.side => f (P.decode v)) = booleanMean f :=
  SupplierWalkBridge.booleanMean_toeplitzWalkEncoding P.base.rank f

theorem flatReport_fail_le (spectrum : ExpanderSpectrumContract) (Z : List Bool) (hZ : Z.length ≤ P.M)
    (hw : Z.count true ≤ P.B) :
    booleanMean (fun e : P.FlatSeed => decide (P.flatReport e Z ≠ Z.count true)) ≤ 1 / 2 ^ P.errExp := by
  set good : MargulisVertex P.side → Bool := fun v => decide (P.base.report (P.decode v) Z = Z.count true)
  have hrho : booleanMean (fun v => !good v) ≤ 1 / 128 := by
    have := P.booleanMean_decode (fun s => !decide (P.base.report s Z = Z.count true))
    simp only [good]
    rw [this]
    have hb := P.base.report_fail_le Z hZ hw
    refine le_of_eq_of_le ?_ hb
    congr 1; funext s; simp
  have hmaj := concreteMajorityFailure_le spectrum P.walkLen_odd (fun v => !good v) hrho
  have hwM : Z.count true ≤ P.M := (List.count_le_length ..).trans hZ
  refine le_trans (booleanMean_mono _ _ fun e he => ?_) (hmaj.trans ?_)
  · apply majority_complement P.walkLen_odd good e
    by_contra hg
    simp only [Bool.not_eq_false] at hg
    have := P.flatReport_eq_of_majority e Z _ hwM hg
    simp only [decide_eq_true_eq] at he
    exact he this
  · apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    unfold walkLen; omega

/-- The majority indicator of state `s` as the integer sum of indicator products of the visited base states. -/
theorem majState_expansion (e : P.FlatSeed) (Z : List Bool) (s : ℕ) :
    bitInt (P.majState e Z s) =
      ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
        indicatorProduct (fun k => decide (P.visitReport e k Z = s)) T := by
  rw [majState_eq]; exact majority_expansion _ _

theorem flatState_expansion (e : P.FlatSeed) (Z : List Bool) (s : ℕ) (hsM : s ≤ P.M) :
    bitInt (decide (P.flatReport e Z = s)) =
      if s = 0 then
        1 - ∑ s' ∈ Finset.Icc 1 P.M, ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
          indicatorProduct (fun k => decide (P.visitReport e k Z = s')) T
      else ∑ T ∈ majoritySets P.walkLen (majorityThreshold P.walkLen),
          indicatorProduct (fun k => decide (P.visitReport e k Z = s)) T := by
  simp only [← P.majState_expansion]
  split_ifs with h0
  · subst h0
    rcases P.flatReport_spec e Z with ⟨hr, hn⟩ | ⟨h1, h2, h3⟩
    · rw [hr, Finset.sum_eq_zero fun s' hs' => by
        rw [Finset.mem_Icc] at hs'; rw [hn s' hs'.1 hs'.2]; rfl]
      simp [bitInt]
    · rw [Finset.sum_eq_single (P.flatReport e Z)]
      · rw [h3]; simp [bitInt]; omega
      · intro s' hs' hne
        rw [Finset.mem_Icc] at hs'
        by_contra hb
        have : P.majState e Z s' = true := by
          cases hm : P.majState e Z s' <;> simp_all [bitInt]
        exact hne (P.majState_unique e Z this h3)
      · intro hnot; exact absurd (Finset.mem_Icc.mpr ⟨h1, h2⟩) hnot
  · rcases P.flatReport_spec e Z with ⟨hr, hn⟩ | ⟨h1, h2, h3⟩
    · rw [hr, hn s (by omega) hsM]; simp [bitInt, Ne.symm h0]
    · by_cases hrs : P.flatReport e Z = s
      · rw [← hrs, h3]; simp [bitInt]
      · have : P.majState e Z s = false := by
          by_contra hm; simp only [Bool.not_eq_false] at hm
          exact hrs (P.majState_unique e Z h3 hm)
        rw [this]; simp [bitInt, hrs]

theorem visit_state_poly (e : P.FlatSeed) (k : Fin P.walkLen) (L s : ℕ) (hs : s ≤ P.M) :
    ∃ p : MvPolynomial (Fin L) (ZMod 2),
      p.totalDegree ≤ 1536 * (Nat.sqrt P.B + 1) + 260 * P.base.J ∧
        ∀ z : Fin L → Bool, MvPolynomial.eval (fun i => bitF2 (z i)) p =
          bitF2 (decide (P.visitReport e k (List.ofFn z) = s)) := by
  obtain ⟨hdeg, heval⟩ := P.base.report_poly (P.decode (e.vertex k)) L s hs
  exact ⟨_, hdeg.trans (P.base.degree_le _), heval⟩

theorem card_flatSeed : Fintype.card P.FlatSeed = P.side * P.side * (16 ^ 40) ^ (P.walkLen - 1) := by
  have he : P.FlatSeed ≃ MargulisVertex P.side × (Fin (P.walkLen - 1) → PoweredMargulisLabel) :=
    { toFun := fun s => (s.start, s.transitions)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr he]
  simp [Fintype.card_prod, MargulisVertex, ZMod.card, PoweredMargulisLabel]

end FlatListParams

end NearCubicWires.WireExponent3_5.Lists
