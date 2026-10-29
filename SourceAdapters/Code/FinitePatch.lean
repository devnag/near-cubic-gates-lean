import SourceAdapters.Code.Distance

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": identity patches at short lengths and common strict constants. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

/-- A finite support code used to select the actual construction at each size. -/
structure CoordinateCode (n : ℕ) where
  size : ℕ
  support : Fin size → Finset (Fin n)
  decoder : BitInput size → BitInput n

noncomputable def CoordinateCode.encode {n : ℕ} (C : CoordinateCode n) (x : BitInput n) : BitInput C.size :=
  fun j => parityOn (C.support j) x

def familyFromAt (C : (n : ℕ) → CoordinateCode n) : LinearCodeFamily where
  length n := (C n).size
  support n := (C n).support
  decoder n := (C n).decoder

def identityAt (n : ℕ) : CoordinateCode n where
  size := n
  support i := {i}
  decoder y := y

noncomputable def threeBlockAt (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) : CoordinateCode n where
  size := (threeBlock F).length n
  support := sourceSupport (threeBlock F) n
  decoder := threeDecoder F D n

def cutoff (onset : ℕ) : ℕ := 6 * (onset + 1)

noncomputable def patchedAt (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ) : CoordinateCode n :=
  if cutoff onset ≤ n then threeBlockAt F D n else identityAt n

noncomputable def patchedFamily (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) : LinearCodeFamily := familyFromAt (patchedAt F D)

theorem patched_length (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (rate : ℕ)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k) (n : ℕ) :
    (patchedFamily F D).length n ≤ (rate + 1) * (n + 1) := by
  by_cases hn : cutoff onset ≤ n
  · change (patchedAt F D n).size ≤ _
    rw [patchedAt, if_pos hn]
    have h := threeBlock_length_upper F onset rate n hrate hn
    change (threeBlock F).length n ≤ _
    nlinarith
  · change (patchedAt F D n).size ≤ _
    rw [patchedAt, if_neg hn]
    change n ≤ _
    nlinarith

theorem patched_support (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (n : ℕ) (hn : 2 ≤ n) : ∀ j, ((patchedFamily F D).support n j).card ≤ n / 2 := by
  change ∀ j, ((patchedAt F D n).support j).card ≤ n / 2
  by_cases hlarge : cutoff onset ≤ n
  · rw [patchedAt, if_pos hlarge]
    exact threeBlock_support_bound F hlinear n hn
  · rw [patchedAt, if_neg hlarge]
    change ∀ j : Fin n, ({j} : Finset (Fin n)).card ≤ n / 2
    intro j
    rw [Finset.card_singleton]
    omega

theorem patched_distance (F : BinaryFamily) (onset rate : ℕ) (distance radius d : ℝ)
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (hdlarge : d ≤ distance / lossFactor rate) (hdsmall : d ≤ 1 / (cutoff onset + 1 : ℕ))
    (n : ℕ) (hn : 2 ≤ n) (x y : BitInput n) (hxy : x ≠ y) :
    d ≤ relativeHamming ((patchedFamily F D).enc n x) ((patchedFamily F D).enc n y) := by
  change d ≤ relativeHamming ((patchedAt F D n).encode x) ((patchedAt F D n).encode y)
  by_cases hlarge : cutoff onset ≤ n
  · rw [patchedAt, if_pos hlarge]
    change d ≤ relativeHamming
      (fun i => parityOn (sourceSupport (threeBlock F) n i) x)
      (fun i => parityOn (sourceSupport (threeBlock F) n i) y)
    simp only [← sourceSupport_enc (threeBlock F) (threeBlock_linear F hlinear)]
    exact hdlarge.trans (threeBlock_distance F onset rate distance hd hmin hrate n hlarge x y hxy)
  · rw [patchedAt, if_neg hlarge]
    change d ≤ relativeHamming (fun i => parityOn {i} x) (fun i => parityOn {i} y)
    simp only [parityOn, Finset.toList_singleton, List.foldl_cons, List.foldl_nil, Bool.false_xor]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsmall : (n : ℝ) ≤ (cutoff onset + 1 : ℕ) := by exact_mod_cast (by omega : n ≤ cutoff onset + 1)
    calc
      d ≤ 1 / (cutoff onset + 1 : ℕ) := hdsmall
      _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn' hsmall
      _ ≤ relativeHamming x y := inverse_length_le_relativeHamming (by omega) x y hxy

theorem patched_decoder (F : BinaryFamily) (onset rate : ℕ) (distance radius r : ℝ)
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (hrlarge : r ≤ radius / lossFactor rate) (hrsmall : r < 1 / (cutoff onset + 1 : ℕ))
    (n : ℕ) (hn : 2 ≤ n) (x : BitInput n) :
    ∀ y : BitInput ((patchedFamily F D).length n),
      relativeHamming ((patchedFamily F D).enc n x) y ≤ r → (patchedFamily F D).decoder n y = x := by
  change ∀ y : BitInput (patchedAt F D n).size,
    relativeHamming ((patchedAt F D n).encode x) y ≤ r → (patchedAt F D n).decoder y = x
  by_cases hlarge : cutoff onset ≤ n
  · rw [patchedAt, if_pos hlarge]
    change ∀ y : BitInput ((threeBlock F).length n),
      relativeHamming (fun i => parityOn (sourceSupport (threeBlock F) n i) x) y ≤ r → threeDecoder F D n y = x
    simp only [← sourceSupport_enc (threeBlock F) (threeBlock_linear F hlinear)]
    intro y hy
    exact threeDecoder_correct F onset rate distance radius hd hmin hrate D n hlarge x y (hy.trans hrlarge)
  · rw [patchedAt, if_neg hlarge]
    change ∀ y : BitInput n, relativeHamming (fun i => parityOn {i} x) y ≤ r → y = x
    simp only [parityOn, Finset.toList_singleton, List.foldl_cons, List.foldl_nil, Bool.false_xor]
    intro y hy
    by_contra hxy
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsmall : (n : ℝ) ≤ (cutoff onset + 1 : ℕ) := by exact_mod_cast (by omega : n ≤ cutoff onset + 1)
    have hxy' : x ≠ y := Ne.symm hxy
    have hl := inverse_length_le_relativeHamming (by omega) x y hxy'
    have hdiv := one_div_le_one_div_of_le hn' hsmall
    linarith

/-- Distance is strictly below all the available distance bounds and below one. -/
noncomputable def codeDistance (onset rate : ℕ) (distance : ℝ) : ℝ :=
  min (distance / lossFactor rate) (min (1 / (cutoff onset + 1 : ℕ)) (1 / 2)) / 2

/-- Radius is strictly inside both the decoder promise and the chosen distance. -/
noncomputable def codeRadius (onset rate : ℕ) (distance radius : ℝ) : ℝ :=
  min (radius / lossFactor rate) (codeDistance onset rate distance) / 2

theorem codeDistance_pos (onset rate : ℕ) (distance : ℝ) (hd : 0 < distance) :
    0 < codeDistance onset rate distance := by
  have hC : (0 : ℝ) < lossFactor rate := by exact_mod_cast lossFactor_pos rate
  unfold codeDistance
  positivity

theorem codeDistance_bounds (onset rate : ℕ) (distance : ℝ) (hd : 0 < distance) :
    codeDistance onset rate distance ≤ distance / lossFactor rate ∧
    codeDistance onset rate distance ≤ 1 / (cutoff onset + 1 : ℕ) ∧
    codeDistance onset rate distance < 1 := by
  have hp := codeDistance_pos onset rate distance hd
  have h0 := min_le_left (distance / (lossFactor rate : ℝ)) (min (1 / (cutoff onset + 1 : ℕ)) (1 / 2))
  have h1 := (min_le_right (distance / (lossFactor rate : ℝ)) (min (1 / (cutoff onset + 1 : ℕ)) (1 / 2))).trans
    (min_le_left (1 / (cutoff onset + 1 : ℕ) : ℝ) (1 / 2))
  have h2 := (min_le_right (distance / (lossFactor rate : ℝ)) (min (1 / (cutoff onset + 1 : ℕ)) (1 / 2))).trans
    (min_le_right (1 / (cutoff onset + 1 : ℕ) : ℝ) (1 / 2))
  unfold codeDistance at hp ⊢
  constructor
  · linarith
  constructor <;> linarith

theorem codeRadius_bounds (onset rate : ℕ) (distance radius : ℝ) (hd : 0 < distance) (hr : 0 < radius) :
    0 < codeRadius onset rate distance radius ∧
    codeRadius onset rate distance radius < codeDistance onset rate distance ∧
    codeRadius onset rate distance radius ≤ radius / lossFactor rate := by
  have hC : (0 : ℝ) < lossFactor rate := by exact_mod_cast lossFactor_pos rate
  have hd' := codeDistance_pos onset rate distance hd
  have hr' : 0 < radius / (lossFactor rate : ℝ) := div_pos hr hC
  have hm : 0 < min (radius / (lossFactor rate : ℝ)) (codeDistance onset rate distance) := lt_min hr' hd'
  have h0 := min_le_left (radius / (lossFactor rate : ℝ)) (codeDistance onset rate distance)
  have h1 := min_le_right (radius / (lossFactor rate : ℝ)) (codeDistance onset rate distance)
  unfold codeRadius
  constructor
  · positivity
  constructor <;> linarith

/-- All four mathematical clauses of the code target, with explicit family
and constants; the two ordinary/TM2 algorithm realizations remain separate. -/
theorem patched_mathematics (F : BinaryFamily) (onset rate : ℕ) (distance radius : ℝ)
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (hd : 0 < distance) (hr : 0 < radius) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k) :
    let E := patchedFamily F D
    let d := codeDistance onset rate distance
    let r := codeRadius onset rate distance radius
    0 < r ∧ r < d ∧ d < 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ j, (E.support n j).card ≤ n / 2) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y → d ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    (∀ n, 2 ≤ n → ∀ x : BitInput n, ∀ y : BitInput (E.length n),
      relativeHamming (E.enc n x) y ≤ r → E.decoder n y = x) := by
  dsimp only
  obtain ⟨hdlarge, hdsmall, hd1⟩ := codeDistance_bounds onset rate distance hd
  obtain ⟨hr0, hrd, hrlarge⟩ := codeRadius_bounds onset rate distance radius hd hr
  refine ⟨hr0, hrd, hd1, ⟨rate + 1, fun n _ => patched_length F D rate hrate n⟩,
    patched_support F D hlinear, ?_, ?_⟩
  · exact patched_distance F onset rate distance radius _ D hlinear hd hmin hrate hdlarge hdsmall
  · exact patched_decoder F onset rate distance radius _ D hlinear hd hmin hrate hrlarge (hrd.trans_le hdsmall)

/-- Lemma 26 alone supplies the complete mathematical code interface. The
full algorithmic target additionally requires the encoder and decoder programs. -/
theorem mathematics_of_lemma26 (hsource : Lemma26) :
    ∃ E : LinearCodeFamily, ∃ distance radius : ℝ,
      0 < radius ∧ radius < distance ∧ distance < 1 ∧
      (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
      (∀ n, 2 ≤ n → ∀ j, (E.support n j).card ≤ n / 2) ∧
      (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y → distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
      (∀ n, 2 ≤ n → ∀ x : BitInput n, ∀ y : BitInput (E.length n),
        relativeHamming (E.enc n x) y ≤ radius → E.decoder n y = x) := by
  obtain ⟨F, distance, fraction, onset, rate, hd, hf, hlinear, hrate, hmin, _, ⟨D⟩⟩ := hsource
  exact ⟨patchedFamily F D, codeDistance onset rate distance,
    codeRadius onset rate distance (fraction * distance),
    patched_mathematics F onset rate distance (fraction * distance) D hlinear hd (mul_pos hf hd) hmin hrate⟩

theorem patched_length_lower (F : BinaryFamily) (onset : ℕ) (distance radius : ℝ)
    (D : PromisedDecoder F onset radius) (hd : 0 < distance)
    (hmin : MinimumDistance F onset distance) (n : ℕ) : n ≤ (patchedFamily F D).length n := by
  change n ≤ (patchedAt F D n).size
  by_cases hn : cutoff onset ≤ n
  · rw [patchedAt, if_pos hn]
    have h0 := source_length_lower F onset distance hd hmin _ (blockSize_large onset n hn 0).1
    have h1 := source_length_lower F onset distance hd hmin _ (blockSize_large onset n hn 1).1
    have h2 := source_length_lower F onset distance hd hmin _ (blockSize_large onset n hn 2).1
    change n ≤ (threeBlock F).length n
    change n ≤ F.length (blockSize n 0) + F.length (blockSize n 1) + F.length (blockSize n 2)
    have hsum := add_le_add (add_le_add h0 h1) h2
    rwa [blockSize_sum] at hsum
  · rw [patchedAt, if_neg hn]
    exact le_rfl

end NearCubicGates.Adapters.Code
