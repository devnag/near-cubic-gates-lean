import SourceAdapters.Code.ThreeBlock

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the losses in distance and promised decoding under concatenation. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

def firstOutputIndex (F : BinaryFamily) (n : ℕ) :
    Fin (F.length (blockSize n 0)) ↪ Fin ((threeBlock F).length n) where
  toFun i := Fin.castAdd _ (Fin.castAdd _ i)
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin ((threeBlock F).length n) => z.val) h

def secondOutputIndex (F : BinaryFamily) (n : ℕ) :
    Fin (F.length (blockSize n 1)) ↪ Fin ((threeBlock F).length n) where
  toFun i := Fin.castAdd _ (Fin.natAdd _ i)
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def thirdOutputIndex (F : BinaryFamily) (n : ℕ) :
    Fin (F.length (blockSize n 2)) ↪ Fin ((threeBlock F).length n) where
  toFun i := Fin.natAdd _ i
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

@[simp] theorem threeBlock_encode_first (F : BinaryFamily) (n : ℕ) (x : BitInput n) :
    (threeBlock F).encode n x ∘ firstOutputIndex F n = F.encode (blockSize n 0) (x ∘ firstIndex n) := by
  funext i
  change joinWord (joinWord (F.encode _ (x ∘ firstIndex n)) (F.encode _ (x ∘ secondIndex n)))
    (F.encode _ (x ∘ thirdIndex n)) (Fin.castAdd _ (Fin.castAdd _ i)) = _
  simp only [joinWord_left]

@[simp] theorem threeBlock_encode_second (F : BinaryFamily) (n : ℕ) (x : BitInput n) :
    (threeBlock F).encode n x ∘ secondOutputIndex F n = F.encode (blockSize n 1) (x ∘ secondIndex n) := by
  funext i
  change joinWord (joinWord (F.encode _ (x ∘ firstIndex n)) (F.encode _ (x ∘ secondIndex n)))
    (F.encode _ (x ∘ thirdIndex n)) (Fin.castAdd _ (Fin.natAdd _ i)) = _
  simp only [joinWord_left, joinWord_right]

@[simp] theorem threeBlock_encode_third (F : BinaryFamily) (n : ℕ) (x : BitInput n) :
    (threeBlock F).encode n x ∘ thirdOutputIndex F n = F.encode (blockSize n 2) (x ∘ thirdIndex n) := by
  funext i
  change joinWord (joinWord (F.encode _ (x ∘ firstIndex n)) (F.encode _ (x ∘ secondIndex n)))
    (F.encode _ (x ∘ thirdIndex n)) (Fin.natAdd _ i) = _
  simp only [joinWord_right]

theorem message_eq_of_blocks (n : ℕ) (x y : BitInput n)
    (h0 : x ∘ firstIndex n = y ∘ firstIndex n)
    (h1 : x ∘ secondIndex n = y ∘ secondIndex n)
    (h2 : x ∘ thirdIndex n = y ∘ thirdIndex n) : x = y := by
  funext j
  have hsum := blockSize_sum n
  have hj := j.isLt
  by_cases hj0 : j.val < blockSize n 0
  · let i : Fin (blockSize n 0) := ⟨j.val, hj0⟩
    have hi : firstIndex n i = j := by apply Fin.ext; rfl
    have h := congrFun h0 i
    simpa only [Function.comp_apply, hi] using h
  · by_cases hj1 : j.val < blockSize n 0 + blockSize n 1
    · let i : Fin (blockSize n 1) := ⟨j.val - blockSize n 0, by omega⟩
      have hi : secondIndex n i = j := by apply Fin.ext; dsimp [secondIndex, i]; omega
      have h := congrFun h1 i
      simpa only [Function.comp_apply, hi] using h
    · let i : Fin (blockSize n 2) := ⟨j.val - (blockSize n 0 + blockSize n 1), by omega⟩
      have hi : thirdIndex n i = j := by apply Fin.ext; dsimp [thirdIndex, i]; omega
      have h := congrFun h2 i
      simpa only [Function.comp_apply, hi] using h

/-- A uniform inverse-ratio bound; `rate+1` also makes the factor positive. -/
def lossFactor (rate : ℕ) : ℕ := 6 * (rate + 1)

theorem lossFactor_pos (rate : ℕ) : 0 < lossFactor rate := by
  unfold lossFactor
  positivity

theorem blockCode_length_pos (F : BinaryFamily) (onset : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (n : ℕ) (hn : 6 * (onset + 1) ≤ n) (i : Fin 3) :
    0 < F.length (blockSize n i) := by
  have hb := blockSize_large onset n hn i
  have hl := source_length_lower F onset distance hd hmin _ hb.1
  omega

theorem threeBlock_length_ratio (F : BinaryFamily) (onset rate : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (n : ℕ) (hn : 6 * (onset + 1) ≤ n) (i : Fin 3) :
    (threeBlock F).length n ≤ lossFactor rate * F.length (blockSize n i) := by
  have hb := blockSize_large onset n hn i
  have hl := source_length_lower F onset distance hd hmin _ hb.1
  calc
    _ ≤ rate * n := threeBlock_length_upper F onset rate n hrate hn
    _ ≤ rate * (6 * blockSize n i) := Nat.mul_le_mul_left rate hb.2
    _ ≤ rate * (6 * F.length (blockSize n i)) :=
      Nat.mul_le_mul_left rate (Nat.mul_le_mul_left 6 hl)
    _ ≤ lossFactor rate * F.length (blockSize n i) := by unfold lossFactor; nlinarith

theorem threeBlock_distance (F : BinaryFamily) (onset rate : ℕ) (distance : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (n : ℕ) (hn : 6 * (onset + 1) ≤ n) (x y : BitInput n) (hxy : x ≠ y) :
    distance / lossFactor rate ≤ relativeHamming ((threeBlock F).encode n x) ((threeBlock F).encode n y) := by
  have hC : (0 : ℝ) < lossFactor rate := by exact_mod_cast lossFactor_pos rate
  have ratio (i : Fin 3) : ((threeBlock F).length n : ℝ) ≤
      (lossFactor rate : ℝ) * F.length (blockSize n i) := by
    exact_mod_cast threeBlock_length_ratio F onset rate distance hd hmin hrate n hn i
  apply (div_le_iff₀ hC).2
  by_cases h0 : x ∘ firstIndex n = y ∘ firstIndex n
  · by_cases h1 : x ∘ secondIndex n = y ∘ secondIndex n
    · have h2 : x ∘ thirdIndex n ≠ y ∘ thirdIndex n := by
        intro h2
        exact hxy (message_eq_of_blocks n x y h0 h1 h2)
      have hs := hmin _ (blockSize_large onset n hn 2).1 _ _ h2
      have hp := relativeHamming_pull_le (thirdOutputIndex F n)
        (blockCode_length_pos F onset distance hd hmin n hn 2) (lossFactor rate) (ratio 2)
        ((threeBlock F).encode n x) ((threeBlock F).encode n y)
      rw [threeBlock_encode_third, threeBlock_encode_third] at hp
      nlinarith
    · have hs := hmin _ (blockSize_large onset n hn 1).1 _ _ h1
      have hp := relativeHamming_pull_le (secondOutputIndex F n)
        (blockCode_length_pos F onset distance hd hmin n hn 1) (lossFactor rate) (ratio 1)
        ((threeBlock F).encode n x) ((threeBlock F).encode n y)
      rw [threeBlock_encode_second, threeBlock_encode_second] at hp
      nlinarith
  · have hs := hmin _ (blockSize_large onset n hn 0).1 _ _ h0
    have hp := relativeHamming_pull_le (firstOutputIndex F n)
      (blockCode_length_pos F onset distance hd hmin n hn 0) (lossFactor rate) (ratio 0)
      ((threeBlock F).encode n x) ((threeBlock F).encode n y)
    rw [threeBlock_encode_first, threeBlock_encode_first] at hp
    nlinarith

/-- Concatenate the three decoded messages and use the proved length identity. -/
def joinMessage (n : ℕ) (x0 : BitInput (blockSize n 0))
    (x1 : BitInput (blockSize n 1)) (x2 : BitInput (blockSize n 2)) : BitInput n :=
  fun j => joinWord (joinWord x0 x1) x2 (Fin.cast (blockSize_sum n).symm j)

theorem joinMessage_reconstruct (n : ℕ) (x : BitInput n) :
    joinMessage n (x ∘ firstIndex n) (x ∘ secondIndex n) (x ∘ thirdIndex n) = x := by
  apply message_eq_of_blocks n
  · funext i
    have hi : Fin.cast (blockSize_sum n).symm (firstIndex n i) =
        Fin.castAdd (blockSize n 2) (Fin.castAdd (blockSize n 1) i) := by apply Fin.ext; rfl
    simp only [Function.comp_apply, joinMessage, hi, joinWord_left]
  · funext i
    have hi : Fin.cast (blockSize_sum n).symm (secondIndex n i) =
        Fin.castAdd (blockSize n 2) (Fin.natAdd (blockSize n 0) i) := by apply Fin.ext; rfl
    simp only [Function.comp_apply, joinMessage, hi, joinWord_left, joinWord_right]
  · funext i
    have hi : Fin.cast (blockSize_sum n).symm (thirdIndex n i) =
        Fin.natAdd (blockSize n 0 + blockSize n 1) i := by apply Fin.ext; rfl
    simp only [Function.comp_apply, joinMessage, hi, joinWord_right]

def threeDecoder (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (n : ℕ)
    (y : BitInput ((threeBlock F).length n)) : BitInput n :=
  joinMessage n
    (totalDecoder F D (blockSize n 0) (y ∘ firstOutputIndex F n))
    (totalDecoder F D (blockSize n 1) (y ∘ secondOutputIndex F n))
    (totalDecoder F D (blockSize n 2) (y ∘ thirdOutputIndex F n))

theorem threeDecoder_correct (F : BinaryFamily) (onset rate : ℕ) (distance radius : ℝ)
    (hd : 0 < distance) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (D : PromisedDecoder F onset radius) (n : ℕ) (hn : 6 * (onset + 1) ≤ n)
    (x : BitInput n) (y : BitInput ((threeBlock F).length n))
    (hnear : relativeHamming ((threeBlock F).encode n x) y ≤ radius / lossFactor rate) :
    threeDecoder F D n y = x := by
  have hC : (0 : ℝ) < lossFactor rate := by exact_mod_cast lossFactor_pos rate
  have ratio (i : Fin 3) : ((threeBlock F).length n : ℝ) ≤
      (lossFactor rate : ℝ) * F.length (blockSize n i) := by
    exact_mod_cast threeBlock_length_ratio F onset rate distance hd hmin hrate n hn i
  have hscaled : (lossFactor rate : ℝ) * relativeHamming ((threeBlock F).encode n x) y ≤ radius := by
    have h := mul_le_mul_of_nonneg_left hnear hC.le
    simpa [mul_div_cancel₀, hC.ne'] using h
  have h0 : totalDecoder F D (blockSize n 0) (y ∘ firstOutputIndex F n) = x ∘ firstIndex n := by
    apply totalDecoder_correct F D _ (blockSize_large onset n hn 0).1
    have hp := relativeHamming_pull_le (firstOutputIndex F n)
      (blockCode_length_pos F onset distance hd hmin n hn 0) (lossFactor rate) (ratio 0)
      ((threeBlock F).encode n x) y
    rw [threeBlock_encode_first] at hp
    exact hp.trans hscaled
  have h1 : totalDecoder F D (blockSize n 1) (y ∘ secondOutputIndex F n) = x ∘ secondIndex n := by
    apply totalDecoder_correct F D _ (blockSize_large onset n hn 1).1
    have hp := relativeHamming_pull_le (secondOutputIndex F n)
      (blockCode_length_pos F onset distance hd hmin n hn 1) (lossFactor rate) (ratio 1)
      ((threeBlock F).encode n x) y
    rw [threeBlock_encode_second] at hp
    exact hp.trans hscaled
  have h2 : totalDecoder F D (blockSize n 2) (y ∘ thirdOutputIndex F n) = x ∘ thirdIndex n := by
    apply totalDecoder_correct F D _ (blockSize_large onset n hn 2).1
    have hp := relativeHamming_pull_le (thirdOutputIndex F n)
      (blockCode_length_pos F onset distance hd hmin n hn 2) (lossFactor rate) (ratio 2)
      ((threeBlock F).encode n x) y
    rw [threeBlock_encode_third] at hp
    exact hp.trans hscaled
  rw [threeDecoder, h0, h1, h2, joinMessage_reconstruct]

end NearCubicGates.Adapters.Code
