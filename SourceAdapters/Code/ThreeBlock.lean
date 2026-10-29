import SourceAdapters.Code.Support

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the three-block construction in CW19 Lemma 27's proof. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code

def joinWord {a b : ℕ} (x : BitInput a) (y : BitInput b) : BitInput (a + b) :=
  Fin.addCases x y

@[simp] theorem joinWord_left {a b : ℕ} (x : BitInput a) (y : BitInput b) (i : Fin a) :
    joinWord x y (Fin.castAdd b i) = x i := by simp [joinWord]

@[simp] theorem joinWord_right {a b : ℕ} (x : BitInput a) (y : BitInput b) (i : Fin b) :
    joinWord x y (Fin.natAdd a i) = y i := by simp [joinWord]

theorem joinWord_zero (a b : ℕ) :
    joinWord (fun _ : Fin a => false) (fun _ : Fin b => false) = fun _ => false := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem joinWord_xor {a b : ℕ} (x x' : BitInput a) (y y' : BitInput b) :
    joinWord (fun i => xor (x i) (x' i)) (fun j => xor (y j) (y' j)) =
      fun k => xor (joinWord x y k) (joinWord x' y' k) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

/-- Explicit inclusions of the three consecutive message intervals. -/
def firstIndex (n : ℕ) : Fin (blockSize n 0) ↪ Fin n where
  toFun i := ⟨i.val, by have h := blockSize_sum n; have hi := i.isLt; omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun z : Fin n => z.val) h

def secondIndex (n : ℕ) : Fin (blockSize n 1) ↪ Fin n where
  toFun i := ⟨blockSize n 0 + i.val, by have h := blockSize_sum n; have hi := i.isLt; omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def thirdIndex (n : ℕ) : Fin (blockSize n 2) ↪ Fin n where
  toFun i := ⟨blockSize n 0 + blockSize n 1 + i.val,
    by have h := blockSize_sum n; have hi := i.isLt; omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def threeBlock (F : BinaryFamily) : BinaryFamily where
  length n := F.length (blockSize n 0) + F.length (blockSize n 1) + F.length (blockSize n 2)
  encode n x := joinWord
    (joinWord (F.encode (blockSize n 0) (x ∘ firstIndex n))
      (F.encode (blockSize n 1) (x ∘ secondIndex n)))
    (F.encode (blockSize n 2) (x ∘ thirdIndex n))

theorem threeBlock_linear (F : BinaryFamily) (hlinear : IsLinear F) : IsLinear (threeBlock F) := by
  constructor
  · intro n
    change joinWord (joinWord (F.encode _ (fun _ => false))
      (F.encode _ (fun _ => false))) (F.encode _ (fun _ => false)) = _
    rw [hlinear.1, hlinear.1, hlinear.1, joinWord_zero, joinWord_zero]
    rfl
  · intro n x y
    change joinWord (joinWord (F.encode _ (fun i => xor ((x ∘ firstIndex n) i) ((y ∘ firstIndex n) i)))
      (F.encode _ (fun i => xor ((x ∘ secondIndex n) i) ((y ∘ secondIndex n) i))))
      (F.encode _ (fun i => xor ((x ∘ thirdIndex n) i) ((y ∘ thirdIndex n) i))) = _
    rw [hlinear.2, hlinear.2, hlinear.2, joinWord_xor, joinWord_xor]
    rfl

theorem threeBlock_length_upper (F : BinaryFamily) (onset rate n : ℕ)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (hn : 6 * (onset + 1) ≤ n) : (threeBlock F).length n ≤ rate * n := by
  have h0 := hrate _ (blockSize_large onset n hn 0).1
  have h1 := hrate _ (blockSize_large onset n hn 1).1
  have h2 := hrate _ (blockSize_large onset n hn 2).1
  change F.length (blockSize n 0) + F.length (blockSize n 1) + F.length (blockSize n 2) ≤ _
  calc
    _ ≤ rate * blockSize n 0 + rate * blockSize n 1 + rate * blockSize n 2 :=
      add_le_add (add_le_add h0 h1) h2
    _ = rate * n := by rw [← Nat.mul_add, ← Nat.mul_add, blockSize_sum]

/-- A functional that sees only the embedded coordinates has no basis support
outside them. This supplies the actual sparsity proof, independently of the
chosen source linear code. -/
theorem functionalSupport_pull_subset {n m : ℕ} (e : Fin m ↪ Fin n)
    (f : BitInput m → Bool) (hzero : f (fun _ => false) = false) :
    functionalSupport (fun x => f (x ∘ e)) ⊆ Finset.univ.map e := by
  classical
  intro i hi
  by_contra hout
  have hi' : f ((unitVector i) ∘ e) = true := (Finset.mem_filter.mp hi).2
  have he : ((unitVector i) ∘ e) = fun _ => false := by
    funext j
    have hji : e j ≠ i := by
      intro h
      apply hout
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, h⟩
    simp [unitVector, hji]
  rw [he, hzero] at hi'
  contradiction

theorem functionalSupport_pull_card {n m : ℕ} (e : Fin m ↪ Fin n)
    (f : BitInput m → Bool) (hzero : f (fun _ => false) = false) :
    (functionalSupport (fun x => f (x ∘ e))).card ≤ m := by
  have h := Finset.card_le_card (functionalSupport_pull_subset e f hzero)
  simpa using h

theorem threeBlock_support_bound (F : BinaryFamily) (hlinear : IsLinear F)
    (n : ℕ) (hn : 2 ≤ n) (j : Fin ((threeBlock F).length n)) :
    (sourceSupport (threeBlock F) n j).card ≤ n / 2 := by
  change (functionalSupport (fun x => joinWord
    (joinWord (F.encode (blockSize n 0) (x ∘ firstIndex n))
      (F.encode (blockSize n 1) (x ∘ secondIndex n)))
    (F.encode (blockSize n 2) (x ∘ thirdIndex n)) j)).card ≤ _
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [joinWord_left]
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp only [joinWord_left]
      exact (functionalSupport_pull_card (firstIndex n) (fun x => F.encode _ x k)
        (congrFun (hlinear.1 _) k)).trans (blockSize_le_half n hn 0)
    · intro k
      simp only [joinWord_right]
      exact (functionalSupport_pull_card (secondIndex n) (fun x => F.encode _ x k)
        (congrFun (hlinear.1 _) k)).trans (blockSize_le_half n hn 1)
  · intro k
    simp only [joinWord_right]
    exact (functionalSupport_pull_card (thirdIndex n) (fun x => F.encode _ x k)
      (congrFun (hlinear.1 _) k)).trans (blockSize_le_half n hn 2)

/-- An arbitrary coordinate restriction cannot introduce new disagreements. -/
theorem hammingCount_pull_le {n m : ℕ} (e : Fin m ↪ Fin n) (x y : BitInput n) :
    (Finset.univ.filter fun i => x (e i) ≠ y (e i)).card ≤
      (Finset.univ.filter fun j => x j ≠ y j).card := by
  classical
  apply Finset.card_le_card_of_injOn e
  · intro i hi
    simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ h
    exact e.injective h

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": relative errors can grow by at most the inverse block ratio.
This controls both distance loss and concentration of adversarial errors. -/
theorem relativeHamming_pull_le {n m : ℕ} (e : Fin m ↪ Fin n) (hm : 0 < m)
    (C : ℝ) (hratio : (n : ℝ) ≤ C * m) (x y : BitInput n) :
    relativeHamming (x ∘ e) (y ∘ e) ≤ C * relativeHamming x y := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ((Finset.univ.filter fun i => x (e i) ≠ y (e i)).card : ℝ) ≤
      ((Finset.univ.filter fun j => x j ≠ y j).card : ℝ) := by
    exact_mod_cast hammingCount_pull_le e x y
  unfold relativeHamming
  simp only [Function.comp_apply]
  rw [← mul_div_assoc, div_le_div_iff₀ hm' hn']
  have hnn : (0 : ℝ) ≤ (Finset.univ.filter fun j => x j ≠ y j).card := by positivity
  calc
    _ ≤ ((Finset.univ.filter fun j => x j ≠ y j).card : ℝ) * n := mul_le_mul_of_nonneg_right hc hn'.le
    _ ≤ ((Finset.univ.filter fun j => x j ≠ y j).card : ℝ) * (C * m) :=
      mul_le_mul_of_nonneg_left hratio hnn
    _ = _ := by ring

end NearCubicGates.Adapters.Code
