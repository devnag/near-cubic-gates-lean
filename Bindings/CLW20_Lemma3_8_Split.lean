import Proof.Foundations.SourceInterfaces

/-! # CLW20 Lemma 3.8, Appendix A: the split `x = yz`

CLW20 (ECCC TR20-150), Appendix A, PDF p.50, printed p.49:

> "For an input x to f^{⊕k}, we write x = yz such that |y| = n, |z| = (k − 1)n."

Definition 3.7 (PDF p.17, printed p.16): "f^{⊕k}(x_1, ..., x_k) := ⊕_{1≤i≤k} f(x_i)". The
imported `xorPower` folds over `Finset.univ.toList`, whose order is not canonical;
`xorPower_eq_finRange` puts it in block order, and `xorPower_join` is the identity
`f^{⊕(k+1)}(y,z) = f(y) ⊕ f^{⊕k}(z)` that both cases of the proof use. `fixFirst` and `fixRest` show
that the two restrictions the proof applies — `C′(z) := C(y,z)` in Case 1 and `y ↦ C(y,z_i)` in
Case 2 — are literal projections, so they stay in any `LiteralProjectionClosed` family ("The atoms
may be restrictions or negated restrictions of C"). Here `k + 1` blocks play the paper's `k`. -/
namespace NearCubicWires.Bindings.CLW20Lemma38
open NearCubicWires SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem succ_mul_eq (k n : ℕ) : (k + 1) * n = k * n + n := Nat.succ_mul k n

/-- The concatenation `yz`: block 0 is `y`, blocks 1..k are `z`. -/
def joinInput {n k : ℕ} (y : BitInput n) (z : BitInput (k * n)) : BitInput ((k + 1) * n) :=
  fun c => if h : c.val < n then y ⟨c.val, h⟩ else
    z ⟨c.val - n, by have h1 := c.isLt; have h2 := succ_mul_eq k n; omega⟩

theorem foldl_xor_shift {β : Type*} (g : β → Bool) (a : Bool) (l : List β) :
    l.foldl (fun p b => xor p (g b)) a = xor a (l.foldl (fun p b => xor p (g b)) false) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor a (g b)), ih (g b), Bool.xor_assoc]

theorem foldl_xor_perm {β : Type*} (g : β → Bool) {l₁ l₂ : List β} (h : l₁.Perm l₂) (a : Bool) :
    l₁.foldl (fun p b => xor p (g b)) a = l₂.foldl (fun p b => xor p (g b)) a := by
  refine h.foldl_eq' ?_ a
  intro x _ y _ z
  simp only [Bool.xor_assoc, Bool.xor_comm (g x) (g y)]

theorem univ_toList_perm (k : ℕ) :
    ((Finset.univ : Finset (Fin k)).toList).Perm (List.finRange k) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange k)).mpr
  intro i
  simp

/-- `xorPower` in canonical block order. -/
theorem xorPower_eq_finRange {n : ℕ} (f : BoolFunction n) (k : ℕ) (x : BitInput (k * n)) :
    xorPower f k x = (List.finRange k).foldl (fun p b => xor p (f (blockInput x b))) false :=
  foldl_xor_perm _ (univ_toList_perm k) false

theorem blockInput_join_zero {n k : ℕ} (y : BitInput n) (z : BitInput (k * n)) :
    blockInput (joinInput y z) (0 : Fin (k + 1)) = y := by
  funext i
  simp [blockInput, joinInput]

theorem blockInput_join_succ {n k : ℕ} (y : BitInput n) (z : BitInput (k * n)) (b : Fin k) :
    blockInput (joinInput y z) b.succ = blockInput z b := by
  funext i
  have hi := i.isLt
  simp only [blockInput, joinInput, Fin.val_succ]
  have hlt : ¬ ((b.val + 1) * n + i.val < n) := by
    rw [Nat.succ_mul]; omega
  rw [dif_neg hlt]
  congr 2
  rw [Nat.succ_mul]; omega

/-- `f^{⊕(k+1)}(y,z) = f(y) ⊕ f^{⊕k}(z)` for the imported `xorPower`. -/
theorem xorPower_join {n k : ℕ} (f : BoolFunction n) (y : BitInput n) (z : BitInput (k * n)) :
    xorPower f (k + 1) (joinInput y z) = xor (f y) (xorPower f k z) := by
  rw [xorPower_eq_finRange, xorPower_eq_finRange, List.finRange_succ, List.foldl_cons,
    List.foldl_map, Bool.false_xor, blockInput_join_zero, foldl_xor_shift]
  congr 1
  congr 1
  funext p b
  rw [blockInput_join_succ]

/-- One block: `f^{⊕1}` is `f` read through the identity reindexing of `1·n` coordinates. -/
def oneBlock {n : ℕ} (y : BitInput n) : BitInput (1 * n) :=
  fun c => y ⟨c.val, by have h := c.isLt; omega⟩

theorem xorPower_one {n : ℕ} (f : BoolFunction n) (y : BitInput n) :
    xorPower f 1 (oneBlock y) = f y := by
  rw [xorPower_eq_finRange]
  simp only [List.finRange_succ, List.finRange_zero, List.map_nil, List.foldl_cons,
    List.foldl_nil, Bool.false_xor]
  congr 1
  funext i
  simp [blockInput, oneBlock]

/-- The Case 1 restriction `z ↦ C(y,z)` as a literal projection. -/
def fixFirst {n k : ℕ} (y : BitInput n) : Fin ((k + 1) * n) → ProjectedRandomBit (k * n) :=
  fun c => if h : c.val < n then .constant (y ⟨c.val, h⟩) else
    .bit ⟨c.val - n, by have h1 := c.isLt; have h2 := succ_mul_eq k n; omega⟩

theorem fixFirst_eval {n k : ℕ} (y : BitInput n) (z : BitInput (k * n)) :
    (fun c => (fixFirst (k := k) y c).eval z) = joinInput y z := by
  funext c
  unfold fixFirst joinInput
  split <;> rfl

/-- The Case 2 atom `y ↦ C(y,z_i)` as a literal projection. -/
def fixRest {n k : ℕ} (z : BitInput (k * n)) : Fin ((k + 1) * n) → ProjectedRandomBit n :=
  fun c => if h : c.val < n then .bit ⟨c.val, h⟩ else
    .constant (z ⟨c.val - n, by have h1 := c.isLt; have h2 := succ_mul_eq k n; omega⟩)

theorem fixRest_eval {n k : ℕ} (y : BitInput n) (z : BitInput (k * n)) :
    (fun c => (fixRest (n := n) z c).eval y) = joinInput y z := by
  funext c
  unfold fixRest joinInput
  split <;> rfl

/-- The `k = 1` reindexing as a literal projection. -/
def oneBlockProjection (n : ℕ) : Fin (1 * n) → ProjectedRandomBit n :=
  fun c => .bit ⟨c.val, by have h := c.isLt; omega⟩

theorem oneBlockProjection_eval {n : ℕ} (y : BitInput n) :
    (fun c => (oneBlockProjection n c).eval y) = oneBlock y := rfl

end NearCubicWires.Bindings.CLW20Lemma38
