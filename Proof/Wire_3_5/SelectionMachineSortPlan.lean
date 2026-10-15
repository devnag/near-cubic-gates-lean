import Proof.Wire_3_5.SelectionMachineMathDefs
import Proof.Wire_3_5.FinalPassWordMap
import Proof.MachineModel.OrdinaryRadixSemantics

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-! ## Keys, tags and the sweep -/

/-- The record of a width-`W` key: its low-bit-first word (base `SignedSortKey.record`). -/
def keyRec (W x : ℕ) : StablePartition.Record := record (binary W x)

/-- **A key stream**: the base sorter's stream of the width-`W` words of `l`. -/
def keyStream (W : ℕ) (l : List ℕ) : List Bool := StablePartition.stream (l.map (keyRec W))

/-- An inner key sorts after an equal query. -/
def tagA (a : ℕ) : ℕ := 2 * a + 1

/-- A query. -/
def tagB (b : ℕ) : ℕ := 2 * b

/-- The sweep: count the inner keys seen, and add the count at each query. -/
def scanRef (l : List ℕ) : ℕ × ℕ :=
  l.foldl (fun p x => if x % 2 = 1 then (p.1 + 1, p.2) else (p.1, p.2 + p.1)) (0, 0)

/-- The sorted permutation. -/
def sorted (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

/-- A width-`W` number on stream `i`, head at its start. -/
def NumOn {ns nr : ℕ} (σ : WState ns nr) (i : Fin (ns + 1)) (W v : ℕ) : Prop :=
  σ.st i = frame (binary W v) ∧ σ.sh i = 0

/-! ## The residuals -/

/-- **The sweep of a sorted permutation of the tagged keys is the `<`-join.** -/
def ScanJoin : Prop :=
  ∀ (A B l : List ℕ), l.Perm (A.map tagA ++ B.map tagB) → l.Pairwise (· ≤ ·) → (scanRef l).2 = joinLt A B

variable {ns nr : ℕ}

/-- **The sort**: from the key stream of `l` on `S` (a scratch stream `S'` of the same length), `S` ends holding the key
stream of `sorted l` and `S'` some list of the same length, with every head back at `0` and the scratch registers
`regs` back at `0`. -/
def SortSpec (cap W : ℕ) (P : WM ns nr) (S S' : Fin (ns + 1)) (regs : List (Fin nr)) (cost : ℕ → ℕ → ℕ) : Prop :=
  ∀ (σ : WState ns nr) (l : List ℕ), 1 ≤ W → (∀ x ∈ l, x < 2 ^ W) → σ.st S = keyStream W l → σ.sh S = 0 →
    (σ.st S').length = (keyStream W l).length → σ.sh S' = 0 → (∀ r ∈ regs, σ.val r = 0) →
    (keyStream W l).length + 2 ≤ cap →
      ∃ junk : List Bool, junk.length = (keyStream W l).length ∧
        WExec cap P σ ((σ.sets S (keyStream W (sorted l))).sets S' junk) (cost W l.length)

/-- **The sweep**: over the key stream of `l` on `S`, add the sweep's total to the number on `TOT`, using the zero
counter `CNT`; every head, `CNT` and the scratch registers come back. -/
def ScanSpec (cap W : ℕ) (P : WM ns nr) (S CNT TOT : Fin (ns + 1)) (regs : List (Fin nr)) (cost : ℕ → ℕ → ℕ) :
    Prop :=
  ∀ (σ : WState ns nr) (l : List ℕ) (t0 : ℕ), 1 ≤ W → (∀ x ∈ l, x < 2 ^ W) → σ.st S = keyStream W l → σ.sh S = 0 →
    NumOn σ CNT W 0 → NumOn σ TOT W t0 → (scanRef l).1 < 2 ^ W → t0 + (scanRef l).2 < 2 ^ W →
    (∀ r ∈ regs, σ.val r = 0) → (keyStream W l).length + 2 ≤ cap →
      WExec cap P σ (σ.sets TOT (frame (binary W (t0 + (scanRef l).2)))) (cost W l.length)

/-- **The join-accumulate** (the interface C1.4 and C1.5 consume): from a key stream of any arrangement `l` of the
tagged keys, add `joinLt A B` to `TOT`; the key stream ends sorted and its scratch `S'` keeps its length. -/
def JoinSpec (cap W : ℕ) (P : WM ns nr) (S S' CNT TOT : Fin (ns + 1)) (regs : List (Fin nr)) (cost : ℕ → ℕ → ℕ) :
    Prop :=
  ∀ (σ : WState ns nr) (A B l : List ℕ) (t0 : ℕ), 1 ≤ W → l.Perm (A.map tagA ++ B.map tagB) →
    (∀ x ∈ l, x < 2 ^ W) → σ.st S = keyStream W l → σ.sh S = 0 → (σ.st S').length = (keyStream W l).length →
    σ.sh S' = 0 → NumOn σ CNT W 0 → NumOn σ TOT W t0 → A.length < 2 ^ W → t0 + joinLt A B < 2 ^ W →
    (∀ r ∈ regs, σ.val r = 0) → (keyStream W l).length + 2 ≤ cap →
      ∃ junk : List Bool, junk.length = (keyStream W l).length ∧
        WExec cap P σ (((σ.sets S (keyStream W (sorted l))).sets S' junk).sets TOT
          (frame (binary W (t0 + joinLt A B)))) (cost W l.length)

/-! ## Composition -/

theorem sorted_perm (l : List ℕ) : (sorted l).Perm l := List.perm_insertionSort _ l

theorem sorted_pairwise (l : List ℕ) : (sorted l).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ l

theorem sorted_length (l : List ℕ) : (sorted l).length = l.length := (sorted_perm l).length_eq

/-- The sweep's count is the number of inner keys. -/
theorem scanRef_fst : ∀ (l : List ℕ) (p : ℕ × ℕ),
    (l.foldl (fun p x => if x % 2 = 1 then (p.1 + 1, p.2) else (p.1, p.2 + p.1)) p).1 =
      p.1 + l.countP (fun x => x % 2 = 1)
  | [], p => by simp
  | x :: l, p => by
    rw [List.foldl_cons, scanRef_fst l, List.countP_cons]
    have e1 : (if x % 2 = 1 then (p.1 + 1, p.2) else (p.1, p.2 + p.1)).1 = p.1 + (if x % 2 = 1 then 1 else 0) := by
      split_ifs <;> rfl
    rw [e1]
    simp only [decide_eq_true_eq]
    omega

theorem countP_odd_tagged (A B : List ℕ) :
    (A.map tagA ++ B.map tagB).countP (fun x => x % 2 = 1) = A.length := by
  rw [List.countP_append, List.countP_map, List.countP_map]
  have h1 : A.countP ((fun x => decide (x % 2 = 1)) ∘ tagA) = A.length := by
    rw [List.countP_eq_length]; intro a _; simp [tagA, Nat.add_mod]
  have h2 : B.countP ((fun x => decide (x % 2 = 1)) ∘ tagB) = 0 := by
    rw [List.countP_eq_zero]; intro b _; simp [tagB]
  rw [h1, h2, Nat.add_zero]

theorem frame_length (bs : List Bool) : (frame bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [frame, List.length_cons, ih]; ring

/-- A key stream's length depends only on the number of keys. -/
theorem keyStream_length (W : ℕ) (hW : 1 ≤ W) (l : List ℕ) :
    (keyStream W l).length = l.length * (2 * W + 1) + 1 := by
  have hrec : ∀ x, (StablePartition.recordBits (keyRec W x)).length = 2 * W + 1 := by
    intro x
    obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
    simp only [keyRec, binary, record, StablePartition.recordBits, List.length_cons, frame_length, binary_length]
    ring
  unfold keyStream StablePartition.stream StablePartition.recordsBits
  induction l with
  | nil => simp
  | cons x l ih =>
    have e : (x :: l).length * (2 * W + 1) = l.length * (2 * W + 1) + (2 * W + 1) := by
      rw [List.length_cons]; ring
    rw [List.map_cons, List.flatMap_cons, List.length_append, List.length_append, hrec, e]
    rw [List.length_append] at ih
    omega

/-- **Sort, then sweep, is the join-accumulate.** -/
theorem joinSpec_of (hj : ScanJoin) {cap W : ℕ} {sortP scanP : WM ns nr} {S S' CNT TOT : Fin (ns + 1)}
    {regs : List (Fin nr)} {cs cc : ℕ → ℕ → ℕ} (hsort : SortSpec cap W sortP S S' regs cs)
    (hscan : ScanSpec cap W scanP S CNT TOT regs cc) (hSS' : S ≠ S') (hSC : S ≠ CNT) (hST : S ≠ TOT)
    (hS'C : S' ≠ CNT) (hS'T : S' ≠ TOT) :
    JoinSpec cap W (.seq sortP scanP) S S' CNT TOT regs (fun w m => cs w m + 1 + cc w m) := by
  intro σ A B l t0 hW hperm hl hS hSh hS' hS'h hC hT hA ht hr hcap
  obtain ⟨junk, hjl, h1⟩ := hsort σ l hW hl hS hSh hS' hS'h hr hcap
  set σ1 := (σ.sets S (keyStream W (sorted l))).sets S' junk with hσ1
  have hjoin : (scanRef (sorted l)).2 = joinLt A B :=
    hj A B (sorted l) ((sorted_perm l).trans hperm) (sorted_pairwise l)
  have hcnt : (scanRef (sorted l)).1 = A.length := by
    unfold scanRef
    rw [scanRef_fst, (sorted_perm l).countP_eq, hperm.countP_eq, countP_odd_tagged]
    simp
  have hst : ∀ i, i ≠ S → i ≠ S' → σ1.st i = σ.st i := by
    intro i h1 h2
    simp [hσ1, h1, h2]
  have h2 := hscan σ1 (sorted l) t0 hW (fun x hx => hl x ((sorted_perm l).subset hx))
    (by simp [hσ1, hSS'])
    (by simp [hσ1, hSh])
    ⟨by rw [hst CNT (Ne.symm hSC) (Ne.symm hS'C)]; exact hC.1, by simp [hσ1, hC.2]⟩
    ⟨by rw [hst TOT (Ne.symm hST) (Ne.symm hS'T)]; exact hT.1, by simp [hσ1, hT.2]⟩
    (by rw [hcnt]; exact hA) (by rw [hjoin]; exact ht) (by simpa [hσ1] using hr)
    (by rw [keyStream_length W hW, sorted_length, ← keyStream_length W hW]; exact hcap)
  rw [hjoin, sorted_length] at h2
  exact ⟨junk, hjl, WExec.seq h1 h2⟩

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort
