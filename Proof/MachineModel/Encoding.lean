import Proof.MachineModel.OrdinaryUnaryTemplate
import Proof.Foundations.OrdinaryStreaming
import Proof.Amplification.RecoveryTimedExecution

/-! Ordered raw incidence data for the rows branch (outside supplier, partitioned
under `ExtIncidence`). A monomial stream over child indices and the row-major
incidence table it denotes: exactly the `rows.flatten` word read by the checked
polynomial bank. Pure list semantics; the machine lives in `ExtIncidence.Machine`.
Duplicate monomials stay separate rows; repeated indices inside one monomial
collapse; the empty monomial is an all-zero row; the empty stream is no row. -/
namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One child index `d` as a shifted unary block (`d+1` marks, one terminator).
This is `RowIndexField.word (d+1)`, so existing index writers apply. -/
def block (d : ℕ) : List Bool := List.replicate (d+1) true ++ [false]
/-- One monomial: start mark, its index blocks in source order, end mark. -/
def monomialWord (m : List ℕ) : List Bool := true :: (m.flatMap block ++ [false])
/-- The ordered monomial stream, closed by one end-of-stream mark. -/
def stream (ms : List (List ℕ)) : List Bool := ms.flatMap monomialWord ++ [false]
/-- The incidence row of one monomial over `B` children. -/
def maskOf (B : ℕ) (m : List ℕ) : List Bool := List.ofFn (fun i : Fin B => decide (i.val ∈ m))
/-- The row-major incidence table (`rows.flatten` of the bank). -/
def table (B : ℕ) (ms : List (List ℕ)) : List Bool := (ms.map (maskOf B)).flatten

def blockCost (d : ℕ) : ℕ := 2*d+4
def monomialCost (B : ℕ) (m : List ℕ) : ℕ := 2*B+4+(m.map blockCost).sum
def cost (B : ℕ) (ms : List (List ℕ)) : ℕ := (ms.map (monomialCost B)).sum+1

@[simp] theorem block_length (d : ℕ) : (block d).length = d+2 := by simp [block]
@[simp] theorem maskOf_length (B : ℕ) (m : List ℕ) : (maskOf B m).length = B := by simp [maskOf]
theorem block_cons (d : ℕ) : block d = true :: (List.replicate d true ++ [false]) := by
  simp [block, List.replicate_succ]
theorem monomialWord_length (m : List ℕ) : (monomialWord m).length = (m.flatMap block).length+2 := by
  simp [monomialWord]
theorem stream_nil : stream [] = [false] := by simp [stream]
theorem stream_cons (m : List ℕ) (ms : List (List ℕ)) : stream (m :: ms) = monomialWord m ++ stream ms := by
  simp [stream]
theorem table_nil (B : ℕ) : table B [] = [] := by simp [table]
theorem table_cons (B : ℕ) (m : List ℕ) (ms : List (List ℕ)) : table B (m :: ms) = maskOf B m ++ table B ms := by
  simp [table]
theorem table_length (B : ℕ) (ms : List (List ℕ)) : (table B ms).length = ms.length*B := by
  induction ms with
  | nil => simp [table_nil]
  | cons m ms ih => rw [table_cons, List.length_append, maskOf_length, ih, List.length_cons]; ring
theorem cost_cons (B : ℕ) (m : List ℕ) (ms : List (List ℕ)) :
    cost B (m :: ms) = monomialCost B m + cost B ms := by
  simp [cost]; omega
theorem monomialCost_cons (B d : ℕ) (m : List ℕ) :
    monomialCost B (d :: m) = blockCost d + monomialCost B m := by
  simp [monomialCost]; omega

theorem maskOf_nil (B : ℕ) : maskOf B [] = List.replicate B false := by
  simp [maskOf, List.ofFn_const]
theorem maskOf_congr (B : ℕ) {S T : List ℕ} (h : ∀ i, i ∈ S ↔ i ∈ T) : maskOf B S = maskOf B T := by
  unfold maskOf
  congr 1
  funext i
  exact decide_eq_decide.mpr (h i.val)

/-! ## Local tape-cell lemmas -/

theorem writeTapeBit_eq_set (l : List Bool) (k : ℕ) (v : Bool) (hk : k < l.length) :
    writeTapeBit l k v = l.set k v := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b l ih =>
    cases k with
    | zero => simp [writeTapeBit]
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      simp [writeTapeBit, ih k hk]

theorem writeTapeBit_ofFn {B : ℕ} (g : Fin B → Bool) (k : ℕ) (hk : k < B) (v : Bool) :
    writeTapeBit (List.ofFn g) k v = List.ofFn (Function.update g ⟨k, hk⟩ v) := by
  rw [writeTapeBit_eq_set _ _ _ (by simpa using hk)]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn, Function.update_apply]
    by_cases hik : k = i
    · subst hik; simp
    · have hne : (⟨i, by simpa using h2⟩ : Fin B) ≠ ⟨k, hk⟩ := by
        intro he; exact hik (congrArg Fin.val he).symm
      simp [hik, hne]

theorem readTapeBit_ofFn {B : ℕ} (g : Fin B → Bool) (k : ℕ) (hk : k < B) :
    readTapeBit (List.ofFn g) k = g ⟨k, hk⟩ := by
  rw [readTapeBit, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]

theorem maskOf_write (B : ℕ) (S : List ℕ) (d : ℕ) (hd : d < B) :
    writeTapeBit (maskOf B S) d true = maskOf B (d :: S) := by
  unfold maskOf
  rw [writeTapeBit_ofFn _ d hd]
  congr 1
  funext i
  rw [Function.update_apply]
  by_cases hi : i.val = d
  · have : i = ⟨d, hd⟩ := Fin.ext hi
    simp [this]
  · have : i ≠ ⟨d, hd⟩ := fun he => hi (congrArg Fin.val he)
    simp [this, hi]

/-- Positions below `k` still carry `g`; positions at or above `k` are already zero. -/
def zeroed {B : ℕ} (g : Fin B → Bool) (k : ℕ) : Fin B → Bool := fun i => if i.val < k then g i else false
theorem zeroed_top {B : ℕ} (g : Fin B → Bool) : zeroed g B = g := by
  funext i; simp [zeroed, i.isLt]
theorem zeroed_zero {B : ℕ} (g : Fin B → Bool) : List.ofFn (zeroed g 0) = List.replicate B false := by
  have h : zeroed g 0 = fun _ => false := by funext i; simp [zeroed]
  rw [h, List.ofFn_const]
theorem zeroed_write {B : ℕ} (g : Fin B → Bool) (k : ℕ) (hk : k < B) :
    writeTapeBit (List.ofFn (zeroed g (k+1))) k false = List.ofFn (zeroed g k) := by
  rw [writeTapeBit_ofFn _ k hk]
  congr 1
  funext i
  rw [Function.update_apply]
  by_cases hi : i.val = k
  · have : i = ⟨k, hk⟩ := Fin.ext hi
    simp [this, zeroed]
  · have : i ≠ ⟨k, hk⟩ := fun he => hi (congrArg Fin.val he)
    simp only [this, ↓reduceIte, zeroed]
    have : (i.val < k+1) ↔ (i.val < k) := by omega
    simp [this]

/-- The first `k` cells of a row, read in order. -/
def copied (L : List Bool) (k : ℕ) : List Bool := (List.range k).map (fun i => readTapeBit L i)
theorem copied_zero (L : List Bool) : copied L 0 = [] := by simp [copied]
theorem copied_succ (L : List Bool) (k : ℕ) : copied L (k+1) = copied L k ++ [readTapeBit L k] := by
  simp [copied, List.range_succ]
theorem copied_full (L : List Bool) (B : ℕ) (hL : L.length = B) : copied L B = L := by
  apply List.ext_getElem
  · simp [copied, hL]
  · intro i h1 h2
    simp [copied, readTapeBit, List.getElem?_eq_getElem h2]

theorem count_write (c : ℕ) : writeTapeBit (List.replicate c true) c true = List.replicate (c+1) true := by
  rw [List.replicate_succ']
  have h := Streaming.write_append (List.replicate c true) true
  rwa [List.length_replicate] at h

end NearCubicWires.ExtIncidence
