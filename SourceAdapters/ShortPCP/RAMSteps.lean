import SourceAdapters.ShortPCP.RAMCode

/-!
# Executing `M_n`: registers, arithmetic unit, memory layout, frames (P02 infrastructure)

Paper context: proof of `lem:tm-ram`, “Layout”. Memory cell `2 k_V j + i` holds cell `j` of tape `i`;
symbols are small integers and blank is zero. The framed tapes of “The exact Lean interface” in
`app:short-pcp-proof` use `fr(b_1⋯b_j) = 1b_1⋯1b_j0`, followed by blank zeros.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-! ## Distinct registers -/

section Regs
variable {V : Verifier}

@[simp] theorem rCnt_val : (rCnt : Fin (regCount V)).val = 0 := rfl
@[simp] theorem rTmp_val : (rTmp : Fin (regCount V)).val = 1 := rfl
@[simp] theorem rVd_val : (rVd : Fin (regCount V)).val = 2 := rfl
@[simp] theorem rP_val : (rP : Fin (regCount V)).val = 3 := rfl
@[simp] theorem rMask_val : (rMask : Fin (regCount V)).val = 4 := rfl
@[simp] theorem rWord_val : (rWord : Fin (regCount V)).val = 5 := rfl
@[simp] theorem rA_val : (rA : Fin (regCount V)).val = 6 := rfl
@[simp] theorem rSr_val : (rSr : Fin (regCount V)).val = 7 := rfl
@[simp] theorem rIdx_val : (rIdx : Fin (regCount V)).val = 8 := rfl
@[simp] theorem rH_val (i : Fin V.tapeCount) : (rH i).val = 9 + i.val := rfl
@[simp] theorem rS_val (i : Fin V.tapeCount) : (rS i).val = 9 + V.tapeCount + i.val := rfl

/-- Registers are equal iff their numbers are (used by `simp` to decide `Function.update` lookups). -/
theorem reg_eq_iff (a b : Fin (regCount V)) : a = b ↔ a.val = b.val := Fin.ext_iff

theorem rH_inj {i j : Fin V.tapeCount} : rH i = rH j ↔ i = j := by
  rw [reg_eq_iff, Fin.ext_iff]; simp

theorem rS_inj {i j : Fin V.tapeCount} : rS i = rS j ↔ i = j := by
  rw [reg_eq_iff, Fin.ext_iff]; simp

end Regs

/-! ## Arithmetic unit -/

@[simp] theorem mnAlu_add (w : ℕ) (x y : BitVec w) : mnAlu w 0 x y = x + y := rfl
@[simp] theorem mnAlu_sub (w : ℕ) (x y : BitVec w) : mnAlu w 1 x y = x - y := rfl
@[simp] theorem mnAlu_and (w : ℕ) (x y : BitVec w) : mnAlu w 2 x y = x &&& y := rfl
@[simp] theorem mnAlu_cmp (w : ℕ) (x y : BitVec w) : mnAlu w 3 x y = cmpFn x y := rfl

theorem toNat_ofNat_lt {w a : ℕ} (h : a < 2 ^ w) : (BitVec.ofNat w a).toNat = a := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem cmpFn_lt {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : a < b) :
    cmpFn (BitVec.ofNat w a) (BitVec.ofNat w b) = 1 := by
  unfold cmpFn; rw [toNat_ofNat_lt ha, toNat_ofNat_lt hb, if_pos h]

theorem cmpFn_eq {w a : ℕ} : cmpFn (BitVec.ofNat w a) (BitVec.ofNat w a) = 0 := by
  unfold cmpFn; simp

theorem cmpFn_gt {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : b < a) :
    cmpFn (BitVec.ofNat w a) (BitVec.ofNat w b) = -1 := by
  unfold cmpFn
  rw [toNat_ofNat_lt ha, toNat_ofNat_lt hb, if_neg (by omega), if_neg]
  rw [ofNat_inj ha hb]; omega

/-- `cmp(0, x)` is `1` iff `x ≠ 0`. -/
theorem cmpFn_zero_left {w : ℕ} (x : BitVec w) : cmpFn 0 x = if x = 0 then 0 else 1 := by
  unfold cmpFn
  by_cases hx : x = 0
  · subst hx; simp
  · have : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
      · exact h
    have h0 : (0 : BitVec w).toNat < x.toNat := by simpa using this
    rw [if_pos h0, if_neg hx]

theorem ofNat_ne_zero {w a : ℕ} (ha : a < 2 ^ w) (h0 : a ≠ 0) : BitVec.ofNat w a ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [toNat_ofNat_lt ha] at this
  simp at this; exact h0 this

/-- Bit `j` of a word is set iff its `and` with `2^j` is nonzero. -/
theorem and_two_pow_ne_zero {w : ℕ} (x : BitVec w) (j : ℕ) (hj : j < w) :
    (x &&& BitVec.ofNat w (2 ^ j)) ≠ 0 ↔ x.getLsbD j = true := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases hij : j = i
    · subst hij; simp_all
    · simp [hij]
  · intro hb h
    have := congrArg (fun v => BitVec.getLsbD v j) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow] at this
    simp_all [BitVec.getLsbD_eq_getElem]

theorem ofNat_two_pow_self (w : ℕ) : BitVec.ofNat w (2 ^ w) = 0 := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The memory layout -/

section Layout
variable (V : Verifier) (w : ℕ)

/-- The memory holding tapes `τ`: cell `j` of tape `i` at address `stride·j + i`, as the word `0` or `1`. -/
def memRep (τ : Fin V.tapeCount → ℕ → Bool) : BitVec w → BitVec w := fun addr =>
  if h : addr.toNat % stride V < V.tapeCount then
    (if τ ⟨addr.toNat % stride V, h⟩ (addr.toNat / stride V) then 1 else 0)
  else 0

/-- The all-blank tapes are the zero memory. -/
theorem memRep_blank : memRep V w (fun _ _ => false) = 0 := by
  funext addr; simp [memRep]

theorem addr_decomp (i : Fin V.tapeCount) (j : ℕ) :
    (stride V * j + i.val) % stride V = i.val ∧ (stride V * j + i.val) / stride V = j := by
  have hs : i.val < stride V := by unfold stride; omega
  constructor
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]

/-- Reading cell `j` of tape `i`. -/
theorem memRep_read (τ : Fin V.tapeCount → ℕ → Bool) (i : Fin V.tapeCount) (j : ℕ)
    (hj : stride V * j + i.val < 2 ^ w) :
    memRep V w τ (BitVec.ofNat w (stride V * j + i.val)) = if τ i j then 1 else 0 := by
  obtain ⟨h1, h2⟩ := addr_decomp V i j
  unfold memRep
  rw [toNat_ofNat_lt hj]
  rw [dif_pos (by rw [h1]; exact i.isLt)]
  have key : ∀ (k : ℕ) (hk : k < V.tapeCount), k = i.val → τ ⟨k, hk⟩ = τ i := by
    rintro k hk rfl; rfl
  rw [key _ _ h1, h2]

/-- Writing cell `j` of tape `i`. -/
theorem memRep_write (τ : Fin V.tapeCount → ℕ → Bool) (i : Fin V.tapeCount) (j : ℕ) (b : Bool)
    (hj : stride V * j + i.val < 2 ^ w) :
    Function.update (memRep V w τ) (BitVec.ofNat w (stride V * j + i.val)) (if b then 1 else 0) =
      memRep V w (Function.update τ i (Function.update (τ i) j b)) := by
  obtain ⟨h1, h2⟩ := addr_decomp V i j
  funext addr
  by_cases ha : addr = BitVec.ofNat w (stride V * j + i.val)
  · subst ha
    rw [Function.update_self, memRep_read V w _ i j hj]
    simp
  · rw [Function.update_of_ne ha]
    unfold memRep
    by_cases hlt : addr.toNat % stride V < V.tapeCount
    · rw [dif_pos hlt, dif_pos hlt]
      have hne : ¬ (⟨addr.toNat % stride V, hlt⟩ = i ∧ addr.toNat / stride V = j) := by
        rintro ⟨hi, hjj⟩
        apply ha
        apply BitVec.eq_of_toNat_eq
        rw [toNat_ofNat_lt hj, ← hjj, ← (congrArg Fin.val hi : _)]
        simp only
        exact (Nat.div_add_mod addr.toNat (stride V)).symm
      have key : Function.update τ i (Function.update (τ i) j b) ⟨addr.toNat % stride V, hlt⟩
          (addr.toNat / stride V) = τ ⟨addr.toNat % stride V, hlt⟩ (addr.toNat / stride V) := by
        by_cases hi : (⟨addr.toNat % stride V, hlt⟩ : Fin V.tapeCount) = i
        · have hjj : addr.toNat / stride V ≠ j := fun h => hne ⟨hi, h⟩
          rw [hi, Function.update_self, Function.update_of_ne hjj]
        · rw [Function.update_of_ne hi]
      rw [key]
    · rw [dif_neg hlt, dif_neg hlt]

end Layout

/-! ## Frames -/

/-- `fr(b_0⋯b_{p−1})` followed by blanks, as a function of the cell: cells `2q` hold `1`, cells `2q + 1` hold `b_q`
(`q < p`), the rest blank. -/
def frameFn (p : ℕ) (b : ℕ → Bool) (j : ℕ) : Bool := decide (j < 2 * p) && (decide (j % 2 = 0) || b (j / 2))

theorem frameFn_zero (b : ℕ → Bool) : frameFn 0 b = fun _ => false := by
  funext j; simp [frameFn]

theorem frameFn_succ (p : ℕ) (b : ℕ → Bool) :
    frameFn (p + 1) b = Function.update (Function.update (frameFn p b) (2 * p) true) (2 * p + 1) (b p) := by
  funext j
  simp only [Function.update_apply, frameFn]
  by_cases h1 : j = 2 * p + 1
  · subst h1
    have e1 : (2 * p + 1) % 2 = 1 := by omega
    have e2 : (2 * p + 1) / 2 = p := by omega
    simp [e1, e2]; omega
  · by_cases h2 : j = 2 * p
    · subst h2; simp
    · rw [if_neg h1, if_neg h2]
      congr 1
      simp only [decide_eq_decide]; omega

/-- The frame of a list, read cell by cell (`RepairOrdinary.frame`, `lem:tm-ram` and its proof). -/
theorem frame_getD (l : List Bool) (j : ℕ) :
    (frame l).getD j false = frameFn l.length (fun q => l.getD q false) j := by
  induction l generalizing j with
  | nil => cases j <;> simp [frame, frameFn]
  | cons b l ih =>
    rcases j with _ | _ | j
    · simp [frame, frameFn]
    · simp [frame, frameFn]; omega
    · simp only [frame, List.getD_cons_succ]
      rw [ih j]
      simp only [frameFn, List.length_cons]
      have h1 : (j + 1 + 1) % 2 = j % 2 := by omega
      have h2 : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
      rw [h1, h2, List.getD_cons_succ]
      congr 1
      simp only [decide_eq_decide]; omega

/-- The tape list `writeTapeBit` read cell by cell. -/
theorem writeTapeBit_getD : ∀ (l : List Bool) (p : ℕ) (b : Bool) (j : ℕ),
    (writeTapeBit l p b).getD j false = if j = p then b else l.getD j false
  | [], 0, b, j => by cases j <;> simp [writeTapeBit]
  | [], p + 1, b, j => by
    cases j with
    | zero => simp [writeTapeBit]
    | succ j => simp only [writeTapeBit, List.getD_cons_succ]; rw [writeTapeBit_getD [] p b j]; simp
  | _ :: tail, 0, b, j => by cases j <;> simp [writeTapeBit]
  | old :: tail, p + 1, b, j => by
    cases j with
    | zero => simp [writeTapeBit]
    | succ j => simp only [writeTapeBit, List.getD_cons_succ]; rw [writeTapeBit_getD tail p b j]; simp

end NearCubicGates.Adapters.ShortPCP
