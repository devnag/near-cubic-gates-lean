import SourceAdapters.RAMTrace.Row
import Mathlib.Data.BitVec

/-!
# `lem:trace-step` (iii): the semantics of the result bus, the registers and the program counter

Word-level facts used in both directions of `lem:trace-step`:
- `cmpWord_getLsbD`: the bits of `cmp(X, Y)` are `CMP_0 = bo_w + gt`, `CMP_j = gt` ((T6));
- `regBit_rowSucc`, `regFlag_rowSucc`: (T7) — a register written by `I` takes the result `(ZF, Z)`, the others keep
  their value;
- `pcSem`, `rowSucc_pc_bit`, `evalB_pcTerm_self`: (T8) — the next program counter.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable {M : Ram}

/-! ## `cmp` -/

/-- The comparison flag `gt = [X > Y]` ((T4)). -/
def gtBit {w : ℕ} (X Y : BitVec w) : Bool := (!decide (X.toNat < Y.toNat)) && decide (X ≠ Y)

theorem cmpWord_getLsbD {w : ℕ} (hw : 1 ≤ w) (X Y : BitVec w) (j : ℕ) (hj : j < w) :
    (cmpWord X Y).getLsbD j =
      if j = 0 then Bool.xor (decide (X.toNat < Y.toNat)) (gtBit X Y) else gtBit X Y := by
  unfold cmpWord gtBit
  by_cases hlt : X.toNat < Y.toNat
  · have hne : X ≠ Y := by rintro rfl; omega
    simp only [hlt, if_true, decide_true, Bool.not_true, Bool.false_and, Bool.xor_false]
    rw [show (1 : BitVec w) = 1#w from rfl, getLsbD_one]
    by_cases hj0 : j = 0
    · simp [hj0]; omega
    · simp [hj0]
  · by_cases heq : X = Y
    · subst heq
      simp
    · simp only [hlt, if_false, heq, decide_false, Bool.not_false, Bool.true_and, decide_true,
        Bool.false_xor, ne_eq, not_false_eq_true]
      rw [show (-1 : BitVec w) = -(1#w) from rfl, neg_one_eq_allOnes, getLsbD_allOnes]
      split_ifs <;> simp [hj]

/-- The canonical final borrow and comparison flag, in the form the canonical row stores them. -/
theorem canon_bo_gt {w : ℕ} (hw : 1 ≤ w) (X Y : BitVec w) :
    (!carry (w - 1 + 1) X (~~~Y) true) = decide (X.toNat < Y.toNat) ∧
      (carry (w - 1 + 1) X (~~~Y) true && prefixOr (X - Y).getLsbD (w - 1)) = gtBit X Y := by
  have hb := final_borrow X Y hw
  refine ⟨hb, ?_⟩
  have hc : carry (w - 1 + 1) X (~~~Y) true = !decide (X.toNat < Y.toNat) := by
    rw [← hb, Bool.not_not]
  rw [hc, prefixOr_ne_zero _ hw, gtBit]
  congr 1
  have : X - Y = 0 ↔ X = Y := sub_eq_zero
  simp only [ne_eq, decide_not, this]

/-! ## Registers (T7) -/

theorem regBit_setNext (S : M.Config) (i : Fin M.k) (val : Option (BitVec M.w)) (r j : ℕ) :
    regBit (S.setNext i val) r j = if i.val = r then (if r < M.k then (val.getD 0).getLsbD j else false)
      else regBit S r j := by
  unfold regBit Ram.Config.setNext
  by_cases hr : r < M.k
  · simp only [hr, dite_true, if_true]
    by_cases hri : i.val = r
    · subst hri; simp
    · have : (⟨r, hr⟩ : Fin M.k) ≠ i := fun h => hri (by rw [← h])
      simp [Function.update_of_ne this, hri]
  · simp [hr]

theorem regFlag_setNext (S : M.Config) (i : Fin M.k) (val : Option (BitVec M.w)) (r : ℕ) :
    regFlag (S.setNext i val) r = if i.val = r then (if r < M.k then val.isNone else false)
      else regFlag S r := by
  unfold regFlag Ram.Config.setNext
  by_cases hr : r < M.k
  · simp only [hr, dite_true, if_true]
    by_cases hri : i.val = r
    · subst hri; simp
    · have : (⟨r, hr⟩ : Fin M.k) ≠ i := fun h => hri (by rw [← h])
      simp [Function.update_of_ne this, hri]
  · simp [hr]

/-! ## Program counter (T8) -/

/-- Bit `j` of the next program counter contributed by `I` at position `pcv`, with `oz = [X ≠ Y]` (T8). -/
def pcSem (pcv : ℕ) (I : Instr M.w M.k M.ops) (j : ℕ) (oz : Bool) : Bool :=
  match I with
  | .out _ => pcv.testBit j
  | .jmp c => c.testBit j
  | .je _ c => if oz then (pcv + 1).testBit j else c.testBit j
  | .jne _ c => if oz then c.testBit j else (pcv + 1).testBit j
  | _ => (pcv + 1).testBit j

theorem evalB_pcTerm_self (v : TVar → Bool) (pcv : ℕ) (I : Instr M.w M.k M.ops) (j : ℕ)
    (he : v (.inl (.e pcv)) = true) :
    (pcTerm M pcv I j).evalB v = pcSem pcv I j (v (.inl (.OZ (M.w - 1)))) := by
  cases I <;> simp only [pcTerm, pcSem, evalB_mul, evalB_add, evalB_var, evalB_bit, he, Bool.true_and] <;>
    cases v (.inl (.OZ (M.w - 1))) <;> simp

theorem rowSucc_pc_bit (S : M.Config) (mv : BitVec M.w) (rd : Option (BitVec M.w)) (I : Instr M.w M.k M.ops)
    (pcv : ℕ) (hS : S.pc = BitVec.ofNat M.w pcv) (hw : 1 ≤ M.w) (j : ℕ) (hj : j < M.w) :
    (rowSucc S mv rd I).pc.getLsbD j =
      pcSem pcv I j (prefixOr (xWord S I - yWord S I).getLsbD (M.w - 1)) := by
  have hnext : (S.pc + 1#M.w).getLsbD j = (pcv + 1).testBit j := by
    rw [hS, BitVec.ofNat_add_ofNat,
      BitVec.getLsbD_ofNat]
    simp [hj]
  have hjump : ∀ c : ℕ, (BitVec.ofNat M.w c).getLsbD j = c.testBit j := by
    intro c; rw [BitVec.getLsbD_ofNat]; simp [hj]
  cases I with
  | je i c =>
    simp only [rowSucc, pcSem, xWord, yWord, prefixOr_ne_zero _ hw]
    by_cases h0 : S.val (.reg i) = 0#M.w
    · simp [h0, Ram.Config.jump, hjump]
    · simp [h0, Ram.Config.next, hnext]
  | jne i c =>
    simp only [rowSucc, pcSem, xWord, yWord, prefixOr_ne_zero _ hw]
    by_cases h0 : S.val (.reg i) = 0#M.w
    · simp [h0, Ram.Config.next, hnext]
    · simp [h0, Ram.Config.jump, hjump]
  | jmp c => simp [rowSucc, pcSem, Ram.Config.jump, hjump]
  | out b =>
    simp only [rowSucc, pcSem, hS, BitVec.getLsbD_ofNat]
    simp [hj]
  | nop => simp [rowSucc, pcSem, Ram.Config.next, hnext]
  | pload => simp [rowSucc, pcSem, Ram.Config.next, hnext]
  | readA => simp [rowSucc, pcSem, Ram.Config.setNext, hnext]
  | readB => simp [rowSucc, pcSem, Ram.Config.setNext, hnext]
  | load => simp [rowSucc, pcSem, Ram.Config.setNext, hnext]
  | store => simp [rowSucc, pcSem, Ram.Config.next, hnext]
  | iseof => simp [rowSucc, pcSem, Ram.Config.setNext, hnext]
  | arith => simp [rowSucc, pcSem, Ram.Config.setNext, hnext]

variable (kind : Fin M.ops → AluOp) (halu : ∀ op, M.alu op = (kind op).fn)
include halu

/-- (T7) at the word level: a register written by `I` holds the result word, the others keep their bits. -/
theorem regBit_rowSucc (S : M.Config) (mv : BitVec M.w) (rd : Option (BitVec M.w)) (I : Instr M.w M.k M.ops)
    (r j : ℕ) (hr : r < M.k) :
    regBit (rowSucc S mv rd I) r j =
      if writes r I then (zWord kind S mv rd I).getLsbD j else regBit S r j := by
  cases I with
  | readA i => simp [rowSucc, writes, zWord, regBit_setNext, hr]
  | readB i => simp [rowSucc, writes, zWord, regBit_setNext, hr]
  | load i j' => simp [rowSucc, writes, zWord, regBit_setNext, hr]
  | iseof i j' =>
    simp only [rowSucc, writes, zWord, regBit_setNext, hr, if_true, Option.getD_some]
    by_cases hri : i.val = r
    · simp only [hri, if_true, decide_true]
      cases hj : S.regs j' <;> simp
    · simp [hri]
  | arith op i x y => simp [rowSucc, writes, zWord, regBit_setNext, hr, halu]
  | je i c =>
    simp only [rowSucc, writes, Bool.false_eq_true, if_false]
    split_ifs <;> rfl
  | jne i c =>
    simp only [rowSucc, writes, Bool.false_eq_true, if_false]
    split_ifs <;> rfl
  | nop => rfl
  | pload => rfl
  | store => rfl
  | out => rfl
  | jmp => rfl

omit halu in
/-- (T7) for the `#` flags. -/
theorem regFlag_rowSucc (S : M.Config) (mv : BitVec M.w) (rd : Option (BitVec M.w)) (I : Instr M.w M.k M.ops)
    (r : ℕ) (hr : r < M.k) :
    regFlag (rowSucc S mv rd I) r = if writes r I then zfBit rd I else regFlag S r := by
  cases I with
  | readA i => simp [rowSucc, writes, zfBit, regFlag_setNext, hr]
  | readB i => simp [rowSucc, writes, zfBit, regFlag_setNext, hr]
  | load i j' => simp [rowSucc, writes, zfBit, regFlag_setNext, hr]
  | iseof i j' => simp [rowSucc, writes, zfBit, regFlag_setNext, hr]
  | arith op i x y => simp [rowSucc, writes, zfBit, regFlag_setNext, hr]
  | je i c =>
    simp only [rowSucc, writes, Bool.false_eq_true, if_false]
    split_ifs <;> rfl
  | jne i c =>
    simp only [rowSucc, writes, Bool.false_eq_true, if_false]
    split_ifs <;> rfl
  | nop => rfl
  | pload => rfl
  | store => rfl
  | out => rfl
  | jmp => rfl

end NearCubicGates.Adapters.RAMTrace
