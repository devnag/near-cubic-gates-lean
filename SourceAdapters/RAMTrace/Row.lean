import SourceAdapters.RAMTrace.Gadgets

/-!
# `lem:trace-step`: one time row — decoding, the step, and the canonical row

`app:event-trace` `lem:trace-step`. This module fixes the semantic objects of a time row and evaluates the linear forms `e(Q)`:
- `decCur v`, `decNxt v`: the configurations encoded by the `cur` and `nxt` blocks (`fl_r = 1` is `#`);
- `xWord`, `yWord`, `xfBit` (`app:event-trace` operand sources), `zWord`, `zfBit` ((T6)), `rowSucc` (the successor of `S`
  under `I` with the row's access: `load` reads `mv`, a read receives `rd`, `lem:trace-step` (iii));
- `canon S I mv rd ts cA cB`: the canonical row of `lem:trace-step` (iii)'s existence half — `cur = S`, `nxt =
  rowSucc …`, the canonical arithmetic and counter auxiliaries (the existence part of `lem:trace-gadgets`), the record of (T9);
- `evalB_eSet`, `evalB_eDot`, `evalB_pcSum`: under one-hot `e` (`lem:trace-step` (ii)) every linear form `e(Q)` is
  `[I_pc ∈ Q]`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMTrace

open NearCubicGates.Adapters.ACSP Expr BitVec

variable {M : Ram}

/-! ## Configurations of a row -/

/-- The register `#` flag (`false` outside the register file). -/
def regFlag (S : M.Config) (r : ℕ) : Bool := if h : r < M.k then (S.regs ⟨r, h⟩).isNone else false

/-- Bit `j` of the word of register `r` (`#` reads as zero). -/
def regBit (S : M.Config) (r j : ℕ) : Bool :=
  if h : r < M.k then ((S.regs ⟨r, h⟩).getD 0).getLsbD j else false

/-- The configuration encoded by the `cur` block (`lem:trace-step` (i)). -/
def decCur (v : TVar → Bool) : M.Config where
  pc := bvOf M.w fun j => v (.inl (.pc j))
  regs r := if v (.inl (.fl r.val)) then none else some (bvOf M.w fun j => v (.inl (.rg r.val j)))

/-- The configuration encoded by the `nxt` block. -/
def decNxt (v : TVar → Bool) : M.Config where
  pc := bvOf M.w fun j => v (.inl (.npc j))
  regs r := if v (.inl (.nfl r.val)) then none else some (bvOf M.w fun j => v (.inl (.nrg r.val j)))

/-! ## Operands, results, successor -/

/-- The word on the bus `X` (`app:event-trace` operand sources; `#` reads as zero). -/
def xWord (S : M.Config) : Instr M.w M.k M.ops → BitVec M.w
  | .arith _ _ x _ => S.val x
  | .je i _ => S.val (.reg i)
  | .jne i _ => S.val (.reg i)
  | .load i _ => S.val (.reg i)
  | .store i _ => S.val (.reg i)
  | _ => 0

/-- The word on the bus `Y`. -/
def yWord (S : M.Config) : Instr M.w M.k M.ops → BitVec M.w
  | .arith _ _ _ y => S.val y
  | .store _ x => S.val x
  | _ => 0

/-- The flag bus `XF` (`iseof i j`: register `j` holds `#`). -/
def xfBit (S : M.Config) : Instr M.w M.k M.ops → Bool
  | .iseof _ j => (S.regs j).isNone
  | _ => false

/-- The result word `Z` of (T6). -/
def zWord (kind : Fin M.ops → AluOp) (S : M.Config) (mv : BitVec M.w) (rd : Option (BitVec M.w)) :
    Instr M.w M.k M.ops → BitVec M.w
  | .arith op _ x y => (kind op).fn (S.val x) (S.val y)
  | .load _ _ => mv
  | .readA _ => rd.getD 0
  | .readB _ => rd.getD 0
  | .iseof _ j => if (S.regs j).isNone then 1 else 0
  | _ => 0

/-- The result flag `ZF` of (T6). -/
def zfBit (rd : Option (BitVec M.w)) : Instr M.w M.k M.ops → Bool
  | .readA _ => rd.isNone
  | .readB _ => rd.isNone
  | _ => false

/-- **The successor of `S` under `I` with the row's access** (`lem:trace-step` (iii)): `load` reads `mv`, `readA`,
`readB` receive `rd`; `out` keeps `S` ((T7)–(T8) for `I = out`). -/
def rowSucc (S : M.Config) (mv : BitVec M.w) (rd : Option (BitVec M.w)) :
    Instr M.w M.k M.ops → M.Config
  | .nop => S.next
  | .pload _ _ => S.next
  | .readA i => S.setNext i rd
  | .readB i => S.setNext i rd
  | .load _ j => S.setNext j (some mv)
  | .store _ _ => S.next
  | .iseof i j => S.setNext i (some (if S.regs j = none then 1 else 0))
  | .out _ => S
  | .arith op i x y => S.setNext i (some (M.alu op (S.val x) (S.val y)))
  | .je i c => if S.val (.reg i) = 0 then S.jump c else S.next
  | .jne i c => if S.val (.reg i) ≠ 0 then S.jump c else S.next
  | .jmp c => S.jump c

/-! ## The canonical row -/

/-- **The canonical row** (`lem:trace-step` (iii), existence; the existence part of `lem:trace-gadgets`): `cur = S`, decode of `pc`, operand buses,
canonical carries/borrows/prefix-ors, the result, the access channels `mv`, `rd`, `nxt = rowSucc S mv rd I`, the
counters `ts`, `cA`, `cB` with canonical incrementer carries, and the record of (T9). -/
def canon (kind : Fin M.ops → AluOp) (τ : ℕ) (S : M.Config) (I : Instr M.w M.k M.ops) (mv : BitVec M.w)
    (rd : Option (BitVec M.w)) (ts cA : BitVec τ) (cB : BitVec ((dims M τ).β + 1)) : TVar → Bool :=
  let X := xWord S I
  let Y := yWord S I
  let aA := isRdA I && !rd.isNone
  let aB := isRdB I && !rd.isNone
  let ls := Bool.xor (isLd I) (isSt I)
  let S' := rowSucc S mv rd I
  fun
  | .inl (.pc j) => S.pc.getLsbD j
  | .inl (.fl r) => regFlag S r
  | .inl (.rg r j) => regBit S r j
  | .inl (.e p) => decide (p = S.pc.toNat)
  | .inl (.o p) => decide (S.pc.toNat ≤ p)
  | .inl (.X j) => X.getLsbD j
  | .inl .XF => xfBit S I
  | .inl (.Y j) => Y.getLsbD j
  | .inl (.AD j) => (X + Y).getLsbD j
  | .inl (.CA j) => carry (j + 1) X Y false
  | .inl (.SB j) => (X - Y).getLsbD j
  | .inl (.BO j) => !carry (j + 1) X (~~~Y) true
  | .inl (.AN j) => (X &&& Y).getLsbD j
  | .inl (.OZ j) => prefixOr (X - Y).getLsbD j
  | .inl .GT => carry (M.w - 1 + 1) X (~~~Y) true && prefixOr (X - Y).getLsbD (M.w - 1)
  | .inl (.Z j) => (zWord kind S mv rd I).getLsbD j
  | .inl .ZF => zfBit rd I
  | .inl (.RV j) => (rd.getD 0).getLsbD j
  | .inl .RF => rd.isNone
  | .inl (.MV j) => mv.getLsbD j
  | .inl (.TC j) => carry (j + 1) ts 0#τ true
  | .inl (.cA j) => cA.getLsbD j
  | .inl (.cB j) => cB.getLsbD j
  | .inl (.AC j) => carry (j + 1) cA 0#τ aA
  | .inl (.BC j) => carry (j + 1) cB 0#((dims M τ).β + 1) aB
  | .inl .aA => aA
  | .inl .aB => aB
  | .inl (.npc j) => S'.pc.getLsbD j
  | .inl (.nfl r) => regFlag S' r
  | .inl (.nrg r j) => regBit S' r j
  | .inl (.ncA j) => (cA + 0#τ + setWidth τ (ofBool aA)).getLsbD j
  | .inl (.ncB j) => (cB + 0#((dims M τ).β + 1) + setWidth ((dims M τ).β + 1) (ofBool aB)).getLsbD j
  | .inl (.TSN j) => (ts + 0#τ + setWidth τ (ofBool true)).getLsbD j
  | .inr (.act, _) => Bool.xor ls aA
  | .inr (.rgn, _) => aA
  | .inr (.ad, j) => Bool.xor (ls && X.getLsbD j) (if j < τ then aA && cA.getLsbD j else false)
  | .inr (.ph, _) => true
  | .inr (.ts, j) => ts.getLsbD j
  | .inr (.va, j) => Bool.xor (ls && mv.getLsbD j) (aA && (rd.getD 0).getLsbD j)
  | .inr (.st, _) => isSt I

/-! ## The linear forms `e(Q)` under one-hot decoding -/

section OneHot

variable (v : TVar → Bool) (pcv : ℕ) (hpc : pcv < M.code.length)
  (hE : ∀ p < M.code.length, v (.inl (.e p)) = decide (p = pcv))
include hpc hE

theorem evalB_eSet (Q : Instr M.w M.k M.ops → Bool) : (eSet M Q).evalB v = Q (M.code[pcv]) := by
  unfold eSet
  rw [evalB_sumCode_single _ v pcv M.code 0 (Nat.zero_le _) (by simpa using hpc)]
  · simp only [Nat.sub_zero]
    split_ifs with h
    · simp [hE pcv hpc, h]
    · simp [h]
  · intro p I _ hp hne
    split_ifs
    · simp [hE p (by simpa using hp), hne]
    · rfl

theorem evalB_eDot (s : Instr M.w M.k M.ops → Expr TVar) :
    (eDot M s).evalB v = (s (M.code[pcv])).evalB v := by
  unfold eDot
  rw [evalB_sumCode_single _ v pcv M.code 0 (Nat.zero_le _) (by simpa using hpc)]
  · simp [hE pcv hpc]
  · intro p I _ hp hne
    simp [hE p (by simpa using hp), hne]

omit hpc in
theorem evalB_pcTerm_of_ne (p : ℕ) (hp : p < M.code.length) (hne : p ≠ pcv) (I : Instr M.w M.k M.ops)
    (j : ℕ) : (pcTerm M p I j).evalB v = false := by
  have he : v (.inl (.e p)) = false := by simp [hE p hp, hne]
  cases I <;> simp [pcTerm, he]

theorem evalB_pcSum (j : ℕ) :
    (sumCode (fun p I => pcTerm M p I j) 0 M.code).evalB v = (pcTerm M pcv (M.code[pcv]) j).evalB v := by
  rw [evalB_sumCode_single _ v pcv M.code 0 (Nat.zero_le _) (by simpa using hpc)]
  · simp
  · intro p I _ hp hne
    exact evalB_pcTerm_of_ne v pcv hE p (by simpa using hp) hne I j

theorem evalB_decPcSum (j : ℕ) :
    (sumCode (fun p (_ : Instr M.w M.k M.ops) => if p.testBit j then tv (.e p) else zero) 0 M.code).evalB v =
      pcv.testBit j := by
  rw [evalB_sumCode_single _ v pcv M.code 0 (Nat.zero_le _) (by simpa using hpc)]
  · split_ifs with h
    · simp [hE pcv hpc, h]
    · simp [h]
  · intro p I _ hp hne
    split_ifs
    · simp [hE p (by simpa using hp), hne]
    · rfl

end OneHot

/-! ## Operands under (T1) -/

section Operands

variable (v : TVar → Bool) (hT1 : ∀ r < M.k, ∀ j < M.w, (v (.inl (.fl r)) && v (.inl (.rg r j))) = false)
include hT1

theorem decCur_val_reg (r : Fin M.k) (j : ℕ) (hj : j < M.w) :
    ((decCur v).val (.reg r)).getLsbD j = v (.inl (.rg r.val j)) := by
  have h := hT1 r.val r.isLt j hj
  simp only [decCur, Ram.Config.val]
  by_cases hf : v (.inl (.fl r.val)) = true
  · rw [hf, Bool.true_and] at h
    simp [hf, h]
  · simp only [Bool.not_eq_true] at hf
    simp [hf, hj]

theorem evalB_opnd (x : Operand M.w M.k) (j : ℕ) (hj : j < M.w) :
    (opnd M x j).evalB v = ((decCur v).val x).getLsbD j := by
  cases x with
  | reg r => simp only [opnd, evalB_var]; exact (decCur_val_reg v hT1 r j hj).symm
  | pc => simp [opnd, decCur, Ram.Config.val, hj]
  | const c => simp [opnd, Ram.Config.val]

theorem evalB_srcX (I : Instr M.w M.k M.ops) (j : ℕ) (hj : j < M.w) :
    (srcX M I j).evalB v = (xWord (decCur v) I).getLsbD j := by
  cases I <;> simp only [srcX, xWord] <;>
    first
    | exact evalB_opnd v hT1 _ j hj
    | exact (decCur_val_reg v hT1 _ j hj).symm
    | simp

theorem evalB_srcY (I : Instr M.w M.k M.ops) (j : ℕ) (hj : j < M.w) :
    (srcY M I j).evalB v = (yWord (decCur v) I).getLsbD j := by
  cases I <;> simp only [srcY, yWord] <;>
    first
    | exact evalB_opnd v hT1 _ j hj
    | simp

omit hT1 in
theorem evalB_srcXF (I : Instr M.w M.k M.ops) : (srcXF M I).evalB v = xfBit (decCur v) I := by
  cases I <;> simp only [srcXF, xfBit, decCur, evalB_var, evalB_zero]
  rename_i j
  by_cases h : v (.inl (.fl j.val)) <;> simp [h]

end Operands

end NearCubicGates.Adapters.RAMTrace
