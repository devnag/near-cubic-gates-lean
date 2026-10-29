import SourceAdapters.ShortPCP.RAMRun
import SourceAdapters.ShortPCP.RAMIdle
import Mathlib.Algebra.BigOperators.Fin

/-!
# The code `C_n` of the random-access machine `M_n` (P02a)

Paper context: proof of `lem:tm-ram`, “Layout”, “Loading the tapes”, “Simulating `V`” and “Counting”.
The current paper uses the following representation, whose exact register assignment is given below.

- Memory cell `2 k_V j + i` holds cell `j` of tape `i`. A head at position zero is recognized by
  `h < 2k_V`, and a left move can be computed without a branch.
- The state of `V` is stored in register `sr`. The interpreter loads the scanned symbols, forms
  `sr·2^{k_V} + Σ_i s_i 2^{k_V−1−i}`, and branches through a chain of comparisons to one leaf per
  (state, scanned symbols) pair.
- The input is unpacked bit by bit, with `n` written into the code, and the first `t` witness bits are
  unpacked during initialization. The simulated tapes receive `fr(x)` and `fr(y)`, as described in
  “The exact Lean interface” in `app:short-pcp-proof`; loading costs `O(n + t + w_n)` RAM steps.
- A read of `#`, a halted rejecting state or a stuck configuration enters the one-instruction loop
  `jmp dead`, which never reaches `out`. The accepting path records a verdict and starts the counted
  idle phase. Every completed block adds its padded length, a multiple of eight, to the counter.

Registers (`9 + 2k_V`): `0` counter, `1` scratch, `2` verdict, `3` position `p`, `4` mask, `5` word, `6` address,
`7` state `sr`, `8` index, `9 + i` head of tape `i`, `9 + k_V + i` scanned symbol of tape `i`. Arithmetic unit
`mnAlu`: `0 = add`, `1 = sub`, `2 = and`, `3 = cmp` (`def:ram`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

variable (V : Verifier)

/-! ## Sizes -/

/-- The number of registers. -/
def regCount : ℕ := 9 + 2 * V.tapeCount

/-- The stride `2 k_V` of the tape layout. -/
def stride : ℕ := 2 * V.tapeCount

/-- The number of (state, scanned symbols) pairs, i.e. of leaves. -/
def leafCount : ℕ := V.stateCount * 2 ^ V.tapeCount

/-- `nop`s that pad a simulation path to a multiple of `8`. -/
def simPad : ℕ := (8 - (11 * V.tapeCount + 2 * leafCount V + 4) % 8) % 8

/-- `nop`s that pad the accepting path to a multiple of `8`. -/
def accPad : ℕ := (8 - (4 * V.tapeCount + 2 * leafCount V + 4) % 8) % 8

/-- Steps of one simulated step of `V`. -/
def simLen : ℕ := 11 * V.tapeCount + 2 * leafCount V + 4 + simPad V

/-- Steps from the interpreter to the idle block on the accepting path. -/
def accLen : ℕ := 4 * V.tapeCount + 2 * leafCount V + 4 + accPad V

/-- The code length of one leaf. -/
def leafLen : ℕ := 2 * leafCount V + 7 * V.tapeCount + 12

/-- Address of the interpreter. -/
def interpAddr : ℕ := 8 * V.tapeCount + 92

/-- Address of the comparison chain. -/
def chainAddr : ℕ := interpAddr V + 4 * V.tapeCount + 1

/-- Address of the first leaf. -/
def leafAddr : ℕ := chainAddr V + 2 * leafCount V + 1

/-- Address of the `jmp dead` loop. -/
def deadAddr : ℕ := leafAddr V + leafCount V * leafLen V

/-- Address of the idle block. -/
def idleAddr : ℕ := deadAddr V + 1

/-- The code length. -/
def codeLen : ℕ := idleAddr V + 17

/-! ## Registers and operands -/

section Regs

variable {V}

def rCnt : Fin (regCount V) := ⟨0, by unfold regCount; omega⟩
def rTmp : Fin (regCount V) := ⟨1, by unfold regCount; omega⟩
def rVd : Fin (regCount V) := ⟨2, by unfold regCount; omega⟩
def rP : Fin (regCount V) := ⟨3, by unfold regCount; omega⟩
def rMask : Fin (regCount V) := ⟨4, by unfold regCount; omega⟩
def rWord : Fin (regCount V) := ⟨5, by unfold regCount; omega⟩
def rA : Fin (regCount V) := ⟨6, by unfold regCount; omega⟩
def rSr : Fin (regCount V) := ⟨7, by unfold regCount; omega⟩
def rIdx : Fin (regCount V) := ⟨8, by unfold regCount; omega⟩
def rH (i : Fin V.tapeCount) : Fin (regCount V) := ⟨9 + i.val, by unfold regCount; omega⟩
def rS (i : Fin V.tapeCount) : Fin (regCount V) := ⟨9 + V.tapeCount + i.val, by unfold regCount; omega⟩

end Regs

/-- An instruction of `M_n`. -/
abbrev MI (w : ℕ) : Type := Instr w (regCount V) 4

/-- A constant operand. -/
def cst {w k : ℕ} (c : ℕ) : Operand w k := .const (BitVec.ofNat w c)

/-! ## Blocks -/

section Blocks

variable (w : ℕ)

/-- The first block (8 steps): `store` to cell `0` (Def. 7.7), six `nop`s, counter `+= 8`. -/
def startBlock : List (MI V w) :=
  [.store rCnt (cst 0)] ++ List.replicate 6 .nop ++ [.arith 0 rCnt (.reg rCnt) (cst 8)]

/-- The unpacking loop at `u` (34 instructions): writes `fr` of the first `N` bits read with `rd` onto the tape whose
base address is in `a`. A pass takes 24 steps (one bit), the exit 8 steps. -/
def unpackBlock (rd : Fin (regCount V) → MI V w) (u N dead : ℕ) : List (MI V w) :=
  [ .arith 3 rTmp (.reg rP) (cst N),
    .je rTmp (u + 28),
    .jne rMask (u + 24),
    rd rWord,
    .iseof rTmp rWord,
    .jne rTmp dead,
    .arith 0 rMask (cst 1) (cst 0),
    .arith 2 rTmp (.reg rWord) (.reg rMask),
    .arith 3 rTmp (cst 0) (.reg rTmp),
    .store rA (cst 1),
    .arith 0 rA (.reg rA) (cst (stride V)),
    .store rA (.reg rTmp),
    .arith 0 rA (.reg rA) (cst (stride V)),
    .arith 0 rMask (.reg rMask) (.reg rMask),
    .arith 0 rP (.reg rP) (cst 1),
    .nop, .nop, .nop, .nop, .nop, .nop, .nop,
    .arith 0 rCnt (.reg rCnt) (cst 24),
    .jmp u,
    .nop, .nop, .nop,
    .jmp (u + 7),
    .nop, .nop, .nop, .nop, .nop,
    .arith 0 rCnt (.reg rCnt) (cst 8) ]

/-- Between the loops (8 steps): `p ← 0`, `mask ← 0`, `a ← 1` (tape 1, cell 0), counter `+= 8`. -/
def setupBlock : List (MI V w) :=
  [.arith 0 rP (cst 0) (cst 0), .arith 0 rMask (cst 0) (cst 0), .arith 0 rA (cst 1) (cst 0)] ++
    List.replicate 4 .nop ++ [.arith 0 rCnt (.reg rCnt) (cst 8)]

/-- Before the simulation (`8(k_V + 1)` steps): heads at cell `0`, `sr ← start`, counter. -/
def simSetupBlock : List (MI V w) :=
  List.ofFn (fun i : Fin V.tapeCount => (.arith 0 (rH i) (cst i.val) (cst 0) : MI V w)) ++
    [.arith 0 rSr (cst V.machine.start.val) (cst 0)] ++ List.replicate (7 * V.tapeCount + 6) .nop ++
    [.arith 0 rCnt (.reg rCnt) (cst (8 * (V.tapeCount + 1)))]

/-- The interpreter header (`4k_V + 1` steps): load the scanned symbols (each `load` followed by its `pload`) and
form the index by Horner's rule. -/
def headerBlock : List (MI V w) :=
  (List.ofFn fun i : Fin V.tapeCount => ([.load (rH i) (rS i), .pload (rH i) (rS i)] : List (MI V w))).flatten ++
    [.arith 0 rIdx (.reg rSr) (cst 0)] ++
    (List.ofFn fun i : Fin V.tapeCount =>
      ([.arith 0 rIdx (.reg rIdx) (.reg rIdx), .arith 0 rIdx (.reg rIdx) (.reg (rS i))] : List (MI V w))).flatten

/-- The comparison chain: entry `m` subtracts `m` from the index and jumps to leaf `m` on zero. -/
def chainBlock : List (MI V w) :=
  (List.ofFn fun m : Fin (leafCount V) =>
    ([.arith 1 rTmp (.reg rIdx) (cst m.val), .je rTmp (leafAddr V + m.val * leafLen V)] : List (MI V w))).flatten ++
    [.jmp (deadAddr V)]

/-- The write of one tape: `store` the symbol at the head, or `nop`. -/
def writeInstr (i : Fin V.tapeCount) : Option Bool → MI V w
  | none => .nop
  | some b => .store (rH i) (cst (if b then 1 else 0))

/-- The move of one tape (6 instructions, straight-line). A left move subtracts `stride·[h ≥ stride]`. -/
def moveInstrs (i : Fin V.tapeCount) : HeadMove → List (MI V w)
  | .right => [.arith 0 (rH i) (.reg (rH i)) (cst (stride V)), .nop, .nop, .nop, .nop, .nop]
  | .stay => [.nop, .nop, .nop, .nop, .nop, .nop]
  | .left =>
    [ .arith 3 rTmp (.reg (rH i)) (cst (stride V)),
      .arith 1 rTmp (.reg rTmp) (cst 1),
      .arith 3 rTmp (cst 0) (.reg rTmp),
      .arith 1 rTmp (cst 0) (.reg rTmp),
      .arith 2 rTmp (.reg rTmp) (cst (stride V)),
      .arith 1 (rH i) (.reg (rH i)) (.reg rTmp) ]

/-- One tape of an action (7 instructions). -/
def tapeSeg (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) : List (MI V w) :=
  writeInstr V w i (a.write i) :: moveInstrs V w i (a.move i)

/-- The leaf of a `V`-step with action `a` (reached after `2(m+1)` chain steps). -/
def actLeaf (m : ℕ) (a : Action V.tapeCount V.stateCount) : List (MI V w) :=
  List.replicate (2 * (leafCount V - 1 - m)) .nop ++ (List.ofFn (tapeSeg V w a)).flatten ++
    [.arith 0 rSr (cst a.nextControl.val) (cst 0)] ++ List.replicate (simPad V) .nop ++
    [.arith 0 rCnt (.reg rCnt) (cst (simLen V)), .jmp (interpAddr V)]

/-- The leaf of a halted accepting state: verdict `1`, counter, jump to the idle block. -/
def accLeaf (m : ℕ) : List (MI V w) :=
  List.replicate (2 * (leafCount V - 1 - m)) .nop ++ [.arith 0 rVd (cst 1) (cst 0)] ++
    List.replicate (accPad V) .nop ++ [.arith 0 rCnt (.reg rCnt) (cst (accLen V)), .jmp (idleAddr V)]

/-- The leaf of a halted rejecting state or a stuck configuration. -/
def deadLeaf : List (MI V w) := [.jmp (deadAddr V)]

/-- Pad a leaf to `leafLen` instructions (the filler is never reached). -/
def padLeaf (l : List (MI V w)) : List (MI V w) := l ++ List.replicate (leafLen V - l.length) .nop

end Blocks

/-! ## Encoding of (state, scanned symbols) -/

/-- The number `Σ_i σ_i 2^{k_V − 1 − i}` of a scanned tuple. -/
def symCode {k : ℕ} (σ : Fin k → Bool) : Fin (2 ^ k) :=
  finFunctionFinEquiv fun i : Fin k => (if σ (Fin.rev i) then 1 else 0 : Fin 2)

/-- The scanned tuple of a number below `2^{k}`. -/
def symDecode {k : ℕ} (c : Fin (2 ^ k)) : Fin k → Bool :=
  fun i => finFunctionFinEquiv.symm c (Fin.rev i) = 1

theorem symDecode_symCode {k : ℕ} (σ : Fin k → Bool) : symDecode (symCode σ) = σ := by
  funext i
  unfold symDecode symCode
  rw [Equiv.symm_apply_apply]
  simp

/-- The leaf index of (state `q`, scanned `σ`): `q·2^{k_V} + symCode σ`. -/
def leafIndex (q : Fin V.stateCount) (σ : Fin V.tapeCount → Bool) : ℕ :=
  q.val * 2 ^ V.tapeCount + (symCode σ).val

theorem leafIndex_lt (q : Fin V.stateCount) (σ : Fin V.tapeCount → Bool) : leafIndex V q σ < leafCount V := by
  unfold leafIndex leafCount
  have h1 := (symCode σ).isLt
  have h2 : q.val + 1 ≤ V.stateCount := q.isLt
  calc q.val * 2 ^ V.tapeCount + (symCode σ).val < q.val * 2 ^ V.tapeCount + 2 ^ V.tapeCount := by omega
    _ = (q.val + 1) * 2 ^ V.tapeCount := by ring
    _ ≤ V.stateCount * 2 ^ V.tapeCount := Nat.mul_le_mul_right _ h2

/-- The state of leaf `m`. -/
def leafState (m : Fin (leafCount V)) : Fin V.stateCount :=
  ⟨m.val / 2 ^ V.tapeCount, by
    have := m.isLt; unfold leafCount at this
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)⟩

/-- The scanned tuple of leaf `m`. -/
def leafSym (m : Fin (leafCount V)) : Fin V.tapeCount → Bool :=
  symDecode ⟨m.val % 2 ^ V.tapeCount, Nat.mod_lt _ (by positivity)⟩

theorem leaf_decode (q : Fin V.stateCount) (σ : Fin V.tapeCount → Bool) :
    leafState V ⟨leafIndex V q σ, leafIndex_lt V q σ⟩ = q ∧ leafSym V ⟨leafIndex V q σ, leafIndex_lt V q σ⟩ = σ := by
  have hlt := (symCode σ).isLt
  have hpos : 0 < 2 ^ V.tapeCount := by positivity
  constructor
  · apply Fin.ext
    simp only [leafState, leafIndex]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · simp only [leafSym, leafIndex]
    have : (⟨(q.val * 2 ^ V.tapeCount + (symCode σ).val) % 2 ^ V.tapeCount, Nat.mod_lt _ hpos⟩ :
        Fin (2 ^ V.tapeCount)) = symCode σ := by
      apply Fin.ext
      simp only
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [this, symDecode_symCode]

/-- The leaf code at index `m`. -/
def leafCode (w : ℕ) (m : Fin (leafCount V)) : List (MI V w) :=
  padLeaf V w <|
    if V.machine.halted (leafState V m) then
      (if V.accepting (leafState V m) then accLeaf V w m.val else deadLeaf V w)
    else
      match V.machine.rule (leafState V m) (leafSym V m) with
      | none => deadLeaf V w
      | some a => actLeaf V w m.val a

/-! ## The code -/

/-- **The code `C_n`** for register width `w`, input length `n`, clock `t` and padded time `T` (`T_n`). -/
def mnCode (w n t T : ℕ) : List (MI V w) :=
  startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
    unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w ++ headerBlock V w ++
    chainBlock V w ++ (List.ofFn (leafCode V w)).flatten ++ [.jmp (deadAddr V)] ++
    idleCode 0 3 rCnt rTmp rVd (idleAddr V) T

theorem sum_ofFn_length {α : Type} {n c : ℕ} (f : Fin n → List α) (h : ∀ i, (f i).length = c) :
    (List.ofFn (List.length ∘ f)).sum = n * c := by
  have : (List.length ∘ f) = fun _ => c := funext h
  rw [this, List.ofFn_const, List.sum_replicate, smul_eq_mul]

theorem startBlock_length (w : ℕ) : (startBlock V w).length = 8 := rfl
theorem unpackBlock_length (w : ℕ) (rd : Fin (regCount V) → MI V w) (u N dead : ℕ) :
    (unpackBlock V w rd u N dead).length = 34 := rfl
theorem setupBlock_length (w : ℕ) : (setupBlock V w).length = 8 := rfl
theorem simSetupBlock_length (w : ℕ) : (simSetupBlock V w).length = 8 * (V.tapeCount + 1) := by
  simp [simSetupBlock]; ring

theorem headerBlock_length (w : ℕ) : (headerBlock V w).length = 4 * V.tapeCount + 1 := by
  simp only [headerBlock, List.length_append, List.length_flatten, List.map_ofFn, List.length_cons,
    List.length_nil]
  simp only [Function.comp_def, List.length_cons, List.length_nil, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]
  ring

theorem chainBlock_length (w : ℕ) : (chainBlock V w).length = 2 * leafCount V + 1 := by
  simp only [chainBlock, List.length_append, List.length_flatten, List.map_ofFn, List.length_cons,
    List.length_nil]
  simp only [Function.comp_def, List.length_cons, List.length_nil, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]
  ring

theorem tapeSeg_length (w : ℕ) (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) :
    (tapeSeg V w a i).length = 7 := by
  unfold tapeSeg; cases a.move i <;> rfl

theorem actLeaf_length_le (w : ℕ) (m : ℕ) (a : Action V.tapeCount V.stateCount) :
    (actLeaf V w m a).length ≤ leafLen V := by
  have hp : simPad V < 8 := by unfold simPad; omega
  simp only [actLeaf, List.length_append, List.length_replicate, List.length_flatten, List.map_ofFn,
    List.length_cons, List.length_nil]
  have : (List.ofFn ((fun l => List.length l) ∘ tapeSeg V w a)).sum = 7 * V.tapeCount := by
    have : ((fun l => List.length l) ∘ tapeSeg V w a) = fun _ => 7 := by
      funext i; exact tapeSeg_length V w a i
    rw [this]; simp [List.sum_replicate]; ring
  rw [this]; unfold leafLen; omega

theorem accLeaf_length_le (w : ℕ) (m : ℕ) : (accLeaf V w m).length ≤ leafLen V := by
  have hp : accPad V < 8 := by unfold accPad; omega
  simp only [accLeaf, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  unfold leafLen; omega

theorem padLeaf_length (w : ℕ) (l : List (MI V w)) (hl : l.length ≤ leafLen V) :
    (padLeaf V w l).length = leafLen V := by
  simp [padLeaf]; omega

theorem leafCode_length (w : ℕ) (m : Fin (leafCount V)) : (leafCode V w m).length = leafLen V := by
  unfold leafCode
  apply padLeaf_length
  split_ifs
  · exact accLeaf_length_le V w m.val
  · simp [deadLeaf, leafLen]
  · split
    · simp [deadLeaf, leafLen]
    · exact actLeaf_length_le V w m.val _

theorem mnCode_length (w n t T : ℕ) : (mnCode V w n t T).length = codeLen V := by
  simp only [mnCode, List.length_append, startBlock_length, unpackBlock_length, setupBlock_length,
    simSetupBlock_length, headerBlock_length, chainBlock_length, List.length_flatten, List.map_ofFn]
  have : (List.ofFn ((fun l => List.length l) ∘ leafCode V w)).sum = leafCount V * leafLen V := by
    have : ((fun l => List.length l) ∘ leafCode V w) = fun _ => leafLen V := by
      funext m; exact leafCode_length V w m
    rw [this]; simp [List.sum_replicate]
  rw [this]
  simp [idleCode, codeLen, idleAddr, deadAddr, leafAddr, chainAddr, interpAddr]
  ring

/-! ## The machine -/

/-- **`M_n = ⟨w_n, k, A, C_n⟩`** (`lem:tm-ram` and its proof), for `codeLen V ≤ 2^w`. -/
abbrev mnRam (w n t T : ℕ) (hfit : codeLen V ≤ 2 ^ w) : Ram where
  w := w
  k := regCount V
  ops := 4
  alu := mnAlu w
  code := mnCode V w n t T
  codeNonempty := by rw [mnCode_length]; unfold codeLen; omega
  codeFits := by rw [mnCode_length]; exact hfit

/-! ## Memory-well-behavedness (Def. 7.7; ruling B3) -/

/-- Every `load` is followed by its `pload` with distinct operands. -/
def LoadsOK {w k ops : ℕ} (l : List (Instr w k ops)) : Prop :=
  ∀ p i j, l[p]? = some (.load i j) → i ≠ j ∧ l[p + 1]? = some (.pload i j)

/-- No `load` at all. -/
def NoLoad {w k ops : ℕ} (l : List (Instr w k ops)) : Prop := ∀ i j, Instr.load i j ∉ l

theorem LoadsOK.of_noLoad {w k ops : ℕ} {l : List (Instr w k ops)} (h : NoLoad l) : LoadsOK l := by
  intro p i j hp
  exact absurd (List.mem_of_getElem? hp) (h i j)

theorem LoadsOK.append {w k ops : ℕ} {l₁ l₂ : List (Instr w k ops)} (h₁ : LoadsOK l₁) (h₂ : LoadsOK l₂)
    (hlast : ∀ i j, l₁.getLast? ≠ some (.load i j)) : LoadsOK (l₁ ++ l₂) := by
  intro p i j hp
  by_cases hlt : p < l₁.length
  · rw [List.getElem?_append_left hlt] at hp
    by_cases hlt' : p + 1 < l₁.length
    · obtain ⟨h1, h2⟩ := h₁ p i j hp
      exact ⟨h1, by rw [List.getElem?_append_left hlt']; exact h2⟩
    · exfalso
      have hp' : p = l₁.length - 1 := by omega
      apply hlast i j
      rw [List.getLast?_eq_getElem?, ← hp']; exact hp
  · rw [List.getElem?_append_right (by omega)] at hp
    obtain ⟨h1, h2⟩ := h₂ _ i j hp
    refine ⟨h1, ?_⟩
    rw [List.getElem?_append_right (by omega), show p + 1 - l₁.length = p - l₁.length + 1 by omega]
    exact h2

theorem LoadsOK.flatten {w k ops : ℕ} : ∀ (L : List (List (Instr w k ops))), (∀ l ∈ L, LoadsOK l) →
    (∀ l ∈ L, ∀ i j, l.getLast? ≠ some (.load i j)) → LoadsOK L.flatten
  | [], _, _ => LoadsOK.of_noLoad (by simp [NoLoad])
  | l :: L, h1, h2 => by
    rw [List.flatten_cons]
    by_cases hl : l = []
    · subst hl; simpa using LoadsOK.flatten L (fun l hl => h1 l (by simp [hl])) (fun l hl => h2 l (by simp [hl]))
    · exact LoadsOK.append (h1 l (by simp)) (LoadsOK.flatten L (fun l hl => h1 l (by simp [hl]))
        (fun l hl => h2 l (by simp [hl]))) (h2 l (by simp))

end NearCubicGates.Adapters.ShortPCP
