import SourceAdapters.ShortPCP.ClockFits

/-!
# The code word of `M_n` as a template with four holes

`lem:tm-ram`: "the code of `M_n` is a fixed code, depending only on `V`, into which the integers `n`, `T(n)` and
`T_n − 8` are written". The natural encoding `ramCode` (`ACSP/Model.lean`) of `M_n = mnRam V w n t T` is

  `numCode w ++ E0 ++ numCode (n mod 2^w) ++ E1 ++ numCode (t mod 2^w) ++ E2 ++ numCode ((T−8) mod 2^w) ++ E3`

with words `E0 … E3` that depend on `V` only (`ramCode_template`), whenever `clockConst V ≤ w`: every other constant
of the code is at most `clockConst V`, so its `w`-bit value is the number itself. The `E`s are the encodings at the
reference width `clockConst V`. The integers `n` and `t` are written into the two unpacking loops (`RAMCode.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.RamCodeWord

open NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.ShortPCP
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

variable (V : Verifier)

/-- The encoding of an instruction list. -/
def encI {w k ops : ℕ} (l : List (Instr w k ops)) : List Bool := (l.map instrCode).flatten

theorem encI_append {w k ops : ℕ} (l l' : List (Instr w k ops)) : encI (l ++ l') = encI l ++ encI l' := by
  simp [encI]

theorem encI_cons {w k ops : ℕ} (i : Instr w k ops) (l : List (Instr w k ops)) :
    encI (i :: l) = instrCode i ++ encI l := by simp [encI]

/-- The reference width of the fixed words. -/
abbrev refW : ℕ := clockConst V

/-- The unpacking loop after its first instruction (independent of the bound `N`). -/
def unpackRest (w : ℕ) (rd : Fin (regCount V) → MI V w) (u dead : ℕ) : List (MI V w) :=
  (unpackBlock V w rd u 0 dead).tail

theorem unpackBlock_eq (w : ℕ) (rd : Fin (regCount V) → MI V w) (u N dead : ℕ) :
    unpackBlock V w rd u N dead = .arith 3 rTmp (.reg rP) (cst N) :: unpackRest V w rd u dead := rfl

/-- The words of the instruction `x ← cmp/add(r, ·)` up to its constant operand's value: tag `8`, operation `op`,
target `i`, first operand the register `j`, kind `2` (a constant). -/
def arithPre (op i j : ℕ) : List Bool := numCode 8 ++ numCode op ++ numCode i ++ (numCode 0 ++ numCode j) ++ numCode 2

/-- The idle block after its first two instructions. -/
def idleRest (w : ℕ) : List (MI V w) := (idleCode 0 3 rCnt rTmp rVd (idleAddr V) 0).drop 2

theorem idleCode_eq (w T : ℕ) :
    idleCode (w := w) 0 3 rCnt rTmp rVd (idleAddr V) T =
      .arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat w 8)) ::
        .arith 3 rTmp (.reg rCnt) (.const (BitVec.ofNat w (T - 8))) :: idleRest V w := rfl

/-- The fixed words of the template. -/
def E0 : List Bool :=
  numCode (regCount V) ++ numCode 4 ++ numCode (codeLen V) ++ encI (startBlock V (refW V)) ++ arithPre 3 1 3

def E1 : List Bool :=
  encI (unpackRest V (refW V) (fun r => .readA r) 8 (deadAddr V)) ++ encI (setupBlock V (refW V)) ++ arithPre 3 1 3

def E2 : List Bool :=
  encI (unpackRest V (refW V) (fun r => .readB r) 50 (deadAddr V)) ++ encI (simSetupBlock V (refW V)) ++
    encI (headerBlock V (refW V)) ++ encI (chainBlock V (refW V)) ++
    encI (List.ofFn (leafCode V (refW V))).flatten ++ encI [(.jmp (deadAddr V) : MI V (refW V))] ++
    instrCode (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat (refW V) 8)) : MI V (refW V)) ++ arithPre 3 1 0

def E3 : List Bool := encI (idleRest V (refW V))

/-! ## Width independence of the fixed blocks -/

section Fixed

variable {w : ℕ}

theorem mod_small (hw : refW V ≤ w) (c : ℕ) (hc : c ≤ clockConst V) : c % 2 ^ w = c :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (hc.trans hw) Nat.lt_two_pow_self)

theorem mod_ref (c : ℕ) (hc : c ≤ clockConst V) : c % 2 ^ refW V = c :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt hc Nat.lt_two_pow_self)

theorem leafCount_le_codeLen : leafCount V ≤ codeLen V := by
  unfold codeLen idleAddr deadAddr leafAddr leafLen
  have : leafCount V ≤ leafCount V * (2 * leafCount V + 7 * V.tapeCount + 12) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem stateCount_le_leafCount : V.stateCount ≤ leafCount V := by
  unfold leafCount
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem consts_le : 64 ≤ clockConst V ∧ codeLen V ≤ clockConst V ∧ stride V ≤ clockConst V ∧
    V.tapeCount ≤ clockConst V ∧ leafCount V ≤ clockConst V ∧ V.stateCount ≤ clockConst V ∧
    simLen V ≤ clockConst V ∧ accLen V ≤ clockConst V ∧ 8 * (V.tapeCount + 1) ≤ clockConst V := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := clockConst_facts V _ le_rfl
  have := leafCount_le_codeLen V
  have := stateCount_le_leafCount V
  refine ⟨by unfold clockConst; omega, h2, h3, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem encI_startBlock (hw : refW V ≤ w) : encI (startBlock V w) = encI (startBlock V (refW V)) := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [encI, startBlock, instrCode, operandCode, cst, mod_small V hw, mod_ref V]

theorem encI_setupBlock (hw : refW V ≤ w) : encI (setupBlock V w) = encI (setupBlock V (refW V)) := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [encI, setupBlock, instrCode, operandCode, cst, mod_small V hw, mod_ref V]

theorem encI_unpackRest (hw : refW V ≤ w) (isA : Bool) (u : ℕ) :
    encI (unpackRest V w (if isA then fun r => .readA r else fun r => .readB r) u (deadAddr V)) =
      encI (unpackRest V (refW V) (if isA then fun r => .readA r else fun r => .readB r) u (deadAddr V)) := by
  obtain ⟨h16, -, hs, -⟩ := consts_le V
  cases isA <;>
  simp (disch := omega) [encI, unpackRest, unpackBlock, instrCode, operandCode, cst, mod_small V hw, mod_ref V]

theorem encI_simSetupBlock (hw : refW V ≤ w) :
    encI (simSetupBlock V w) = encI (simSetupBlock V (refW V)) := by
  obtain ⟨h16, -, -, ht, -, hq, -, -, h8⟩ := consts_le V
  have hi : ∀ i : Fin V.tapeCount, (i : ℕ) ≤ clockConst V := fun i => by have := i.isLt; omega
  have hq' : ∀ q : Fin V.stateCount, (q : ℕ) ≤ clockConst V := fun q => by have := q.isLt; omega
  simp (disch := first | omega | exact hi _ | exact hq' _)
    [encI, simSetupBlock, instrCode, operandCode, cst, mod_small V hw, mod_ref V, List.map_ofFn, Function.comp_def]

theorem encI_headerBlock (hw : refW V ≤ w) : encI (headerBlock V w) = encI (headerBlock V (refW V)) := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [encI, headerBlock, instrCode, operandCode, cst, mod_small V hw, mod_ref V, List.map_ofFn,
    Function.comp_def, List.map_flatten]

theorem encI_chainBlock (hw : refW V ≤ w) : encI (chainBlock V w) = encI (chainBlock V (refW V)) := by
  obtain ⟨h16, -, -, -, hl, -⟩ := consts_le V
  have hm : ∀ m : Fin (leafCount V), (m : ℕ) ≤ clockConst V := fun m => by have := m.isLt; omega
  simp (disch := first | omega | exact hm _) [encI, chainBlock, instrCode, operandCode, cst, mod_small V hw,
    mod_ref V, List.map_ofFn, Function.comp_def, List.map_flatten]

theorem encI_flatten {w k ops : ℕ} (l : List (List (Instr w k ops))) : encI l.flatten = (l.map encI).flatten := by
  simp [encI, List.map_flatten, List.flatten_flatten, Function.comp_def]
  rfl

theorem encI_ofFn_flatten {n w w' k ops : ℕ} (f : Fin n → List (Instr w k ops)) (g : Fin n → List (Instr w' k ops))
    (h : ∀ i, encI (f i) = encI (g i)) : encI (List.ofFn f).flatten = encI (List.ofFn g).flatten := by
  rw [encI_flatten, encI_flatten, List.map_ofFn, List.map_ofFn]
  congr 2
  funext i
  exact h i

theorem encI_replicate_nop {w k ops : ℕ} (n : ℕ) :
    encI (List.replicate n (.nop : Instr w k ops)) = (List.replicate n (numCode 0)).flatten := by
  simp [encI, instrCode]

theorem encI_tapeSeg (hw : refW V ≤ w) (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) :
    encI (tapeSeg V w a i) = encI (tapeSeg V (refW V) a i) := by
  obtain ⟨h16, -, hs, -⟩ := consts_le V
  unfold tapeSeg
  cases hm : a.move i <;> cases hwr : a.write i <;>
    simp (disch := omega) [encI, writeInstr, moveInstrs, hm, hwr, instrCode, operandCode, cst, mod_small V hw,
      mod_ref V] <;> split_ifs <;> simp (disch := omega) [mod_small V hw, mod_ref V]

theorem encI_padLeaf {w' : ℕ} (l : List (MI V w)) (l' : List (MI V w')) (h : encI l = encI l')
    (hl : l.length = l'.length) : encI (padLeaf V w l) = encI (padLeaf V w' l') := by
  simp only [padLeaf, encI_append, encI_replicate_nop, h, hl]

theorem encI_leafCode (hw : refW V ≤ w) (m : Fin (leafCount V)) :
    encI (leafCode V w m) = encI (leafCode V (refW V) m) := by
  obtain ⟨h16, -, hs, -, -, hq, hsim, hacc, -⟩ := consts_le V
  unfold leafCode
  split_ifs with h1 h2
  · apply encI_padLeaf
    · simp (disch := omega) [accLeaf, encI_append, encI_replicate_nop, encI, instrCode, operandCode, cst,
        mod_small V hw, mod_ref V]
    · simp [accLeaf]
  · exact encI_padLeaf V _ _ rfl rfl
  · split
    · exact encI_padLeaf V _ _ rfl rfl
    · rename_i a _
      have hq' : a.nextControl.val ≤ clockConst V := by have := a.nextControl.isLt; omega
      apply encI_padLeaf
      · simp only [actLeaf, encI_append, encI_replicate_nop]
        rw [encI_ofFn_flatten (tapeSeg V w a) (tapeSeg V (refW V) a) (encI_tapeSeg V hw a)]
        simp (disch := omega) [encI, instrCode, operandCode, cst, mod_small V hw, mod_ref V]
      · simp [actLeaf, Function.comp_def, tapeSeg_length]

theorem encI_leaves (hw : refW V ≤ w) :
    encI (List.ofFn (leafCode V w)).flatten = encI (List.ofFn (leafCode V (refW V))).flatten :=
  encI_ofFn_flatten _ _ (encI_leafCode V hw)

theorem encI_idleRest : encI (idleRest V w) = encI (idleRest V (refW V)) := by
  simp [idleRest, idleCode, encI, instrCode]

theorem instrCode_arith_cst (op : Fin 4) (i j : Fin (regCount V)) (c : ℕ) :
    instrCode (.arith op i (.reg j) (cst c) : MI V w) = arithPre op.val i.val j.val ++ numCode (c % 2 ^ w) := by
  simp [instrCode, operandCode, cst, arithPre]

theorem instrCode_arith_const (op : Fin 4) (i j : Fin (regCount V)) (c : ℕ) :
    instrCode (.arith op i (.reg j) (.const (BitVec.ofNat w c)) : MI V w) =
      arithPre op.val i.val j.val ++ numCode (c % 2 ^ w) := by
  simp [instrCode, operandCode, arithPre]

theorem encI_mnCode (n t T : ℕ) :
    encI (mnCode V w n t T) = encI (startBlock V w) ++ (arithPre 3 1 3 ++ numCode (n % 2 ^ w)) ++
      encI (unpackRest V w (fun r => .readA r) 8 (deadAddr V)) ++ encI (setupBlock V w) ++
      (arithPre 3 1 3 ++ numCode (t % 2 ^ w)) ++ encI (unpackRest V w (fun r => .readB r) 50 (deadAddr V)) ++
      encI (simSetupBlock V w) ++ encI (headerBlock V w) ++ encI (chainBlock V w) ++
      encI (List.ofFn (leafCode V w)).flatten ++ encI [(.jmp (deadAddr V) : MI V w)] ++
      instrCode (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat w 8)) : MI V w) ++
      (arithPre 3 1 0 ++ numCode ((T - 8) % 2 ^ w)) ++ encI (idleRest V w) := by
  simp only [mnCode, encI_append, unpackBlock_eq, encI_cons, idleCode_eq, instrCode_arith_cst,
    instrCode_arith_const, List.append_assoc]
  rfl

/-- **The code word of `M_n` is the template** (`lem:tm-ram`). -/
theorem ramCode_template (n t T : ℕ) (hfit : codeLen V ≤ 2 ^ w) (hw : refW V ≤ w) :
    ramCode (mnRam V w n t T hfit) = numCode w ++ E0 V ++ numCode (n % 2 ^ w) ++ E1 V ++ numCode (t % 2 ^ w) ++
      E2 V ++ numCode ((T - 8) % 2 ^ w) ++ E3 V := by
  have hA := encI_unpackRest V hw true 8
  have hB := encI_unpackRest V hw false 50
  simp only [if_true, if_false, Bool.false_eq_true] at hA hB
  have h16 := (consts_le V).1
  have hidle : instrCode (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat w 8)) : MI V w) =
      instrCode (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat (refW V) 8)) : MI V (refW V)) := by
    simp (disch := omega) [instrCode, operandCode, mod_small V hw, mod_ref V]
  have hjmp : encI [(.jmp (deadAddr V) : MI V w)] = encI [(.jmp (deadAddr V) : MI V (refW V))] := rfl
  have key : ramCode (mnRam V w n t T hfit) =
      numCode w ++ (numCode (regCount V) ++ numCode 4 ++ numCode (codeLen V)) ++ encI (mnCode V w n t T) := by
    show numCode w ++ numCode (regCount V) ++ numCode 4 ++ numCode (mnCode V w n t T).length ++
      (List.map instrCode (mnCode V w n t T)).flatten = _
    rw [mnCode_length]
    simp only [List.append_assoc]
    rfl
  rw [key, encI_mnCode, encI_startBlock V hw, hA, encI_setupBlock V hw, hB, encI_simSetupBlock V hw,
    encI_headerBlock V hw, encI_chainBlock V hw, encI_leaves V hw, hjmp, hidle, encI_idleRest V]
  simp only [E0, E1, E2, E3, List.append_assoc]

end Fixed

end NearCubicGates.Adapters.RAMACSP.RamCodeWord
