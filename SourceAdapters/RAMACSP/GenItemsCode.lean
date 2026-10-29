import SourceAdapters.RAMACSP.RamCodeWord

/-!
# The code of `M_n` as a fixed list with three holes

Paper anchor: proof of `lem:tm-ram` (The code `C_n` is a fixed code with the constant `T_n − 8` written into it;
with the deviations recorded in `ShortPCP/RAMCode.lean`, the input length `n` and the clock `t` are written into the
two unpacking loops), and the construction `lem:generator` (G5) (the code-dependent constants … are read from the code
`C_n`, which is `V`'s fixed template with the three numbers `n`, `t`, `T − 8` … inserted).

`refList V` is a list of descriptors that depends on `V` only: an instruction at the reference width `clockConst V`,
or a hole `x ← cmp(r, c)` whose constant `c` is one of the three numbers. `realize w vals` writes a descriptor at the
width `w` with the hole values `vals`; `mnCode_eq`: for every width `w`, `mnCode V w n t T` is
`refList V` realized with `(n, t, T − 8)` (the instruction-level form of `RamCodeWord.ramCode_template`, by the same
width-independence argument: every fixed constant of the code is at most `clockConst V`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.RAMACSP.RamCodeWord
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-! ## Changing the width of an instruction -/

/-- An operand at another width (constants by value). -/
def retagOp {w w' k : ℕ} : Operand w k → Operand w' k
  | .reg i => .reg i
  | .pc => .pc
  | .const c => .const (BitVec.ofNat w' c.toNat)

/-- An instruction at another width (constants by value). -/
def retag {w w' k ops : ℕ} : Instr w k ops → Instr w' k ops
  | .nop => .nop
  | .readA i => .readA i
  | .readB i => .readB i
  | .load i j => .load i j
  | .pload i j => .pload i j
  | .store j x => .store j (retagOp x)
  | .iseof i j => .iseof i j
  | .out b => .out b
  | .arith op i x y => .arith op i (retagOp x) (retagOp y)
  | .je i c => .je i c
  | .jne i c => .jne i c
  | .jmp c => .jmp c

@[simp] theorem retagOp_reg {w w' k : ℕ} (i : Fin k) : (retagOp (.reg i : Operand w k) : Operand w' k) = .reg i := rfl
@[simp] theorem retagOp_pc {w w' k : ℕ} : (retagOp (.pc : Operand w k) : Operand w' k) = .pc := rfl

variable (V : Verifier)

theorem retagOp_cst {w k : ℕ} (c : ℕ) (hc : c ≤ clockConst V) :
    (retagOp (cst c : Operand (refW V) k) : Operand w k) = cst c := by
  simp only [retagOp, cst, BitVec.toNat_ofNat, mod_ref V c hc]

theorem retagOp_const {w k : ℕ} (c : ℕ) (hc : c ≤ clockConst V) :
    (retagOp (.const (BitVec.ofNat (refW V) c) : Operand (refW V) k) : Operand w k) = .const (BitVec.ofNat w c) := by
  simp only [retagOp, BitVec.toNat_ofNat, mod_ref V c hc]

/-! ## Descriptors -/

/-- A descriptor: a reference instruction, or the hole `x ← cmp(r, c)` with `c` the hole value `i`
(`0 ↦ n`, `1 ↦ t`, `2 ↦ T − 8`). -/
inductive Desc where
  | ins (I : MI V (refW V))
  | hole (r : Fin (regCount V)) (i : Fin 3)

/-- A descriptor written at width `w` with the hole values `vals`. -/
def realize (w : ℕ) (vals : Fin 3 → ℕ) : Desc V → MI V w
  | .ins I => retag I
  | .hole r i => .arith 3 rTmp (.reg r) (.const (BitVec.ofNat w (vals i)))

/-- **The reference list of the code.** -/
def refList : List (Desc V) :=
  (startBlock V (refW V)).map .ins ++ [.hole rP 0] ++
    (unpackRest V (refW V) (fun r => .readA r) 8 (deadAddr V)).map .ins ++ (setupBlock V (refW V)).map .ins ++
    [.hole rP 1] ++ (unpackRest V (refW V) (fun r => .readB r) 50 (deadAddr V)).map .ins ++
    (simSetupBlock V (refW V)).map .ins ++ (headerBlock V (refW V)).map .ins ++ (chainBlock V (refW V)).map .ins ++
    ((List.ofFn (leafCode V (refW V))).flatten).map .ins ++ [.ins (.jmp (deadAddr V))] ++
    [.ins (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat (refW V) 8)))] ++ [.hole rCnt 2] ++
    (idleRest V (refW V)).map .ins

/-! ## Width independence of the fixed blocks -/

section Fixed

variable {w : ℕ}

theorem map_retag_startBlock : (startBlock V (refW V)).map retag = startBlock V w := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [startBlock, retag, retagOp_cst V]

theorem map_retag_setupBlock : (setupBlock V (refW V)).map retag = setupBlock V w := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [setupBlock, retag, retagOp_cst V]

theorem map_retag_unpackRest (isA : Bool) (u : ℕ) :
    (unpackRest V (refW V) (if isA then fun r => .readA r else fun r => .readB r) u (deadAddr V)).map retag =
      unpackRest V w (if isA then fun r => .readA r else fun r => .readB r) u (deadAddr V) := by
  obtain ⟨h16, -, hs, -⟩ := consts_le V
  cases isA <;> simp (disch := omega) [unpackRest, unpackBlock, retag, retagOp_cst V]

theorem map_retag_simSetupBlock : (simSetupBlock V (refW V)).map retag = simSetupBlock V w := by
  obtain ⟨h16, -, -, ht, -, hq, -, -, h8⟩ := consts_le V
  have hi : ∀ i : Fin V.tapeCount, (i : ℕ) ≤ clockConst V := fun i => by have := i.isLt; omega
  have hq' : ∀ q : Fin V.stateCount, (q : ℕ) ≤ clockConst V := fun q => by have := q.isLt; omega
  simp (disch := first | omega | exact hi _ | exact hq' _)
    [simSetupBlock, retag, retagOp_cst V, List.map_ofFn, Function.comp_def]

theorem map_retag_headerBlock : (headerBlock V (refW V)).map retag = headerBlock V w := by
  obtain ⟨h16, -⟩ := consts_le V
  simp (disch := omega) [headerBlock, retag, retagOp_cst V, List.map_ofFn, Function.comp_def, List.map_flatten]

theorem map_retag_chainBlock : (chainBlock V (refW V)).map retag = chainBlock V w := by
  obtain ⟨h16, -, -, -, hl, -⟩ := consts_le V
  have hm : ∀ m : Fin (leafCount V), (m : ℕ) ≤ clockConst V := fun m => by have := m.isLt; omega
  simp (disch := first | omega | exact hm _) [chainBlock, retag, retagOp_cst V, List.map_ofFn, Function.comp_def,
    List.map_flatten]

theorem map_retag_tapeSeg (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) :
    (tapeSeg V (refW V) a i).map retag = tapeSeg V w a i := by
  obtain ⟨h16, -, hs, -⟩ := consts_le V
  unfold tapeSeg
  cases hm : a.move i <;> cases hwr : a.write i <;>
    simp (disch := omega) [writeInstr, moveInstrs, hm, hwr, retag, retagOp_cst V] <;>
    split_ifs <;> simp (disch := omega) [retagOp_cst V]

theorem map_retag_replicate_nop (n : ℕ) :
    (List.replicate n (.nop : MI V (refW V))).map retag = (List.replicate n (.nop : MI V w)) := by
  simp [retag]

theorem map_retag_padLeaf (l : List (MI V (refW V))) (l' : List (MI V w)) (h : l.map retag = l') :
    (padLeaf V (refW V) l).map retag = padLeaf V w l' := by
  have hl : l.length = l'.length := by rw [← h, List.length_map]
  simp only [padLeaf, List.map_append, h, map_retag_replicate_nop, hl]

theorem map_retag_leafCode (m : Fin (leafCount V)) : (leafCode V (refW V) m).map retag = leafCode V w m := by
  obtain ⟨h16, -, hs, -, -, hq, hsim, hacc, -⟩ := consts_le V
  unfold leafCode
  split_ifs with h1 h2
  · apply map_retag_padLeaf
    simp (disch := omega) [accLeaf, retag, retagOp_cst V]
  · exact map_retag_padLeaf V _ _ rfl
  · split
    · exact map_retag_padLeaf V _ _ rfl
    · rename_i a _
      have hq' : a.nextControl.val ≤ clockConst V := by have := a.nextControl.isLt; omega
      apply map_retag_padLeaf
      simp only [actLeaf, List.map_append, List.map_flatten, List.map_ofFn, Function.comp_def,
        map_retag_tapeSeg V a, map_retag_replicate_nop]
      simp (disch := omega) [retag, retagOp_cst V]

theorem map_retag_leaves :
    ((List.ofFn (leafCode V (refW V))).flatten).map retag = (List.ofFn (leafCode V w)).flatten := by
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def, map_retag_leafCode V]

theorem map_retag_idleRest : (idleRest V (refW V)).map retag = idleRest V w := by
  simp [idleRest, idleCode, retag]

end Fixed

/-- **The code is the reference list with the three numbers written in** (for every width `w`). -/
theorem mnCode_eq (w n t T : ℕ) :
    mnCode V w n t T = (refList V).map (realize V w ![n, t, T - 8]) := by
  have hA := map_retag_unpackRest V (w := w) true 8
  have hB := map_retag_unpackRest V (w := w) false 50
  simp only [if_true, if_false, Bool.false_eq_true] at hA hB
  have h16 := (consts_le V).1
  have hidle : (retag (.arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat (refW V) 8)) : MI V (refW V)) : MI V w) =
      .arith 0 rCnt (.reg rCnt) (.const (BitVec.ofNat w 8)) := by
    show Instr.arith 0 rCnt (retagOp (.reg rCnt)) (retagOp (.const (BitVec.ofNat (refW V) 8))) = _
    rw [retagOp_const V 8 (by omega)]; rfl
  simp only [refList, List.map_append, List.map_map, Function.comp_def, realize, List.map_cons, List.map_nil]
  have e1 : (startBlock V (refW V)).map (fun I => (retag I : MI V w)) = startBlock V w := map_retag_startBlock V
  have e2 : (unpackRest V (refW V) (fun r => .readA r) 8 (deadAddr V)).map (fun I => (retag I : MI V w)) =
      unpackRest V w (fun r => .readA r) 8 (deadAddr V) := hA
  have e3 : (setupBlock V (refW V)).map (fun I => (retag I : MI V w)) = setupBlock V w := map_retag_setupBlock V
  have e4 : (unpackRest V (refW V) (fun r => .readB r) 50 (deadAddr V)).map (fun I => (retag I : MI V w)) =
      unpackRest V w (fun r => .readB r) 50 (deadAddr V) := hB
  have e5 : (simSetupBlock V (refW V)).map (fun I => (retag I : MI V w)) = simSetupBlock V w :=
    map_retag_simSetupBlock V
  have e6 : (headerBlock V (refW V)).map (fun I => (retag I : MI V w)) = headerBlock V w := map_retag_headerBlock V
  have e7 : (chainBlock V (refW V)).map (fun I => (retag I : MI V w)) = chainBlock V w := map_retag_chainBlock V
  have e8 : ((List.ofFn (leafCode V (refW V))).flatten).map (fun I => (retag I : MI V w)) =
      (List.ofFn (leafCode V w)).flatten := map_retag_leaves V
  have e9 : (idleRest V (refW V)).map (fun I => (retag I : MI V w)) = idleRest V w := map_retag_idleRest V
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, hidle]
  simp only [mnCode, unpackBlock_eq, idleCode_eq, cst, List.append_assoc, List.cons_append, List.singleton_append]
  rfl

end NearCubicGates.Adapters.RAMACSP.Gen.Items
