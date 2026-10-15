import Proof.Wire_3_5.ListMachinePrintOuter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-! ## The visited supports -/

/-- The support bitmap before pass `k`. -/
def xsAt (L d k : ℕ) : List Bool := (Interp.sw d)^[k] (binary L 0)

theorem xsAt_succ (L d k : ℕ) : xsAt L d (k + 1) = Interp.sw d (xsAt L d k) := by
  simp [xsAt, Function.iterate_succ_apply']

theorem xsAt_length (L d k : ℕ) : (xsAt L d k).length = L := by
  induction k with
  | zero => simp [xsAt]
  | succ k ih => rw [xsAt_succ, sw_length, ih]

/-- The mask tape before pass `k`. -/
def mAt (L d : ℕ) (m0 : List Bool) : ℕ → List Bool
  | 0 => m0
  | k + 1 => Block.ripple Interp.gL Interp.hL false (xsAt L d k) (xsAt L d k)

theorem mAt_length (L d : ℕ) (m0 : List Bool) (hm0 : m0.length = L) (k : ℕ) : (mAt L d m0 k).length = L := by
  cases k with
  | zero => exact hm0
  | succ k => simp [mAt, ripple_length _ _ _ _ _ rfl, xsAt_length]

/-- What the first `k` passes print. -/
def printedAt (f : List Bool → Bool) (L d k : ℕ) : List Bool :=
  (List.range k).flatMap fun i => pr (Interp.subsetX f L (Interp.supp (xsAt L d i))) (xsAt L d i)

theorem printedAt_succ (f : List Bool → Bool) (L d k : ℕ) :
    printedAt f L d (k + 1) =
      printedAt f L d k ++ pr (Interp.subsetX f L (Interp.supp (xsAt L d k))) (xsAt L d k) := by
  simp [printedAt, List.range_succ, List.flatMap_append]

theorem any_binary (L X : ℕ) (hX : X < 2 ^ L) : (binary L X).any id = decide (X ≠ 0) := by
  by_cases h : X = 0
  · subst h; simp [Interp.binary_zero]
  · have hpos := Interp.pop_binary_pos L X (Nat.pos_of_ne_zero h) hX
    have hmem : true ∈ binary L X := List.count_pos_iff.mp hpos
    rw [decide_eq_true h]
    exact List.any_eq_true.mpr ⟨true, hmem, rfl⟩

theorem xsAt_goods (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    xsAt L d k = binary L (Interp.goods L d)[k] := (Interp.sw_iterate L d hd).1 k hk

theorem xsAt_end (L d : ℕ) (hd : 1 ≤ d) : xsAt L d (Interp.goods L d).length = binary L 0 :=
  (Interp.sw_iterate L d hd).2

theorem xsAt_pop (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    Interp.pop (xsAt L d k) ≤ d := by
  rw [xsAt_goods L d hd k hk]
  exact (Interp.mem_goods.mp (List.getElem_mem hk)).2

/-- The outer flag after pass `k`: the next support is nonzero exactly while supports remain. -/
theorem fo_next (L d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    (Interp.sw d (xsAt L d k)).any id = decide (k + 1 < (Interp.goods L d).length) := by
  rw [← xsAt_succ]
  rcases Nat.lt_or_eq_of_le (show k + 1 ≤ (Interp.goods L d).length by omega) with h | h
  · rw [xsAt_goods L d hd (k + 1) h, any_binary L _ (Interp.mem_goods.mp (List.getElem_mem h)).1]
    obtain ⟨h0len, h0⟩ := Interp.goods_zero L d
    have := List.pairwise_iff_getElem.mp (Interp.goods_pairwise L d) 0 (k + 1) h0len h (by omega)
    simp [h]; omega
  · rw [h, xsAt_end L d hd]; simp [Interp.binary_zero]

/-! ## One pass of the outer loop -/

noncomputable def setFIM := RecoveryFocus.machine sFI (GF2.CellOp.machine (constOp true))

/-- One outer pass: raise the inner flag, the inner loop, print and step. -/
noncomputable def outerBody {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) :=
  Composition.machine (Composition.machine (RecoveryFocus.machine (Fin.castAdd E.t) setFIM)
    (StreamController.machine (innerBody E) (Fin.castAdd E.t 4)))
    (RecoveryFocus.machine (Fin.castAdd E.t) outerRest)

theorem recInnerCost_len (xs : List Bool) : recInnerCost xs = recInnerCost (List.replicate xs.length false) := by
  simp [recInnerCost, loopCostR]

/-- The bank before outer pass `k`. -/
def outerBank (f : List Bool → Bool) (L d : ℕ) (dtail out B Ub m0 : List Bool) (cap1 cap2 k : ℕ) : Bank where
  x := frame (xsAt L d k)
  t := frame (List.replicate L false)
  r := [false]
  a := [false]
  fi := [false]
  fo := [decide (k < (Interp.goods L d).length)]
  pf := [false]
  m := frame (mAt L d m0 k)
  z := frame (List.replicate L false)
  d := List.replicate d true ++ false :: dtail
  o := overlay (out ++ printedAt f L d k) B
  u := Ub
  l1 := List.replicate cap1 false
  l2 := List.replicate cap2 false

/-- The cost of outer pass `k`. -/
def outerPassCost {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d k : ℕ) : ℕ :=
  1 + 1 + (2 ^ Interp.pop (xsAt L d k) * (innerPassCost E L + 2) + 1) + 1 + outerRestCost (xsAt L d k)

theorem outerBody_step {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d)
    (dtail out B Ub m0 : List Bool) (cap1 cap2 : ℕ) (hm0 : m0.length = L)
    (hUb : overlay (frame (List.replicate L true)) Ub = Ub) (hcap1 : armCost L + 2 ≤ cap1)
    (hcap2 : recInnerCost (List.replicate L false) ≤ cap2) (k : ℕ) (hk : k < (Interp.goods L d).length) :
    Step (outerBody E) (outerPassCost E d k)
      (Fin.addCases (bh (out ++ printedAt f L d k).length) (fun _ => 0))
      (Fin.addCases (outerBank f L d dtail out B Ub m0 cap1 cap2 k).tapes E.data)
      (Fin.addCases (bh (out ++ printedAt f L d (k + 1)).length) (fun _ => 0))
      (Fin.addCases (outerBank f L d dtail out B Ub m0 cap1 cap2 (k + 1)).tapes E.data) := by
  set b := outerBank f L d dtail out B Ub m0 cap1 cap2 k with hb
  set xs := xsAt L d k with hxs
  have hxl : xs.length = L := xsAt_length L d k
  have hc1 : 2 * xs.length + 1 ≤ cap1 := le_trans (by simp [armCost, hxl]) hcap1
  set o := (out ++ printedAt f L d k).length with ho
  -- raise the inner flag
  have s1 := lift_stage (cell_step (constOp true) sFI sFI_inj o b { b with fi := [true] } false false false
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
    (by rw [install_of_pick sFI pFI pick_sFI]; funext i; fin_cases i <;> simp [pFI, Bank.tapes, hb, outerBank, constOp]))
    E.data
  -- the coefficient
  have s2 := inner_run E b o xs hxl cap1 rfl rfl hc1
  rw [hxl] at s2
  have e2 : ({ b with t := frame (List.replicate L false), r := [false], a := [false], fi := [true] } : Bank) =
      { b with fi := [true] } := by simp [hb, outerBank]
  rw [e2] at s2
  set c := Interp.subsetX f L (Interp.supp xs) with hc
  set r3 := rAt f xs (2 ^ Interp.pop xs) with hr3
  set b3 : Bank := { b with t := frame (List.replicate L false), r := [r3], a := [c], fi := [false] } with hb3
  -- print and step
  have s3 := lift_stage (outerRest_step b3 xs Ub (out ++ printedAt f L d k) B (mAt L d m0 k) dtail d cap1 cap2 c
    r3 false false (decide (k < (Interp.goods L d).length)) rfl rfl rfl rfl rfl rfl rfl
    (by rw [mAt_length L d m0 hm0, hxl]) (by rw [hxl]; rfl) rfl rfl rfl rfl rfl (by rw [hxl]; exact hUb)
    (xsAt_pop L d hd k hk) (by rw [hxl]; exact hcap1) (by rw [recInnerCost_len, hxl]; exact hcap2)) E.data
  have t := Step.seq (Step.seq s1 s2) s3
  have eo : out ++ printedAt f L d k ++ pr c xs = out ++ printedAt f L d (k + 1) := by
    rw [printedAt_succ, List.append_assoc]
  rw [eo] at t
  set m3 := frame (Block.ripple Interp.gL Interp.hL false xs xs) with hm3
  set fo3 := [(Interp.sw d xs).any id] with hfo3
  have eb : ({ b3 with o := overlay (out ++ printedAt f L d (k + 1)) B, a := [false], r := [false], pf := [false],
                       m := m3, x := frame (Interp.sw d xs), fo := fo3 } : Bank) =
      outerBank f L d dtail out B Ub m0 cap1 cap2 (k + 1) := by
    simp only [hb3, hb, hm3, hfo3, hxs, outerBank, xsAt_succ, fo_next L d hd k hk, mAt]
  rw [eb] at t
  refine t.enlarge (le_of_eq ?_)
  simp [outerPassCost, hxs]

/-! ## The printer -/

theorem flatMap_range_getD {α β : Type} (l : List α) (x0 : α) (F : α → List β) :
    (List.range l.length).flatMap (fun i => F (l.getD i x0)) = l.flatMap F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]

theorem filter_map_flatMap {α β : Type} (l : List α) (g : α → List ℕ) (P : List ℕ → Bool) (r : List ℕ → List β) :
    ((l.map g).filter P).flatMap r = l.flatMap fun x => if P (g x) then r (g x) else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : P (g a) = true <;> simp [h, ih]

/-- **What the printer prints**: the word of the interpolation print. -/
theorem printedAt_full (f : List Bool → Bool) (L d : ℕ) (hd : 1 ≤ d) :
    printedAt f L d (Interp.goods L d).length ++ [false] = Rec.polyWord (Interp.interpPrint f L d) := by
  unfold Rec.polyWord Interp.interpPrint
  rw [Interp.monos_eq_goods, filter_map_flatMap, ← flatMap_range_getD _ 0]
  congr 1
  unfold printedAt
  apply Interp.flatMap_congr_mem
  intro i hi
  have hi' : i < (Interp.goods L d).length := List.mem_range.mp hi
  rw [xsAt_goods L d hd i hi', List.getD_eq_getElem _ _ hi']
  simp [pr]

/-- **The interpolation printer** on the evaluator of `f`. -/
noncomputable def printM {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) :=
  Composition.machine (StreamController.machine (outerBody E) (Fin.castAdd E.t 5))
    (RecoveryFocus.machine (Fin.castAdd E.t) (RecoveryFocus.machine sOut (Put.machine false)))

/-- The printer's cost: the passes over the supports, then the terminator. -/
def printCost {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) : ℕ :=
  ((List.range (Interp.goods L d).length).map fun k => outerPassCost E d k + 2).sum + 1 + 1 + 1

/-- **The printer**: from the bank with the zero support, the unary bound `1^d 0`, the position word
`frame (1^L)`, the output cursor at `out` and the evaluator's tapes, the output receives
`polyWord (Interp.interpPrint f L d)`, the reduced expansion of `f` in degree `≤ d`. -/
theorem print_run {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d)
    (dtail out B Ub m0 : List Bool) (cap1 cap2 : ℕ) (hm0 : m0.length = L)
    (hUb : overlay (frame (List.replicate L true)) Ub = Ub) (hcap1 : armCost L + 2 ≤ cap1)
    (hcap2 : recInnerCost (List.replicate L false) ≤ cap2) :
    Step (printM E) (printCost E d)
      (Fin.addCases (bh (out ++ printedAt f L d 0).length) (fun _ => 0))
      (Fin.addCases (outerBank f L d dtail out B Ub m0 cap1 cap2 0).tapes E.data)
      (Fin.addCases (bh (out ++ Rec.polyWord (Interp.interpPrint f L d)).length) (fun _ => 0))
      (Fin.addCases { outerBank f L d dtail out B Ub m0 cap1 cap2 (Interp.goods L d).length with
          o := overlay (out ++ Rec.polyWord (Interp.interpPrint f L d)) B }.tapes E.data) := by
  have hW := Block.WhileBody.run ({
    body := outerBody E
    tape := Fin.castAdd E.t 5
    bound := (Interp.goods L d).length
    H := fun k => Fin.addCases (bh (out ++ printedAt f L d k).length) (fun _ => 0)
    A := fun k => Fin.addCases (outerBank f L d dtail out B Ub m0 cap1 cap2 k).tapes E.data
    cost := outerPassCost E d
    step := by
      intro k hk
      exact outerBody_step E d hd dtail out B Ub m0 cap1 cap2 hm0 hUb hcap1 hcap2 k hk
    cont := by
      intro k hk
      simp [Fin.addCases_left, outerBank, Bank.tapes, bh, readTapeBit, hk]
    halt := by
      simp [Fin.addCases_left, outerBank, Bank.tapes, bh, readTapeBit] } : Block.WhileBody (14 + E.t) _)
  have hput := lift_stage (put_stage false (outerBank f L d dtail out B Ub m0 cap1 cap2 (Interp.goods L d).length)
    (out ++ printedAt f L d (Interp.goods L d).length) B rfl) E.data
  have t := Step.seq hW hput
  have ef : out ++ printedAt f L d (Interp.goods L d).length ++ [false] = out ++ Rec.polyWord (Interp.interpPrint f L d) := by
    rw [List.append_assoc, printedAt_full f L d hd]
  rw [ef] at t
  refine t.enlarge (le_of_eq ?_)
  simp [printCost, Block.WhileBody.rest]

end NearCubicWires.WireExponent3_5.ListMachine.Print
