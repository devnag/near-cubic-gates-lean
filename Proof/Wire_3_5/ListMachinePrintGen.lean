import Proof.Wire_3_5.ListMachinePrintLoop
import Proof.Wire_3_5.ListMachinePrintRecL

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-- **A record printer**: on tapes (bitmap, its own word, output, log, log) it appends `recW (g (supp X))`. -/
structure RecSpec where
  s : ℕ
  machine : Machine 5 s
  g : List ℕ → List ℕ
  cost : List Bool → ℕ
  ok : List Bool → List Bool → ℕ → ℕ → Prop
  step : ∀ (xs Ub oo B : List Bool) (cap1 cap2 : ℕ), ok xs Ub cap1 cap2 →
    Step machine (cost xs) ![0, 0, oo.length, 0, 0]
      ![frame xs, Ub, overlay oo B, List.replicate cap1 false, List.replicate cap2 false]
      ![0, 0, (oo ++ Rec.recW (g (Interp.supp xs))).length, 0, 0]
      ![frame xs, Ub, overlay (oo ++ Rec.recW (g (Interp.supp xs))) B, List.replicate cap1 false,
        List.replicate cap2 false]

/-- The labelled record printer as a `RecSpec`. -/
noncomputable def recSpecL (labs : List ℕ) : RecSpec where
  s := _
  machine := recLM
  g := List.map (labOf labs)
  cost := fun xs => 2 * recInnerLCost xs labs + 2
  ok := fun xs Ub cap1 _ => xs.length ≤ labs.length ∧ (∃ tail, Ub = labs.flatMap Rec.atomCode ++ tail) ∧
    recInnerLCost xs labs ≤ cap1
  step := by
    rintro xs Ub oo B cap1 cap2 ⟨hl, ⟨tail, rfl⟩, hcap⟩
    exact recL_run xs labs tail oo B cap1 cap2 hl hcap

theorem rec_stageG (R : RecSpec) (b : Bank) (xs Ub oo B : List Bool) (capU capX : ℕ)
    (hx : b.x = frame xs) (hu : b.u = Ub) (ho : b.o = overlay oo B)
    (h1 : b.l1 = List.replicate capU false) (h2 : b.l2 = List.replicate capX false)
    (hok : R.ok xs Ub capU capX) :
    Step (RecoveryFocus.machine sRec R.machine) (R.cost xs) (bh oo.length) b.tapes
      (bh (oo ++ Rec.recW (R.g (Interp.supp xs))).length)
      { b with o := overlay (oo ++ Rec.recW (R.g (Interp.supp xs))) B }.tapes := by
  have h := dockRun (R.step xs Ub oo B capU capX hok) sRec sRec_inj (bh oo.length) b.tapes
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hu
        · exact ho
        · exact h1
        · exact h2)
  rw [dockH_of_pick sRec pRec pick_sRec, install_of_pick sRec pRec pick_sRec] at h
  generalize (oo ++ Rec.recW (R.g (Interp.supp xs))).length = n at h ⊢
  generalize overlay (oo ++ Rec.recW (R.g (Interp.supp xs))) B = w at h ⊢
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pRec, bh]
  · funext i; fin_cases i <;> simp [pRec, Bank.tapes, hx, hu, h1, h2]

/-- What a pass prints for the support of `xs` with coefficient `c`. -/
def prG (R : RecSpec) (c : Bool) (xs : List Bool) : List Bool := if c then Rec.recW (R.g (Interp.supp xs)) else []

noncomputable def printBrG (R : RecSpec) :=
  Block.branchM (3 : Fin 14) (RecoveryFocus.machine sRec R.machine) (Block.idle 14)

theorem printBrG_step (R : RecSpec) (b : Bank) (xs Ub oo B : List Bool) (capU capX : ℕ) (c : Bool)
    (hx : b.x = frame xs) (hu : b.u = Ub) (ho : b.o = overlay oo B) (ha : b.a = [c])
    (h1 : b.l1 = List.replicate capU false) (h2 : b.l2 = List.replicate capX false) (hok : R.ok xs Ub capU capX) :
    Step (printBrG R) (R.cost xs + 2) (bh oo.length) b.tapes
      (bh (oo ++ prG R c xs).length) { b with o := overlay (oo ++ prG R c xs) B }.tapes := by
  cases c
  · have h := Block.branch_false (3 : Fin 14) (RecoveryFocus.machine sRec R.machine) (idle_step (bh oo.length) b.tapes)
      (by simp [Bank.tapes, ha, bh, readTapeBit])
    refine (h.congr ?_ ?_).enlarge (by omega)
    · simp [prG]
    · have e : ({ b with o := overlay (oo ++ prG R false xs) B } : Bank) = b := by
        simp [prG, ← ho]
      rw [e]
  · have h := Block.branch_true (3 : Fin 14) (Block.idle 14)
      (rec_stageG R b xs Ub oo B capU capX hx hu ho h1 h2 hok)
      (by simp [Bank.tapes, ha, bh, readTapeBit])
    exact h

/-- The rest of one pass, after the coefficient is known. -/
noncomputable def outerRestG (R : RecSpec) := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine (printBrG R) resetAM) resetRM)
  popM) lowM) addBr) resetPFM) foM

def outerRestGCost (R : RecSpec) (xs : List Bool) : ℕ :=
  (R.cost xs + 2) + 1 + 1 + 1 + 1 + 1 + (2 * (2 * xs.length + 1) + 2) + 1 +
    (2 * (2 * xs.length + 1) + 2) + 1 + (2 * (2 * xs.length + 1) + 2 + 2) + 1 + 1 + 1 +
    (2 * (2 * xs.length + 1) + 2)

theorem outerRestG_step (R : RecSpec) (b : Bank) (xs Ub oo B m dtail : List Bool) (d cap1 cap2 : ℕ) (c r0 fi0 pf0 fo0 : Bool)
    (hx : b.x = frame xs) (hr : b.r = [r0]) (ha : b.a = [c]) (hfi : b.fi = [fi0]) (hpf : b.pf = [pf0])
    (hfo : b.fo = [fo0]) (hm : b.m = frame m) (hmL : m.length = xs.length)
    (hz : b.z = frame (List.replicate xs.length false)) (hd : b.d = List.replicate d true ++ false :: dtail)
    (ho : b.o = overlay oo B) (hu : b.u = Ub) (hl1 : b.l1 = List.replicate cap1 false)
    (hl2 : b.l2 = List.replicate cap2 false) (hok : R.ok xs Ub cap1 cap2)
    (hpop : Interp.pop xs ≤ d) (hc1 : 2 * xs.length + 1 ≤ cap1) :
    Step (outerRestG R) (outerRestGCost R xs) (bh oo.length) b.tapes (bh (oo ++ prG R c xs).length)
      { b with o := overlay (oo ++ prG R c xs) B, a := [false], r := [false], pf := [false],
               m := frame (Block.ripple Interp.gL Interp.hL false xs xs), x := frame (Interp.sw d xs),
               fo := [(Interp.sw d xs).any id] }.tapes := by
  set o' := (oo ++ prG R c xs).length with ho'
  have s1 := printBrG_step R b xs Ub oo B cap1 cap2 c hx hu ho ha hl1 hl2 hok
  set b1 : Bank := { b with o := overlay (oo ++ prG R c xs) B } with hb1
  have s2 := reset_step sAR sAR_inj o' b1 { b1 with a := [false] } c r0 fi0 (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact ha
        · exact hr
        · exact hfi)
    (by rw [install_of_pick sAR pAR pick_sAR]; funext i; fin_cases i <;> simp [pAR, Bank.tapes, hb1, hr, hfi])
  set b2 : Bank := { b1 with a := [false] } with hb2
  have s3 := reset_step sRA sRA_inj o' b2 { b2 with r := [false] } r0 false fi0 (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hr
        · rfl
        · exact hfi)
    (by rw [install_of_pick sRA pRA pick_sRA]; funext i; fin_cases i <;> simp [pRA, Bank.tapes, hb2, hb1, hfi])
  set b3 : Bank := { b2 with r := [false] } with hb3
  have s4 := pop_step b3 o' xs d dtail pf0 cap1 hx hd hpf hl1 hpop hc1
  set b4 : Bank := { b3 with pf := [decide (Interp.pop xs = d)] } with hb4
  have s5 := low_step b4 o' xs m cap1 hm hx hl1 hmL hc1
  set b5 : Bank := { b4 with m := frame (Block.ripple Interp.gL Interp.hL false xs xs) } with hb5
  have s6 := addBr_step b5 o' xs d cap1 hx rfl hz rfl hl1 hc1
  set b6 : Bank := { b5 with x := frame (Interp.sw d xs) } with hb6
  have s7 := reset_step sPA sPA_inj o' b6 { b6 with pf := [false] } (decide (Interp.pop xs = d)) false false
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
    (by rw [install_of_pick sPA pPA pick_sPA]; funext i; fin_cases i <;> simp [pPA, Bank.tapes, hb6, hb5, hb4, hb3,
          hb2, hb1])
  set b7 : Bank := { b6 with pf := [false] } with hb7
  have hsl := sw_length d xs
  have s8 := fo_step b7 o' (Interp.sw d xs) fo0 cap1 rfl (by rw [hsl]; exact hz) hfo hl1 (by rw [hsl]; exact hc1)
  have t := Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (Step.seq s1 s2) s3) s4) s5) s6) s7) s8
  refine (t.congr rfl ?_).enlarge (le_of_eq ?_)
  · funext i; fin_cases i <;> simp [Bank.tapes, hb7, hb6, hb5, hb4, hb3, hb2, hb1]
  · simp [outerRestGCost, hmL, hsl]

/-! ## The outer loop -/

/-- What the first `k` passes print. -/
def printedAtG (R : RecSpec) (f : List Bool → Bool) (L d k : ℕ) : List Bool :=
  (List.range k).flatMap fun i => prG R (Interp.subsetX f L (Interp.supp (xsAt L d i))) (xsAt L d i)

theorem printedAtG_succ (R : RecSpec) (f : List Bool → Bool) (L d k : ℕ) :
    printedAtG R f L d (k + 1) =
      printedAtG R f L d k ++ prG R (Interp.subsetX f L (Interp.supp (xsAt L d k))) (xsAt L d k) := by
  simp [printedAtG, List.range_succ, List.flatMap_append]

/-- One outer pass: raise the inner flag, the inner loop, print and step. -/
noncomputable def outerBodyG (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) :=
  Composition.machine (Composition.machine (RecoveryFocus.machine (Fin.castAdd E.t) setFIM)
    (StreamController.machine (innerBody E) (Fin.castAdd E.t 4)))
    (RecoveryFocus.machine (Fin.castAdd E.t) (outerRestG R))

/-- The bank before outer pass `k`. -/
def outerBankG (R : RecSpec) (f : List Bool → Bool) (L d : ℕ) (dtail out B Ub m0 : List Bool) (cap1 cap2 k : ℕ) :
    Bank where
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
  o := overlay (out ++ printedAtG R f L d k) B
  u := Ub
  l1 := List.replicate cap1 false
  l2 := List.replicate cap2 false

/-- The cost of outer pass `k`. -/
def outerPassGCost (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d k : ℕ) : ℕ :=
  1 + 1 + (2 ^ Interp.pop (xsAt L d k) * (innerPassCost E L + 2) + 1) + 1 + outerRestGCost R (xsAt L d k)

theorem outerBodyG_step (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d)
    (dtail out B Ub m0 : List Bool) (cap1 cap2 : ℕ) (hm0 : m0.length = L)
    (hok : ∀ xs : List Bool, xs.length = L → R.ok xs Ub cap1 cap2) (hc1 : 2 * L + 1 ≤ cap1)
    (k : ℕ) (hk : k < (Interp.goods L d).length) :
    Step (outerBodyG R E) (outerPassGCost R E d k)
      (Fin.addCases (bh (out ++ printedAtG R f L d k).length) (fun _ => 0))
      (Fin.addCases (outerBankG R f L d dtail out B Ub m0 cap1 cap2 k).tapes E.data)
      (Fin.addCases (bh (out ++ printedAtG R f L d (k + 1)).length) (fun _ => 0))
      (Fin.addCases (outerBankG R f L d dtail out B Ub m0 cap1 cap2 (k + 1)).tapes E.data) := by
  set b := outerBankG R f L d dtail out B Ub m0 cap1 cap2 k with hb
  set xs := xsAt L d k with hxs
  have hxl : xs.length = L := xsAt_length L d k
  have hc1' : 2 * xs.length + 1 ≤ cap1 := by rw [hxl]; exact hc1
  set o := (out ++ printedAtG R f L d k).length with ho
  -- raise the inner flag
  have s1 := lift_stage (cell_step (constOp true) sFI sFI_inj o b { b with fi := [true] } false false false
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
    (by rw [install_of_pick sFI pFI pick_sFI]; funext i; fin_cases i <;> simp [pFI, Bank.tapes, hb, outerBankG, constOp]))
    E.data
  -- the coefficient
  have s2 := inner_run E b o xs hxl cap1 rfl rfl hc1'
  rw [hxl] at s2
  have e2 : ({ b with t := frame (List.replicate L false), r := [false], a := [false], fi := [true] } : Bank) =
      { b with fi := [true] } := by simp [hb, outerBankG]
  rw [e2] at s2
  set c := Interp.subsetX f L (Interp.supp xs) with hc
  set r3 := rAt f xs (2 ^ Interp.pop xs) with hr3
  set b3 : Bank := { b with t := frame (List.replicate L false), r := [r3], a := [c], fi := [false] } with hb3
  -- print and step
  have s3 := lift_stage (outerRestG_step R b3 xs Ub (out ++ printedAtG R f L d k) B (mAt L d m0 k) dtail d cap1 cap2 c
    r3 false false (decide (k < (Interp.goods L d).length)) rfl rfl rfl rfl rfl rfl rfl
    (by rw [mAt_length L d m0 hm0, hxl]) (by rw [hxl]; rfl) rfl rfl rfl rfl rfl (hok xs hxl)
    (xsAt_pop L d hd k hk) hc1') E.data
  have t := Step.seq (Step.seq s1 s2) s3
  have eo : out ++ printedAtG R f L d k ++ prG R c xs = out ++ printedAtG R f L d (k + 1) := by
    rw [printedAtG_succ, List.append_assoc]
  rw [eo] at t
  set m3 := frame (Block.ripple Interp.gL Interp.hL false xs xs) with hm3
  set fo3 := [(Interp.sw d xs).any id] with hfo3
  have eb : ({ b3 with o := overlay (out ++ printedAtG R f L d (k + 1)) B, a := [false], r := [false], pf := [false],
                       m := m3, x := frame (Interp.sw d xs), fo := fo3 } : Bank) =
      outerBankG R f L d dtail out B Ub m0 cap1 cap2 (k + 1) := by
    simp only [hb3, hb, hm3, hfo3, hxs, outerBankG, xsAt_succ, fo_next L d hd k hk, mAt]
  rw [eb] at t
  refine t.enlarge (le_of_eq ?_)
  simp [outerPassGCost, hxs]

/-- **What the printer prints**: the word of the interpolation print. -/
theorem printedAtG_full (R : RecSpec) (f : List Bool → Bool) (L d : ℕ) (hd : 1 ≤ d) :
    printedAtG R f L d (Interp.goods L d).length ++ [false] =
      Rec.polyWord ((Interp.interpPrint f L d).map R.g) := by
  unfold Rec.polyWord Interp.interpPrint
  rw [List.flatMap_map, Interp.monos_eq_goods, filter_map_flatMap, ← flatMap_range_getD _ 0]
  congr 1
  unfold printedAtG
  apply Interp.flatMap_congr_mem
  intro i hi
  have hi' : i < (Interp.goods L d).length := List.mem_range.mp hi
  rw [xsAt_goods L d hd i hi', List.getD_eq_getElem _ _ hi']
  simp [prG]

/-- **The interpolation printer** on the evaluator of `f`. -/
noncomputable def printMG (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) :=
  Composition.machine (StreamController.machine (outerBodyG R E) (Fin.castAdd E.t 5))
    (RecoveryFocus.machine (Fin.castAdd E.t) (RecoveryFocus.machine sOut (Put.machine false)))

/-- The printer's cost: the passes over the supports, then the terminator. -/
def printGCost (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) : ℕ :=
  ((List.range (Interp.goods L d).length).map fun k => outerPassGCost R E d k + 2).sum + 1 + 1 + 1

/-- **The printer**: from the bank with the zero support, the unary bound `1^d 0`, the position word
`frame (1^L)`, the output cursor at `out` and the evaluator's tapes, the output receives
`polyWord (Interp.interpPrint f L d)`, the reduced expansion of `f` in degree `≤ d`. -/
theorem print_runG (R : RecSpec) {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (d : ℕ) (hd : 1 ≤ d)
    (dtail out B Ub m0 : List Bool) (cap1 cap2 : ℕ) (hm0 : m0.length = L)
    (hok : ∀ xs : List Bool, xs.length = L → R.ok xs Ub cap1 cap2) (hc1 : 2 * L + 1 ≤ cap1) :
    Step (printMG R E) (printGCost R E d)
      (Fin.addCases (bh (out ++ printedAtG R f L d 0).length) (fun _ => 0))
      (Fin.addCases (outerBankG R f L d dtail out B Ub m0 cap1 cap2 0).tapes E.data)
      (Fin.addCases (bh (out ++ Rec.polyWord ((Interp.interpPrint f L d).map R.g)).length) (fun _ => 0))
      (Fin.addCases { outerBankG R f L d dtail out B Ub m0 cap1 cap2 (Interp.goods L d).length with
          o := overlay (out ++ Rec.polyWord ((Interp.interpPrint f L d).map R.g)) B }.tapes E.data) := by
  have hW := Block.WhileBody.run ({
    body := outerBodyG R E
    tape := Fin.castAdd E.t 5
    bound := (Interp.goods L d).length
    H := fun k => Fin.addCases (bh (out ++ printedAtG R f L d k).length) (fun _ => 0)
    A := fun k => Fin.addCases (outerBankG R f L d dtail out B Ub m0 cap1 cap2 k).tapes E.data
    cost := outerPassGCost R E d
    step := by
      intro k hk
      exact outerBodyG_step R E d hd dtail out B Ub m0 cap1 cap2 hm0 hok hc1 k hk
    cont := by
      intro k hk
      simp [Fin.addCases_left, outerBankG, Bank.tapes, bh, readTapeBit, hk]
    halt := by
      simp [Fin.addCases_left, outerBankG, Bank.tapes, bh, readTapeBit] } : Block.WhileBody (14 + E.t) _)
  have hput := lift_stage (put_stage false (outerBankG R f L d dtail out B Ub m0 cap1 cap2 (Interp.goods L d).length)
    (out ++ printedAtG R f L d (Interp.goods L d).length) B rfl) E.data
  have t := Step.seq hW hput
  have ef : out ++ printedAtG R f L d (Interp.goods L d).length ++ [false] =
      out ++ Rec.polyWord ((Interp.interpPrint f L d).map R.g) := by
    rw [List.append_assoc, printedAtG_full R f L d hd]
  rw [ef] at t
  refine t.enlarge (le_of_eq ?_)
  simp [printGCost, Block.WhileBody.rest]

end NearCubicWires.WireExponent3_5.ListMachine.Print
