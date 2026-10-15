import Proof.Wire_3_5.ListMachinePrintInner

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Slot maps -/

def sFI : Fin 3 → Fin 14 := ![4, 3, 2]
theorem sFI_inj : Function.Injective sFI := by decide
def pFI : Fin 14 → Option (Fin 3) :=
  ![none, none, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none]
theorem pick_sFI : ∀ i, RecoveryFocus.pick sFI i = pFI i := by pick_table sFI_inj

def sRA : Fin 3 → Fin 14 := ![2, 3, 4]
theorem sRA_inj : Function.Injective sRA := by decide
def pRA : Fin 14 → Option (Fin 3) :=
  ![none, none, some 0, some 1, some 2, none, none, none, none, none, none, none, none, none]
theorem pick_sRA : ∀ i, RecoveryFocus.pick sRA i = pRA i := by pick_table sRA_inj

def sPA : Fin 3 → Fin 14 := ![6, 3, 2]
theorem sPA_inj : Function.Injective sPA := by decide
def pPA : Fin 14 → Option (Fin 3) :=
  ![none, none, some 2, some 1, none, none, some 0, none, none, none, none, none, none, none]
theorem pick_sPA : ∀ i, RecoveryFocus.pick sPA i = pPA i := by pick_table sPA_inj

def sXDPL : Fin 4 → Fin 14 := ![0, 9, 6, 12]
theorem sXDPL_inj : Function.Injective sXDPL := by decide
def pXDPL : Fin 14 → Option (Fin 4) :=
  ![some 0, none, none, none, none, none, some 2, none, none, some 1, none, none, some 3, none]
theorem pick_sXDPL : ∀ i, RecoveryFocus.pick sXDPL i = pXDPL i := by pick_table sXDPL_inj

def sMXL : Fin 3 → Fin 14 := ![7, 0, 12]
theorem sMXL_inj : Function.Injective sMXL := by decide
def pMXL : Fin 14 → Option (Fin 3) :=
  ![some 1, none, none, none, none, none, none, some 0, none, none, none, none, some 2, none]
theorem pick_sMXL : ∀ i, RecoveryFocus.pick sMXL i = pMXL i := by pick_table sMXL_inj

def sXML : Fin 3 → Fin 14 := ![0, 7, 12]
theorem sXML_inj : Function.Injective sXML := by decide
def pXML : Fin 14 → Option (Fin 3) :=
  ![some 0, none, none, none, none, none, none, some 1, none, none, none, none, some 2, none]
theorem pick_sXML : ∀ i, RecoveryFocus.pick sXML i = pXML i := by pick_table sXML_inj

def sXZL : Fin 3 → Fin 14 := ![0, 8, 12]
theorem sXZL_inj : Function.Injective sXZL := by decide
def pXZL : Fin 14 → Option (Fin 3) :=
  ![some 0, none, none, none, none, none, none, none, some 1, none, none, none, some 2, none]
theorem pick_sXZL : ∀ i, RecoveryFocus.pick sXZL i = pXZL i := by pick_table sXZL_inj

def sXZFL : Fin 4 → Fin 14 := ![0, 8, 5, 12]
theorem sXZFL_inj : Function.Injective sXZFL := by decide
def pXZFL : Fin 14 → Option (Fin 4) :=
  ![some 0, none, none, none, none, some 2, none, none, some 1, none, none, none, some 3, none]
theorem pick_sXZFL : ∀ i, RecoveryFocus.pick sXZFL i = pXZFL i := by pick_table sXZFL_inj

/-! ## The operations -/

def constOp (c : Bool) (_ _ _ : Bool) : Bool := c

/-- The lowest-one mask of the operand, the target's old content ignored. -/
def gL' (_ x s : Bool) : Bool := x && !s
def hL' (_ x s : Bool) : Bool := s || x

theorem ripple_gL' (m xs : List Bool) (hl : m.length = xs.length) (c : Bool) :
    Block.ripple gL' hL' c m xs = Block.ripple Interp.gL Interp.hL c xs xs := by
  induction m generalizing xs c with
  | nil =>
    cases xs with
    | nil => rfl
    | cons x xs => simp at hl
  | cons a m ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      simp only [Block.ripple, gL', hL', Interp.gL, Interp.hL]
      rw [ih xs (by simpa using hl)]

theorem ripple_length (g h : Bool → Bool → Bool → Bool) (c : Bool) (u v : List Bool) (hl : u.length = v.length) :
    (Block.ripple g h c u v).length = u.length := by
  induction u generalizing v c with
  | nil => cases v <;> rfl
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v => simp [Block.ripple, ih _ v (by simpa using hl)]

theorem sw_length (d : ℕ) (xs : List Bool) : (Interp.sw d xs).length = xs.length := by
  unfold Interp.sw
  split_ifs
  · rw [ripple_length _ _ _ _ _ (ripple_length _ _ _ _ _ rfl).symm]
  · rw [ripple_length _ _ _ _ _ (by simp)]

/-! ## The stages -/

noncomputable def printBr := Block.branchM (3 : Fin 14) (RecoveryFocus.machine sRec recM) (Block.idle 14)
noncomputable def resetAM := RecoveryFocus.machine sAR (GF2.CellOp.machine (constOp false))
noncomputable def resetRM := RecoveryFocus.machine sRA (GF2.CellOp.machine (constOp false))
noncomputable def resetPFM := RecoveryFocus.machine sPA (GF2.CellOp.machine (constOp false))
noncomputable def popM := RecoveryFocus.machine sXDPL (MaskedReset.machine PopEq.machine selTTF)
noncomputable def lowM :=
  RecoveryFocus.machine sMXL (MaskedReset.machine (Block.RippleIn.machine gL' hL' false) selTT)
noncomputable def addBr := Block.branchM (6 : Fin 14)
  (RecoveryFocus.machine sXML (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 false) selTT))
  (RecoveryFocus.machine sXZL (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 true) selTT))
noncomputable def foM := RecoveryFocus.machine sXZFL (MaskedReset.machine (Block.FoldCell.machine orFold false) selTTF)

/-- What a pass prints for the support of `xs` with coefficient `c`. -/
def pr (c : Bool) (xs : List Bool) : List Bool := if c then Rec.recW (Interp.supp xs) else []

theorem printBr_step (b : Bank) (xs Ub oo B : List Bool) (capU capX : ℕ) (c : Bool)
    (hx : b.x = frame xs) (hu : b.u = Ub) (ho : b.o = overlay oo B) (ha : b.a = [c])
    (h1 : b.l1 = List.replicate capU false) (h2 : b.l2 = List.replicate capX false)
    (hUb : overlay (frame (List.replicate xs.length true)) Ub = Ub)
    (hcapU : armCost xs.length + 2 ≤ capU) (hcapX : recInnerCost xs ≤ capX) :
    Step printBr (2 * recInnerCost xs + 2 + 2) (bh oo.length) b.tapes
      (bh (oo ++ pr c xs).length) { b with o := overlay (oo ++ pr c xs) B }.tapes := by
  cases c
  · have h := Block.branch_false (3 : Fin 14) (RecoveryFocus.machine sRec recM) (idle_step (bh oo.length) b.tapes)
      (by simp [Bank.tapes, ha, bh, readTapeBit])
    refine (h.congr ?_ ?_).enlarge (by omega)
    · simp [pr]
    · have e : ({ b with o := overlay (oo ++ pr false xs) B } : Bank) = b := by
        simp [pr, ← ho]
      rw [e]
  · have h := Block.branch_true (3 : Fin 14) (Block.idle 14)
      (rec_stage b xs Ub oo B capU capX hx hu ho h1 h2 hUb hcapU hcapX)
      (by simp [Bank.tapes, ha, bh, readTapeBit])
    exact h

theorem reset_step (s : Fin 3 → Fin 14) (hs : Function.Injective s) (o : ℕ) (b b' : Bank) (x y z : Bool)
    (hH : ∀ j, bh o (s j) = 0) (hA : ∀ j, b.tapes (s j) = ![[x], [y], [z]] j)
    (hb : RecoveryRootRound.install s b.tapes ![[false], [y], [z]] = b'.tapes) :
    Step (RecoveryFocus.machine s (GF2.CellOp.machine (constOp false))) 1 (bh o) b.tapes (bh o) b'.tapes :=
  cell_step (constOp false) s hs o b b' x y z hH hA hb

theorem pop_step (b : Bank) (o : ℕ) (xs : List Bool) (d : ℕ) (dtail : List Bool) (pf0 : Bool) (cap : ℕ)
    (hx : b.x = frame xs) (hd : b.d = List.replicate d true ++ false :: dtail) (hpf : b.pf = [pf0])
    (hl : b.l1 = List.replicate cap false) (hpop : Interp.pop xs ≤ d) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step popM (2 * (2 * xs.length + 1) + 2) (bh o) b.tapes (bh o)
      { b with pf := [decide (Interp.pop xs = d)] }.tapes :=
  pop_stage sXDPL sXDPL_inj o b _ xs d dtail pf0 hpop cap hcap (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hd
        · exact hpf
        · exact hl)
    (by rw [install_of_pick sXDPL pXDPL pick_sXDPL]
        funext i; fin_cases i <;> simp [pXDPL, Bank.tapes, hx, hd, hl])

theorem low_step (b : Bank) (o : ℕ) (xs m : List Bool) (cap : ℕ) (hm : b.m = frame m) (hx : b.x = frame xs)
    (hl : b.l1 = List.replicate cap false) (hmL : m.length = xs.length) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step lowM (2 * (2 * m.length + 1) + 2) (bh o) b.tapes (bh o)
      { b with m := frame (Block.ripple Interp.gL Interp.hL false xs xs) }.tapes :=
  ripple_stage gL' hL' false sMXL sMXL_inj o b _ m xs hmL cap (by rw [hmL]; exact hcap)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hm
        · exact hx
        · exact hl)
    (by rw [install_of_pick sMXL pMXL pick_sMXL, ripple_gL' m xs hmL]
        funext i; fin_cases i <;> simp [pMXL, Bank.tapes, hx, hl])

theorem addBr_step (b : Bank) (o : ℕ) (xs : List Bool) (d : ℕ) (cap : ℕ) (hx : b.x = frame xs)
    (hm : b.m = frame (Block.ripple Interp.gL Interp.hL false xs xs))
    (hz : b.z = frame (List.replicate xs.length false)) (hpf : b.pf = [decide (Interp.pop xs = d)])
    (hl : b.l1 = List.replicate cap false) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step addBr (2 * (2 * xs.length + 1) + 2 + 2) (bh o) b.tapes (bh o)
      { b with x := frame (Interp.sw d xs) }.tapes := by
  have hml : (Block.ripple Interp.gL Interp.hL false xs xs).length = xs.length := ripple_length _ _ _ _ _ rfl
  by_cases hp : Interp.pop xs = d
  · have hs := ripple_stage Block.sum3 Block.carry3 false sXML sXML_inj o b { b with x := frame (Interp.sw d xs) }
      xs _ hml.symm cap hcap (by intro j; fin_cases j <;> rfl)
      (by intro j; fin_cases j
          · exact hx
          · exact hm
          · exact hl)
      (by rw [install_of_pick sXML pXML pick_sXML]
          unfold Interp.sw; rw [if_pos hp]
          funext i; fin_cases i <;> simp [pXML, Bank.tapes, hm, hl])
    exact Block.branch_true (6 : Fin 14) _ hs (by simp [Bank.tapes, hpf, hp, bh, readTapeBit])
  · have hs := ripple_stage Block.sum3 Block.carry3 true sXZL sXZL_inj o b { b with x := frame (Interp.sw d xs) }
      xs (List.replicate xs.length false) (by simp) cap hcap (by intro j; fin_cases j <;> rfl)
      (by intro j; fin_cases j
          · exact hx
          · exact hz
          · exact hl)
      (by rw [install_of_pick sXZL pXZL pick_sXZL]
          unfold Interp.sw; rw [if_neg hp]
          funext i; fin_cases i <;> simp [pXZL, Bank.tapes, hz, hl])
    exact Block.branch_false (6 : Fin 14) _ hs (by simp [Bank.tapes, hpf, hp, bh, readTapeBit])

theorem fo_step (b : Bank) (o : ℕ) (ys : List Bool) (fo0 : Bool) (cap : ℕ) (hx : b.x = frame ys)
    (hz : b.z = frame (List.replicate ys.length false)) (hfo : b.fo = [fo0]) (hl : b.l1 = List.replicate cap false)
    (hcap : 2 * ys.length + 1 ≤ cap) :
    Step foM (2 * (2 * ys.length + 1) + 2) (bh o) b.tapes (bh o) { b with fo := [ys.any id] }.tapes :=
  fold_stage orFold false sXZFL sXZFL_inj o b _ ys (List.replicate ys.length false) fo0 (by simp) cap hcap
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hz
        · exact hfo
        · exact hl)
    (by rw [install_of_pick sXZFL pXZFL pick_sXZFL, foldBits_orFold _ _ (by simp)]
        funext i; fin_cases i <;> simp [pXZFL, Bank.tapes, hx, hz, hl])

/-- The rest of one pass, after the coefficient is known. -/
noncomputable def outerRest := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine printBr resetAM) resetRM) popM) lowM) addBr)
  resetPFM) foM

def outerRestCost (xs : List Bool) : ℕ :=
  (2 * recInnerCost xs + 2 + 2) + 1 + 1 + 1 + 1 + 1 + (2 * (2 * xs.length + 1) + 2) + 1 +
    (2 * (2 * xs.length + 1) + 2) + 1 + (2 * (2 * xs.length + 1) + 2 + 2) + 1 + 1 + 1 +
    (2 * (2 * xs.length + 1) + 2)

theorem outerRest_step (b : Bank) (xs Ub oo B m dtail : List Bool) (d cap1 cap2 : ℕ) (c r0 fi0 pf0 fo0 : Bool)
    (hx : b.x = frame xs) (hr : b.r = [r0]) (ha : b.a = [c]) (hfi : b.fi = [fi0]) (hpf : b.pf = [pf0])
    (hfo : b.fo = [fo0]) (hm : b.m = frame m) (hmL : m.length = xs.length)
    (hz : b.z = frame (List.replicate xs.length false)) (hd : b.d = List.replicate d true ++ false :: dtail)
    (ho : b.o = overlay oo B) (hu : b.u = Ub) (hl1 : b.l1 = List.replicate cap1 false)
    (hl2 : b.l2 = List.replicate cap2 false) (hUb : overlay (frame (List.replicate xs.length true)) Ub = Ub)
    (hpop : Interp.pop xs ≤ d) (hcap1 : armCost xs.length + 2 ≤ cap1) (hcap2 : recInnerCost xs ≤ cap2) :
    Step outerRest (outerRestCost xs) (bh oo.length) b.tapes (bh (oo ++ pr c xs).length)
      { b with o := overlay (oo ++ pr c xs) B, a := [false], r := [false], pf := [false],
               m := frame (Block.ripple Interp.gL Interp.hL false xs xs), x := frame (Interp.sw d xs),
               fo := [(Interp.sw d xs).any id] }.tapes := by
  have hc1 : 2 * xs.length + 1 ≤ cap1 := le_trans (by simp [armCost]) hcap1
  set o' := (oo ++ pr c xs).length with ho'
  have s1 := printBr_step b xs Ub oo B cap1 cap2 c hx hu ho ha hl1 hl2 hUb hcap1 hcap2
  set b1 : Bank := { b with o := overlay (oo ++ pr c xs) B } with hb1
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
  · simp [outerRestCost, hmL, hsl]

end NearCubicWires.WireExponent3_5.ListMachine.Print
