import Proof.Wire_3_5.PrimAsmShellDLayout
import Proof.Wire_3_5.ListMachineRowLoad
import Proof.Rows.CapReader
import Proof.Packets.PacketsSetupDriver

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.WireExponent3_5.PrimAsm.Shell (install_eq dockH_eq)

section Boot
variable {x D D1 D2 : ℕ}

theorem cs_eq_iff (a b : Fin 161) : cs (x := x) (D := D) (D1 := D1) (D2 := D2) a = cs b ↔ a = b := by
  constructor
  · intro h
    exact sk_inj x (sTape_inj (cT_inj h))
  · intro h
    rw [h]

theorem eT_ne_cs (k : Fin (UnaryCalc.tapes D1)) (a : Fin 161) : e1T (x := x) (D := D) (D2 := D2) k ≠ cs a := by
  apply ne_of_val
  have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) a
  rw [e1T_val]
  omega

theorem wT_ne_cs (j : Fin (Scrub.wk D)) (a : Fin 161) : wT (x := x) (D1 := D1) (D2 := D2) j ≠ cs a := by
  apply ne_of_val
  have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) a
  rw [wT_val]
  omega

theorem kT_ne_cs (a : Fin 161) : kT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ cs a := by
  apply ne_of_val
  have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) a
  rw [kT_val]
  omega

theorem lgT_ne_cs (a : Fin 161) : lgT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ cs a := by
  apply ne_of_val
  have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) a
  rw [lgT_val]
  omega

theorem drT_ne_cs (a : Fin 161) : drT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ cs a := by
  apply ne_of_val
  have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) a
  rw [drT_val]
  omega

/-- The writer's entry bank: `frame w` on the request stream, all else blank. -/
def B0 (w : List Bool) : Fin (STd x D D1 D2) → List Bool := fun i => if i = cs 0 then frame w else []

/-! ## Stage 1: the request, unframed -/

/-- Request, raw copy, log. -/
def slots1 : Fin 3 → Fin (STd x D D1 D2) := ![cs 0, cs 3, cs 4]

theorem slots1_inj : Function.Injective (slots1 (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [slots1, cs_eq_iff]

noncomputable def M1 (x D D1 D2 : ℕ) := RecoveryFocus.machine (slots1 (x := x) (D := D) (D1 := D1) (D2 := D2))
  (MaskedReset.machine Unframe.machine (fun _ => true))

/-- After stage 1: the raw request on stream `3`, the log on stream `4`. -/
def B1 (w : List Bool) (m1 : ℕ) : Fin (STd x D D1 D2) → List Bool :=
  fun i => if i = cs 3 then w else if i = cs 4 then List.replicate m1 false else B0 w i

theorem st1 (w : List Bool) : ∃ m1, Step (M1 x D D1 D2) (2 * (2 * w.length + 1) + 2) (fun _ => 0) (B0 w) (fun _ => 0)
    (B1 w m1) := by
  obtain ⟨m1, h⟩ := maskBlank (Unframe.run [] w [] [] []) (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have d := Rec.dockRun h (slots1 (x := x) (D := D) (D1 := D1) (D2 := D2)) slots1_inj (fun _ => 0) (B0 w)
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j
      fin_cases j
      · change B0 w (cs 0) = [] ++ frame w ++ []
        simp [B0]
      · change B0 w (cs 3) = overlay [] []
        simp [B0, cs_eq_iff, overlay_nil]
      · change B0 w (cs 4) = List.replicate 0 false
        simp [B0, cs_eq_iff])
  refine ⟨m1, d.congr ?_ ?_⟩
  · exact dockH_eq _ slots1_inj _ _ _ (by intro j; fin_cases j <;> rfl) (fun _ _ => rfl)
  · refine install_eq _ slots1_inj _ _ _ ?_ ?_
    · intro j
      fin_cases j
      · change B1 w m1 (cs 0) = [] ++ frame w ++ []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 3) = overlay ([] ++ w) []
        simp [B1, overlay_nil]
      · change B1 w m1 (cs 4) = List.replicate m1 false
        simp [B1, cs_eq_iff]
    · intro i hi
      have h1 : i ≠ cs 3 := fun e => hi 1 e.symm
      have h2 : i ≠ cs 4 := fun e => hi 2 e.symm
      simp [B1, h1, h2]

theorem cs_ne_eT (k : Fin (UnaryCalc.tapes D1)) (a : Fin 161) : cs a ≠ e1T (x := x) (D := D) (D2 := D2) k :=
  fun e => eT_ne_cs k a e.symm

theorem cs_ne_wT (j : Fin (Scrub.wk D)) (a : Fin 161) : cs a ≠ wT (x := x) (D1 := D1) (D2 := D2) j :=
  fun e => wT_ne_cs j a e.symm

theorem eT_ne_wT (k : Fin (UnaryCalc.tapes D1)) (j : Fin (Scrub.wk D)) : e1T (x := x) (D := D) (D2 := D2) k ≠ wT j := by
  apply ne_of_val
  rw [e1T_val, wT_val]
  have := j.isLt
  omega

theorem wT_ne_eT (k : Fin (UnaryCalc.tapes D1)) (j : Fin (Scrub.wk D)) : wT j ≠ e1T (x := x) (D := D) (D2 := D2) k :=
  fun e => eT_ne_wT k j e.symm

/-! ## Stage 2: `1^n`, twice -/

/-- The reader's tapes: the raw request, seven scratch streams, the bound's run input, the calc input, one scratch
stream (the template), the log. -/
def capSlots : Fin 12 → Fin (STd x D D1 D2) :=
  ![cs 3, cs 5, cs 6, cs 7, cs 8, cs 9, cs 10, cs 11, e1T (UnaryCalc.inputTape D1),
    wT (Fin.castAdd 1 (UnaryCalc.inputTape D)), cs 12, cs 13]

theorem capSlots_inj : Function.Injective (capSlots (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [capSlots, cs_eq_iff, eT_ne_cs, wT_ne_cs, cs_ne_eT, cs_ne_wT, eT_ne_wT, wT_ne_eT]

noncomputable def M2 (x D D1 D2 : ℕ) := RecoveryFocus.machine (capSlots (x := x) (D := D) (D1 := D1) (D2 := D2))
  (MaskedReset.machine CapWidthReader.machine (fun _ => true))

theorem st2 (n : ℕ) (sfx w : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx) (m1 : ℕ) :
    ∃ B2 : Fin (STd x D D1 D2) → List Bool,
      Step (M2 x D D1 D2) (2 * (8 * n + 20 * natBitLength n + 17) + 2) (fun _ => 0) (B1 w m1) (fun _ => 0) B2 ∧
      B2 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true ∧
      B2 (wT (Fin.castAdd 1 (UnaryCalc.inputTape D))) = List.replicate n true ∧
      ∀ i, (∀ j, capSlots j ≠ i) → B2 i = B1 w m1 i := by
  obtain ⟨H, A, h, hout⟩ := CapWidthReader.natural_run [] sfx n
  obtain ⟨_, _, h8, _, h9, _, _, _⟩ := hout
  obtain ⟨m2, hm⟩ := maskBlank h (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have d := Rec.dockRun hm (capSlots (x := x) (D := D) (D1 := D1) (D2 := D2)) capSlots_inj (fun _ => 0) (B1 w m1)
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j
      fin_cases j
      · change B1 w m1 (cs 3) = [] ++ RepairRepresentation.natWord n ++ sfx
        simp [B1, hw]
      · change B1 w m1 (cs 5) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 6) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 7) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 8) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 9) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 10) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 11) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (e1T (UnaryCalc.inputTape D1)) = []
        simp [B1, B0, eT_ne_cs]
      · change B1 w m1 (wT (Fin.castAdd 1 (UnaryCalc.inputTape D))) = []
        simp [B1, B0, wT_ne_cs]
      · change B1 w m1 (cs 12) = []
        simp [B1, B0, cs_eq_iff]
      · change B1 w m1 (cs 13) = List.replicate 0 false
        simp [B1, B0, cs_eq_iff])
  refine ⟨_, d.congr (dockH_eq _ capSlots_inj _ _ _ (by intro j; fin_cases j <;> rfl) (fun _ _ => rfl)) rfl,
    ?_, ?_, ?_⟩
  · change install capSlots (B1 w m1) _ (capSlots 8) = _
    rw [install_slot _ capSlots_inj]
    exact h8
  · change install capSlots (B1 w m1) _ (capSlots 9) = _
    rw [install_slot _ capSlots_inj]
    exact h9
  · intro i hi
    exact install_other _ _ _ _ hi

/-! ## Stage 3: the loop bound `b = C₁(n+1)^{D₁}` -/

noncomputable def M3 (x D D1 D2 C1 : ℕ) := RecoveryFocus.machine (e1T (x := x) (D := D) (D1 := D1) (D2 := D2))
  (PCPSerializerCapacity.Power.machine D1 C1)

theorem st3 (C1 n : ℕ) (Bin : Fin (STd x D D1 D2) → List Bool)
    (hin : ∀ k, Bin (e1T k) = RepairSource.ProjectionNormalization.DimensionPolynomial.input D1 n k) :
    ∃ out : Fin (UnaryCalc.tapes D1) → List Bool,
      Step (M3 x D D1 D2 C1) (PCPSerializerCapacity.Power.budget D1 C1 n) (fun _ => 0) Bin (fun _ => 0)
        (install e1T Bin out) ∧ out (UnaryCalc.outputTape D1) = List.replicate (UnaryCalc.value D1 C1 n) true ∧
        out (UnaryCalc.inputTape D1) = List.replicate n true := by
  obtain ⟨out, h, hi, ho⟩ := UnaryCalc.poly_step D1 C1 n
  have d := Rec.dockRun h (e1T (x := x) (D := D) (D1 := D1) (D2 := D2)) e1T_inj (fun _ => 0) Bin (fun _ => rfl) hin
  exact ⟨out, d.congr (dockH_eq _ e1T_inj _ _ _ (fun _ => rfl) (fun _ _ => rfl)) rfl, ho, hi⟩

/-! ## Stage 4: the counter `word b` -/

theorem eTo_ne_kT : e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.outputTape D1) ≠ kT := by
  apply ne_of_val
  rw [e1T_val, kT_val]
  omega

noncomputable def M4 (x D D1 D2 : ℕ) := RecoveryFocus.machine
  ![e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.outputTape D1), kT] (PacketsGlue.Stamp.machine 0)

theorem st4 (b : ℕ) (Bin : Fin (STd x D D1 D2) → List Bool)
    (hP : Bin (e1T (UnaryCalc.outputTape D1)) = List.replicate b true) (hK : Bin kT = []) :
    Step (M4 x D D1 D2) (2 * b + 3) (fun _ => 0) Bin (fun _ => 0)
      (fun i => if i = e1T (UnaryCalc.outputTape D1) then List.replicate b true else
        if i = kT then RepairSource.VerifierDecoding.CompareMachine.word b else Bin i) := by
  have d := Rec.dockRun (PacketsGlue.Stamp.run 0 b) ![e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.outputTape D1), kT]
    (pair_inj eTo_ne_kT) (fun _ => 0) Bin (by intro j; fin_cases j <;> rfl)
    (by
      intro j
      fin_cases j
      · exact hP
      · exact hK)
  refine d.congr (dockH_eq _ (pair_inj eTo_ne_kT) _ _ _ (by intro j; fin_cases j <;> rfl) (fun _ _ => rfl)) ?_
  rw [install_pair eTo_ne_kT]
  rfl

/-! ## Stage 5: `OUT := [false]`, the counter head to `1` -/

def act5 (x D D1 D2 : ℕ) : Prog (STd x D D1 D2) := .act (writeAt (cs 1) false) (moveAt kT .right)

theorem st5 (Bin : Fin (STd x D D1 D2) → List Bool) (hO : Bin (cs 1) = []) :
    Step (act5 x D D1 D2).compile 1 (fun _ => 0) Bin (fun i => if i = kT then 1 else 0)
      (fun i => if i = cs 1 then [false] else Bin i) := by
  have h := act_step (⟨fun _ => 0, Bin⟩ : Bank (STd x D D1 D2)) (writeAt (cs 1) false) (moveAt kT .right)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = kT
    · subst hi
      simp [Bank.act, moveAt, HeadMove.apply]
    · simp [Bank.act, moveAt, hi, HeadMove.apply]
  · funext i
    by_cases hi : i = cs 1
    · subst hi
      simp [Bank.act, writeAt, hO, writeTapeBit]
    · simp [Bank.act, writeAt, hi]

/-! ## The boot as one run -/

/-- The value table of the reader's slots. -/
def capVal (x D : ℕ) : Fin 12 → ℕ := ![4, 6, 7, 8, 9, 10, 11, 12, TT x + 1 + Scrub.wk D + 3, TT x + 1, 13, 14]

theorem capSlots_val (j : Fin 12) : (capSlots (x := x) (D := D) (D1 := D1) (D2 := D2) j).val = capVal x D j := by
  fin_cases j <;> rfl

theorem capSlots_ne (i : Fin (STd x D D1 D2)) (h : ∀ j, capVal x D j ≠ i.val) (j : Fin 12) : capSlots j ≠ i :=
  fun e => h j (by rw [← e, capSlots_val])

theorem eT_ne_lt (i : Fin (STd x D D1 D2)) (h : i.val < TT x + 1 + Scrub.wk D + 3) (k : Fin (UnaryCalc.tapes D1)) :
    e1T k ≠ i := by
  apply ne_of_val
  rw [e1T_val]
  omega

theorem cs_ne_kT (a : Fin 161) : cs a ≠ kT (x := x) (D := D) (D1 := D1) (D2 := D2) := fun e => kT_ne_cs a e.symm

noncomputable def bootM (x D D1 D2 C1 : ℕ) := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (M1 x D D1 D2) (M2 x D D1 D2)) (M3 x D D1 D2 C1)) (M4 x D D1 D2)) (act5 x D D1 D2).compile

/-- The boot's cost: the five stages and four bridges. -/
def bootCost (w : List Bool) (n D1 C1 : ℕ) : ℕ :=
  2 * (2 * w.length + 1) + 2 + 1 + (2 * (8 * n + 20 * natBitLength n + 17) + 2) + 1 +
    PCPSerializerCapacity.Power.budget D1 C1 n + 1 + (2 * UnaryCalc.value D1 C1 n + 3) + 1 + 1

/-- **The boot**: from the writer's entry bank to the loop's entry data (request kept, `OUT = [false]`, unit counter
blank, workspace `Scrub.calcIn D n`, log and driver blank, counter `word b`, heads `0` but the counter's `1`). -/
theorem boot_step (w sfx : List Bool) (n C1 : ℕ) (hw : w = RepairRepresentation.natWord n ++ sfx) :
    ∃ B5 : Fin (STd x D D1 D2) → List Bool,
      Step (bootM x D D1 D2 C1) (bootCost w n D1 C1) (fun _ => 0) (B0 w) (fun i => if i = kT then 1 else 0) B5 ∧
      B5 (cs 0) = frame w ∧ B5 (cs 1) = [false] ∧ B5 (cs 2) = [] ∧
      (∀ j, B5 (wT j) = Scrub.calcIn D n j) ∧ B5 lgT = [] ∧ B5 drT = [] ∧
      B5 kT = RepairSource.VerifierDecoding.CompareMachine.word (UnaryCalc.value D1 C1 n) ∧ B5 dT = [] ∧
      B5 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true ∧
      (∀ i : Fin (STd x D D1 D2), TT x + 1 + Scrub.wk D + 3 + E1 D1 ≤ i.val → B5 i = []) := by
  have hwk := Scrub.wk_eq D
  obtain ⟨m1, s1⟩ := st1 (x := x) (D := D) (D1 := D1) (D2 := D2) w
  obtain ⟨B2, s2, hU, hV, hB2⟩ := st2 (x := x) (D := D) (D1 := D1) (D2 := D2) n sfx w hw m1
  have hin3 : ∀ k, B2 (e1T k) = RepairSource.ProjectionNormalization.DimensionPolynomial.input D1 n k := by
    intro k
    by_cases hk : k.val = 0
    · have e : k = UnaryCalc.inputTape D1 := Fin.ext hk
      subst e
      rw [hU]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · have hn : ∀ j, capSlots j ≠ e1T (x := x) (D := D) (D2 := D2) k := capSlots_ne _ (by
        intro j
        rw [e1T_val]
        fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)
      rw [hB2 _ hn]
      simp [B1, B0, eT_ne_cs, RepairSource.ProjectionNormalization.DimensionPolynomial.input, hk]
  obtain ⟨out, s3, ho, hi3⟩ := st3 (x := x) (D := D) (D1 := D1) (D2 := D2) C1 n B2 hin3
  have hP : install e1T B2 out (e1T (UnaryCalc.outputTape D1)) = List.replicate (UnaryCalc.value D1 C1 n) true := by
    rw [install_slot _ e1T_inj]
    exact ho
  -- positions below the bound's run and off the reader's slots keep stage 1's contents
  have back3 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 3 → (∀ j, capVal x D j ≠ i.val) →
      install e1T B2 out i = B1 w m1 i := by
    intro i h1 h2
    rw [install_other _ _ _ _ (eT_ne_lt i h1), hB2 _ (capSlots_ne i h2)]
  have hK : install e1T B2 out kT = [] := by
    rw [back3 _ (by rw [kT_val]; omega)
      (by intro j; rw [kT_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
    simp [B1, B0, kT_ne_cs]
  set B4 : Fin (STd x D D1 D2) → List Bool := fun i => if i = e1T (UnaryCalc.outputTape D1) then
    List.replicate (UnaryCalc.value D1 C1 n) true else
      if i = kT then RepairSource.VerifierDecoding.CompareMachine.word (UnaryCalc.value D1 C1 n) else
        install e1T B2 out i with hB4
  have s4 : Step (M4 x D D1 D2) (2 * UnaryCalc.value D1 C1 n + 3) (fun _ => 0) (install e1T B2 out) (fun _ => 0) B4 :=
    st4 (x := x) (D := D) (D1 := D1) (D2 := D2) (UnaryCalc.value D1 C1 n) _ hP hK
  have back4 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 2 → (∀ j, capVal x D j ≠ i.val) →
      B4 i = B1 w m1 i := by
    intro i h1 h2
    have e1 : i ≠ e1T (UnaryCalc.outputTape D1) := fun e => eT_ne_lt i (by omega) _ e.symm
    have e2 : i ≠ kT := by
      intro e
      rw [e, kT_val] at h1
      omega
    simp only [hB4, e1, e2, if_false]
    exact back3 i (by omega) h2
  have hO : B4 (cs 1) = [] := by
    rw [back4 (cs 1) (by have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 1; omega)
      (by intro j; rw [cs_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
    simp [B1, B0, cs_eq_iff]
  have s5 := st5 (x := x) (D := D) (D1 := D1) (D2 := D2) B4 hO
  refine ⟨_, (((s1.seq s2).seq s3).seq s4).seq s5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cs_eq_iff, show ¬((0 : Fin 161) = 1) by decide, if_false]
    rw [back4 (cs 0) (by have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 0; omega)
      (by intro j; rw [cs_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
    simp [B1, B0, cs_eq_iff]
  · simp
  · simp only [cs_eq_iff, show ¬((2 : Fin 161) = 1) by decide, if_false]
    rw [back4 (cs 2) (by have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 2; omega)
      (by intro j; rw [cs_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
    simp [B1, B0, cs_eq_iff]
  · intro j
    have hne1 : wT j ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := wT_ne_cs j 1
    simp only [hne1, if_false]
    refine Fin.addCases (fun k => ?_) (fun u => ?_) j
    · by_cases hk : k.val = 0
      · have e : k = UnaryCalc.inputTape D := Fin.ext hk
        subst e
        have e1 : wT (x := x) (D1 := D1) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)) ≠ e1T (UnaryCalc.outputTape D1) :=
          fun e => eT_ne_wT _ _ e.symm
        have e2 : wT (x := x) (D1 := D1) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)) ≠ kT := by
          apply ne_of_val
          rw [wT_val, kT_val]
          have := (Fin.castAdd 1 (UnaryCalc.inputTape D)).isLt
          omega
        simp only [hB4, e1, e2, if_false]
        rw [install_other _ _ _ _ (fun k' => eT_ne_wT k' _), hV]
        simp only [Scrub.calcIn, Fin.addCases_left]
        rfl
      · rw [back4 (wT (Fin.castAdd 1 k))
          (by rw [wT_val]; have := (Fin.castAdd 1 k).isLt; omega)
          (by intro j; rw [wT_val]; have := k.isLt; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
        simp [B1, B0, wT_ne_cs, Scrub.calcIn, RepairSource.ProjectionNormalization.DimensionPolynomial.input, hk]
    · rw [back4 (wT (Fin.natAdd (UnaryCalc.tapes D) u))
        (by rw [wT_val]; have := (Fin.natAdd (UnaryCalc.tapes D) u).isLt; omega)
        (by
          intro j
          rw [wT_val]
          simp only [Fin.val_natAdd]
          have hu := u.isLt
          have ht : 14 ≤ UnaryCalc.tapes D := by
            show 14 ≤ 14 + 2 * D
            omega
          fin_cases j <;> simp [capVal, TT, LNS, LNR] <;> omega)]
      simp [B1, B0, wT_ne_cs, Scrub.calcIn]
  · have hne1 : lgT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := lgT_ne_cs 1
    simp only [hne1, if_false]
    rw [back4 _ (by rw [lgT_val]; omega) (by intro j; rw [lgT_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;>
      omega)]
    simp [B1, B0, lgT_ne_cs]
  · have hne1 : drT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := drT_ne_cs 1
    simp only [hne1, if_false]
    rw [back4 _ (by rw [drT_val]; omega) (by intro j; rw [drT_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;>
      omega)]
    simp [B1, B0, drT_ne_cs]
  · have hne1 : kT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := kT_ne_cs 1
    have hne2 : kT ≠ e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.outputTape D1) := fun e => eTo_ne_kT e.symm
    simp [hB4, hne1, hne2]
  · have hne1 : dT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := by
      apply ne_of_val
      rw [dT_val]
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 1
      omega
    simp only [hne1, if_false]
    rw [back4 _ (by rw [dT_val]; omega) (by intro j; rw [dT_val]; fin_cases j <;> simp [capVal, TT, LNS, LNR] <;>
      omega)]
    have h0 : dT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0 := by
      apply ne_of_val
      rw [dT_val]
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 0
      omega
    have h3 : dT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 3 := by
      apply ne_of_val
      rw [dT_val]
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 3
      omega
    have h4 : dT ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 4 := by
      apply ne_of_val
      rw [dT_val]
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 4
      omega
    simp [B1, B0, h0, h3, h4]
  · have hoV : (UnaryCalc.outputTape D1).val = 3 + 2 * D1 := rfl
    have hiV : (UnaryCalc.inputTape D1).val = 0 := rfl
    have hne1 : e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.inputTape D1) ≠ cs 1 := eT_ne_cs _ 1
    have hne2 : e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.inputTape D1) ≠ e1T (UnaryCalc.outputTape D1) := by
      apply ne_of_val
      rw [e1T_val, e1T_val, hoV, hiV]
      omega
    have hne3 : e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.inputTape D1) ≠ kT := by
      apply ne_of_val
      rw [e1T_val, kT_val]
      omega
    simp only [hne1, if_false, hB4, hne2, hne3]
    rw [install_slot _ e1T_inj]
    exact hi3
  · intro i hi
    have hE : E1 D1 = UnaryCalc.tapes D1 := rfl
    have hE1 : 14 ≤ UnaryCalc.tapes D1 := by
      show 14 ≤ 14 + 2 * D1
      omega
    have hne1 : i ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1 := by
      apply ne_of_val
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 1
      omega
    have hne2 : i ≠ e1T (x := x) (D := D) (D2 := D2) (UnaryCalc.outputTape D1) := by
      apply ne_of_val
      rw [e1T_val]
      have := (UnaryCalc.outputTape D1).isLt
      omega
    have hne3 : i ≠ kT := by
      apply ne_of_val
      rw [kT_val]
      omega
    simp only [hne1, if_false, hB4, hne2, hne3]
    rw [install_other _ _ _ _ (fun k => by
      apply ne_of_val
      rw [e1T_val]
      have := k.isLt
      omega)]
    have hT : 674 ≤ TT x := by unfold TT LNS LNR; omega
    rw [hB2 _ (capSlots_ne i (by intro j; fin_cases j <;> simp [capVal] <;> omega))]
    have h0 : i ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0 := by
      apply ne_of_val
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 0
      omega
    have h3 : i ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 3 := by
      apply ne_of_val
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 3
      omega
    have h4 : i ≠ cs (x := x) (D := D) (D1 := D1) (D2 := D2) 4 := by
      apply ne_of_val
      have := cs_lt (x := x) (D := D) (D1 := D1) (D2 := D2) 4
      omega
    simp [B1, B0, h0, h3, h4]

end Boot

end NearCubicWires.WireExponent3_5.PrimAsm.ShellD
