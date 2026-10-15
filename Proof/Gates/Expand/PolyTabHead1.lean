import Proof.Gates.Expand.PolyTabStage10b
import Proof.Gates.Expand.PolyTabTailCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation

section Lay
variable {te qa : ℕ}

/-- The ideal start's lengths: the log `sL` holds `lcap` blanks. -/
def lensK (te qa lcap : ℕ) : Fin (NSx te qa + 1) → ℕ := fun i => if i = sL then lcap else 0

def r8 : Fin 8 ↪ Fin NRk :=
  ⟨fun i => rX ⟨20 + i.val, by omega⟩, fun a b e => by
    have := congrArg Fin.val e; simp at this; exact Fin.ext (by omega)⟩

theorem r8_ne (i : Fin 8) : r8 i ≠ rX 28 := by
  intro e; have := congrArg Fin.val e; simp [r8] at this; omega

theorem frame_tabWord (r : TabReq) : frame (tabWord r) = encN (preN r) ++ frame (formulaWord ⟨r.V, r.F⟩) := by
  rw [Codec.frame_eq_marks, Codec.frame_eq_marks, encN_eq_marks, tabWord_eq]
  simp [marks, List.append_assoc]

end Lay

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

abbrev te (E : ExpandMachine) : ℕ := E.wf.program.tapeCount

local notation "WXE" => WMX (NSx (te E) (Qa a)) NRk
local notation "WSE" => WState (NSx (te E) (Qa a)) NRk

def t0 : Fin (te E) := ⟨0, lt_of_lt_of_le (by norm_num) E.wf.program.twoTapes⟩

noncomputable def phA1 : WMX (NSx (te E) (Qa a)) NRk :=
  .seq (.wm (Codec.copyRW sI (sS 0) (rX 8) (rX 3) (rX 4))) <| .seq st1 <| .seq (cpForm (sT (t0 E))) <|
  .seq (WMX.machZ E.wf.program.machine sT sL) <|
  .seq (cpTerms (sT E.wf.program.outputTape) (sS 1) r8 (rX 28) r8_ne) (.wm (Codec.copyRW (sS 1) (sS 2) (rX 8) (rX 3) (rX 4)))

/-- The ideal start of PolyTab. -/
noncomputable def σI (r : TabReq) : WState (NSx (te E) (Qa a)) NRk :=
  idealStart (NSx (te E) (Qa a)) NRk (tabWord r) (lensK (te E) (Qa a) (E.budget ⟨r.V, r.F⟩))

theorem σI_st0 (r : TabReq) : (σI E a r).st sI = frame (tabWord r) := rfl
theorem σI_st (r : TabReq) (x : Fin (NSx (te E) (Qa a) + 1)) (h0 : x ≠ sI) (hL : x ≠ sL) : (σI E a r).st x = [] := by
  have : x.val ≠ 0 := fun e => h0 (Fin.ext e)
  show (if x.val = 0 then _ else _) = _
  rw [if_neg this]; simp [lensK, hL]
theorem σI_stL (r : TabReq) : (σI E a r).st sL = List.replicate (E.budget ⟨r.V, r.F⟩) false := by
  simp [σI, idealStart, lensK, sL]
theorem σI_sh (r : TabReq) (x : Fin (NSx (te E) (Qa a) + 1)) : (σI E a r).sh x = 0 := rfl
theorem σI_val (r : TabReq) (q : Fin NRk) : (σI E a r).val q = 0 := rfl

noncomputable def SA1 : List (Fin (NSx (te E) (Qa a) + 1)) := [sI, sS 0, sS 1, sS 2, sL] ++ List.ofFn sT

structure A1End (r : TabReq) (τ : WSE) : Prop where
  s0 : τ.st (sS 0) = frame (tabWord r)
  s0h : τ.sh (sS 0) = 0
  s1 : τ.st (sS 1) = frame (termsWord (E.expand ⟨r.V, r.F⟩))
  s1h : τ.sh (sS 1) = 0
  s2 : τ.st (sS 2) = frame (termsWord (E.expand ⟨r.V, r.F⟩))
  s2h : τ.sh (sS 2) = 0
  x : ∀ j, τ.val (rX j) = f1 r j
  fr : SameExcept (σI E a r) τ (SA1 E a) RXL

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairRepresentation

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

def cpRWCost (x : ℕ) : ℕ :=
  22 * x + 1 + 1 + 7 + 1 + (18 * (2 * x + 1) + 3 + 1 + (5 * (2 * x + 1) + 1 + 1 + (5 * (2 * x + 1) + 1)))

def cpFormCost (w : ℕ) : ℕ := 22 * w + 1 + 1 + 7 + 1 + (5 * (2 * w + 1) + 1)

noncomputable def phA1Cost (r : TabReq) : ℕ :=
  cpRWCost (tabWord r).length + 1 + (26 * (Cst r + 1) + 1 + (cpFormCost (formulaWord ⟨r.V, r.F⟩).length + 1 +
    ((2 * E.budget ⟨r.V, r.F⟩ + 2) + 1 + (cpTermsCost (E.expand ⟨r.V, r.F⟩) + 1 +
    cpRWCost (termsWord (E.expand ⟨r.V, r.F⟩)).length))))

def capA1 (r : TabReq) (P : Terms r.V) : ℕ :=
  4 * (tabWord r).length + 4 + 2 ^ (Lt r + 1) + 8 * (Mh r + 1) ^ 2 + 2 ^ (natBitLength r.V + 1) + r.V +
    2 ^ (natBitLength P.length + 1) + P.length + 6 * natBitLength r.V + 6 * natBitLength P.length +
    4 * (termsWord P).length + 40

theorem sT_ne_sL (j : Fin (te E)) : sT j ≠ (sL : Fin (NSx (te E) (Qa a) + 1)) := by
  intro e; have := congrArg Fin.val e; rw [sT_val, sL_val] at this; omega
theorem sT_ne_sI (j : Fin (te E)) : sT j ≠ (sI : Fin (NSx (te E) (Qa a) + 1)) := by
  intro e; have := congrArg Fin.val e; rw [sT_val, sI_val] at this; omega
theorem sT_ne_sS (j : Fin (te E)) (i : Fin 40) : sT j ≠ (sS i : Fin (NSx (te E) (Qa a) + 1)) := by
  intro e; have := congrArg Fin.val e; rw [sT_val, sS_val] at this; have := i.isLt; omega

theorem phA1_spec (r : TabReq) (cap : ℕ) (hcap : capA1 r (E.expand ⟨r.V, r.F⟩) ≤ cap) :
    Runs cap (phA1 E a) (σI E a r) (phA1Cost E r) (A1End E a r) := by
  set σ0 := σI E a r with hσ0
  set P := E.expand ⟨r.V, r.F⟩ with hP
  unfold capA1 at hcap
  have q1 := Nat.two_pow_pos (Lt r)
  have q2 := Nat.two_pow_pos (natBitLength r.V)
  have q3 := Nat.two_pow_pos (natBitLength P.length)
  have hfw : (formulaWord ⟨r.V, r.F⟩).length ≤ (tabWord r).length := by rw [tabWord_eq]; simp
  -- (0) copy the input to sS 0
  have e0 := Codec.copyRW_spec (cap := cap) sI (sS 0) (by polyTabNe) (rX 8) (rX 3) (rX 4) (by polyTabNe) (by polyTabNe) (by polyTabNe)
    (tabWord r) [] σ0 (by rw [List.append_nil]; rfl) rfl (σI_st E a r _ (by polyTabNe) (by polyTabNe)) rfl rfl rfl rfl (by omega)
  set σ1 := σ0.sets (sS 0) (frame (tabWord r)) with hσ1
  -- (1) the header pass
  have p1 : PS σ1 sI [] (preN r) (frame (formulaWord ⟨r.V, r.F⟩)) 0 (fun _ => 0) σ1 :=
    ⟨⟨by simp [hσ1, Function.update_of_ne (show sI ≠ sS 0 by polyTabNe), hσ0, σI_st0, frame_tabWord], by
      simp [hσ1, hσ0, σI_sh, encN]⟩, fun j => by simp [hσ1, hσ0, σI_val], SameExcept.refl _ _ _⟩
  obtain ⟨τ2, e1, p2⟩ := st1_spec cap r σ1 σ1 _ p1 (by omega)

  have bl2 : ∀ x, x ≠ sI → x ≠ sL → x ≠ sS 0 → τ2.st x = [] ∧ τ2.sh x = 0 := fun x h0 hL hs0 => by
    have hx : x ∉ [sI] := nm1 h0
    rw [p2.fr.st hx, p2.fr.sh hx]
    simp [hσ1, Function.update_of_ne hs0, hσ0, σI_st E a r x h0 hL, σI_sh]
  -- (2) the formula to the expansion's input tape
  have hpos := p2.pos
  unfold NatAt at hpos
  rw [List.take_length] at hpos
  have e2 := cpForm_spec cap (sT (t0 E)) (sT_ne_sI E a _).symm (formulaWord ⟨r.V, r.F⟩) (encN (preN r)) [] τ2
    (by rw [hpos.1, List.append_nil]) hpos.2 (bl2 _ (sT_ne_sI E a _) (sT_ne_sL E a _) (sT_ne_sS E a _ _)).1
    (bl2 _ (sT_ne_sI E a _) (sT_ne_sL E a _) (sT_ne_sS E a _ _)).2 (by rw [p2.x]; simp [f1, fB]) (by omega)
  set τ3 := (τ2.sets (sT (t0 E)) (frame (formulaWord ⟨r.V, r.F⟩))).seth sI
    ((encN (preN r)).length + 2 * (formulaWord ⟨r.V, r.F⟩).length) with hτ3

  have hL3 : τ3.st sL = List.replicate (E.budget ⟨r.V, r.F⟩) false := by
    rw [hτ3]; simp only [WState.seth_st, WState.sets_st, Function.update_of_ne (sT_ne_sL E a _).symm]
    rw [p2.fr.st (nm1 (by polyTabNe))]; simp [hσ1, Function.update_of_ne (show sL ≠ sS 0 by polyTabNe), hσ0, σI_stL]
  obtain ⟨τ4, e3, o4, h4, d4, v4, c4⟩ := wf_machZ_exact E.wf ⟨r.V, r.F⟩ (cap := cap) sT sT.injective sL
    (sT_ne_sL E a) τ3 (fun j => by
      rw [hτ3]; simp only [WState.seth_sh, WState.sets_sh, Function.update_of_ne (sT_ne_sI E a j)]
      exact (bl2 _ (sT_ne_sI E a _) (sT_ne_sL E a _) (sT_ne_sS E a _ _)).2) (fun j => by
      rw [hτ3]; simp only [WState.seth_st, WState.sets_st, Program.inputTapes]
      by_cases hj : j = t0 E
      · subst hj; simp [t0]
      · have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
        rw [Function.update_of_ne (fun e => hj (sT.injective e)), if_neg hj']
        exact (bl2 _ (sT_ne_sI E a _) (sT_ne_sL E a _) (sT_ne_sS E a _ _)).1)
    (E.budget ⟨r.V, r.F⟩) hL3 (by rw [hτ3]; simp [Function.update_of_ne (show sL ≠ sI by polyTabNe),
      Function.update_of_ne (sT_ne_sL E a _).symm]; exact (p2.fr.sh (nm1 (by polyTabNe))).trans (by simp [hσ1, hσ0, σI_sh]))
    le_rfl

  have nT : ∀ i : Fin 40, ∀ j, sT j ≠ (sS i : Fin (NSx (te E) (Qa a) + 1)) := fun i j => sT_ne_sS E a j i
  have s4 : ∀ i : Fin 40, i ≠ 0 → τ4.st (sS i) = [] ∧ τ4.sh (sS i) = 0 := fun i hi => by
    have hi' : sS i ≠ (sS 0 : Fin (NSx (te E) (Qa a) + 1)) := fun e => hi (sS.injective e)
    rw [(d4 (sS i) (fun j => nT i j)).1, (d4 (sS i) (fun j => nT i j)).2, hτ3]
    simp only [WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh,
      Function.update_of_ne (nT i _).symm, Function.update_of_ne (show sS i ≠ sI by polyTabNe)]
    exact bl2 _ (by polyTabNe) (by polyTabNe) hi'
  -- (4) the terms word, framed, to sS 1
  have hz4 : ∀ j, τ4.val (rX j) = f1 r j := fun j => by rw [v4, hτ3]; simp [p2.x]
  have e4 := cpTerms_spec (cap := cap) (sT E.wf.program.outputTape) (sS 1) (nT 1 _) r8 (rX 28) r8_ne P [] τ4
    (by rw [o4, List.append_nil]) (h4 _) (s4 1 (by decide)).1 (s4 1 (by decide)).2
    (fun i => by
      show τ4.val (rX ⟨20 + i.val, _⟩) = 0
      have := i.isLt
      rw [hz4]; simp only [f1, fB, Fin.ext_iff, Fin.val_ofNat]; split_ifs <;> simp_all <;> omega) (by rw [hz4]; simp [f1, fB])
    (by dsimp only; omega) (by dsimp only; omega) (by omega) (by omega) (by dsimp only; omega)
  set τ5 := (τ4.sets (sS 1) (frame (termsWord P))).seth (sT E.wf.program.outputTape) (termsWord P).length with hτ5
  -- (5) the second copy to sS 2
  have e5 := Codec.copyRW_spec (cap := cap) (sS 1) (sS 2) (by polyTabNe) (rX 8) (rX 3) (rX 4) (by polyTabNe) (by polyTabNe)
    (by polyTabNe) (termsWord P) [] τ5 (by simp [hτ5, Function.update_of_ne (nT 1 _).symm])
    (by simp [hτ5, Function.update_of_ne (nT 1 _).symm, (s4 1 (by decide)).2])
    (by simp [hτ5, Function.update_of_ne (show sS 2 ≠ sS 1 by polyTabNe), Function.update_of_ne (nT 2 _).symm,
      (s4 2 (by decide)).1])
    (by simp [hτ5, Function.update_of_ne (nT 2 _).symm, (s4 2 (by decide)).2])
    (by simp [hτ5, hz4, f1, fB]) (by simp [hτ5, hz4, f1, fB]) (by simp [hτ5, hz4, f1, fB]) (by omega)
  refine ⟨_, WXExec.seq (WXExec.wm e0) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.wm e5))))),
    ⟨?_, ?_, ?_, ?_, by simp [hP], by simp [hτ5, Function.update_of_ne (nT 2 _).symm, (s4 2 (by decide)).2], ?_, ?_⟩⟩
  · simp [hτ5, Function.update_of_ne (show sS 0 ≠ sS 2 by polyTabNe), Function.update_of_ne (show sS 0 ≠ sS 1 by polyTabNe),
      Function.update_of_ne (nT 0 _).symm]
    rw [(d4 (sS 0) (fun j => nT 0 j)).1, hτ3]
    simp only [WState.seth_st, WState.sets_st, Function.update_of_ne (nT 0 _).symm]
    rw [p2.fr.st (nm1 (by polyTabNe))]; simp [hσ1]
  · simp [hτ5, Function.update_of_ne (nT 0 _).symm]
    rw [(d4 (sS 0) (fun j => nT 0 j)).2, hτ3]
    simp only [WState.seth_sh, WState.sets_sh, Function.update_of_ne (nT 0 _).symm,
      Function.update_of_ne (show sS 0 ≠ sI by polyTabNe)]
    rw [p2.fr.sh (nm1 (by polyTabNe))]; simp [hσ1, hσ0, σI_sh]
  · simp [hτ5, Function.update_of_ne (show sS 1 ≠ sS 2 by polyTabNe), hP]
  · simp [hτ5, Function.update_of_ne (nT 1 _).symm, (s4 1 (by decide)).2]
  · intro j; simp [hτ5, hz4]
  · refine ⟨fun x hx => ?_, fun q hq => ?_, ?_⟩
    · simp only [SA1, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨⟨h0, hs0, hs1, hs2, hL⟩, hT⟩ := hx
      have hT' : ∀ j, sT j ≠ x := fun j e => hT ⟨j, e⟩
      simp only [hτ5, WState.sets_st, WState.seth_st, WState.sets_sh, WState.seth_sh, Function.update_of_ne hs2,
        Function.update_of_ne hs1, Function.update_of_ne (Ne.symm (hT' _))]
      rw [(d4 x hT').1, (d4 x hT').2, hτ3]
      simp only [WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, Function.update_of_ne h0,
        Function.update_of_ne (Ne.symm (hT' _))]
      rw [p2.fr.st (nm1 h0), p2.fr.sh (nm1 h0)]
      simp [hσ1, Function.update_of_ne hs0, hσ0]
    · have hq' : ∀ j, q ≠ rX j := fun j e => hq (by rw [e]; exact rX_mem j)
      simp only [hτ5, WState.sets_val, WState.seth_val]
      rw [v4, hτ3]; simp only [WState.seth_val, WState.sets_val]
      rw [p2.fr.val hq]; simp [hσ1, hσ0]
    · simp only [hτ5, WState.sets_cell, WState.seth_cell]; rw [c4, hτ3]
      simp only [WState.seth_cell, WState.sets_cell]; rw [p2.fr.cell]; simp [hσ1, hσ0]

end NearCubicGates.Close.Expand.PolyTab
