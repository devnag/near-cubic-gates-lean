import Proof.Wire_3_5.SeedFixFetchCells

/-! # C4.Sb, machine part 15: a term group appended to the output expression

The output tape holds the printed expression of the groups so far, `exprWord V`. Appending a group `G`: pass `V`'s word,
step back onto its terminator, copy `G`'s word from the accumulator over it. The result is `exprWord (V ++ G)`.

Paper quantity of the main type: the printed expression `V ++ G` (`emit_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

namespace Emit

/-- Step the head one cell left. -/
def backM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .left⟩ else none

theorem back_run (tape : List Bool) (h : ℕ) : Step backM 1 ![h] ![tape] ![h - 1] ![tape] := by
  have hs : step backM ⟨backM.start, ![h], ![tape]⟩ = some ⟨1, ![h - 1], ![tape]⟩ := by
    simp [step, backM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := backM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-! ## Slot maps (tapes 0 the accumulator, 1 the output) -/

def e2S : Fin 2 → Fin 2 := ![1, 0]

theorem install_e2S (A : Fin 2 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install e2S A v = ![v 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1

theorem dockH_e2S (H : Fin 2 → ℕ) (v : Fin 2 → ℕ) :
    dockH e2S H v = ![v 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1

def e2B : Fin 1 → Fin 2 := ![1]

theorem install_e2B (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install e2B A v = ![A 0, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_e2B (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH e2B H v = ![H 0, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

theorem exprWord_append (V G : SExpr) : exprWord (V ++ G) = V.flatMap recT ++ exprWord G := by
  simp [exprWord_eq, List.append_assoc]

theorem overlay_prefix (o T : List Bool) (h : o <+: T) : overlay o T = T := by
  obtain ⟨u, rfl⟩ := h
  simp [overlay]

theorem overlay_overlay_le (w u B : List Bool) (h : u.length ≤ w.length) : overlay w (overlay u B) = overlay w B := by
  simp only [overlay, List.drop_append]
  have e1 : u.length - w.length = 0 := by omega
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
  congr 2
  omega

noncomputable def emitInner := Composition.machine (Composition.machine (RecoveryFocus.machine e2S (ExprCopy.machine false))
  (RecoveryFocus.machine e2B backM)) (ExprCopy.machine true)

def selE2 : Fin 2 → Bool := ![true, true]

/-- **The emission**: the output's expression extended by the accumulator's, both heads rewound. -/
noncomputable def emitM := MaskedReset.machine emitInner selE2

def emitInnerCost (a b : ℕ) : ℕ := a + 1 + 1 + 1 + b

theorem emit_run (V G : SExpr) (tX OB : List Bool) (cap : ℕ)
    (hcap : emitInnerCost (exprWord V).length (exprWord G).length ≤ cap) :
    Step emitM (2 * emitInnerCost (exprWord V).length (exprWord G).length + 2) (fun _ => 0)
      ![exprWord G ++ tX, overlay (exprWord V) OB, List.replicate cap false] (fun _ => 0)
      ![exprWord G ++ tX, overlay (exprWord (V ++ G)) OB, List.replicate cap false] := by
  set X := exprWord G ++ tX
  set O0 := overlay (exprWord V) OB
  set out := V.flatMap recT
  have eO : O0 = [] ++ exprWord V ++ OB.drop (exprWord V).length := by simp [O0, overlay]
  -- 1: past the output's expression
  have h1 := ExprCopy.run false [] V (OB.drop (exprWord V).length) [] X
  rw [← eO] at h1
  have h1' : Step (ExprCopy.machine false) (exprWord V).length ![0, 0] ![O0, X] ![(exprWord V).length, 0] ![O0, X] :=
    (h1.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> simp [overlay])).congr
      (by funext j; fin_cases j <;> simp [owC]) (by funext j; fin_cases j <;> simp [owC, overlay])
  have s1 := dockRun h1' e2S (by decide) (fun _ => 0) ![X, O0] (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [dockH_e2S, install_e2S] at s1
  -- 2: back onto its terminator
  have s2 := dockRun (back_run O0 (exprWord V).length) e2B (by decide) ![0, (exprWord V).length] ![X, O0]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_e2B, install_e2B] at s2
  -- 3: the accumulator's expression over it
  have hpre : out <+: O0 := ⟨[false] ++ OB.drop (exprWord V).length, by simp [O0, overlay, exprWord_eq, out]⟩
  have h3 := ExprCopy.run true [] G tX out O0
  rw [overlay_prefix out O0 hpre] at h3
  have hol : (exprWord V).length - 1 = out.length := by simp [exprWord_eq, out]
  have eOut : overlay (out ++ owC true (exprWord G)) O0 = overlay (exprWord (V ++ G)) OB := by
    simp only [owC, if_true]
    rw [← exprWord_append, overlay_overlay_le]
    simp [exprWord_eq]
  rw [eOut] at h3
  have hall := ((s1.congr (hout' := ![0, (exprWord V).length]) (tout' := ![X, O0]) (by funext j; fin_cases j <;> rfl)
      (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![0, out.length]) (tout' := ![X, O0]) (by funext j; fin_cases j <;> simp [hol])
      (by funext j; fin_cases j <;> rfl))).seq
    (h3.congr_in (hin' := ![0, out.length]) (tin' := ![X, O0]) (by funext j; fin_cases j <;> rfl)
      (by funext j; fin_cases j <;> simp [X]))
  have hm := hall.mask (cap := cap) selE2 (by intro j _; fin_cases j <;> rfl) hcap
  unfold emitInnerCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

end Emit

end NearCubicWires.WireExponent3_5.SeedFix
