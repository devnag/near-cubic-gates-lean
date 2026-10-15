import Proof.Wire_3_5.ListMachinePrintRec

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-- Evaluate a docked tape bank at a concrete tape. -/
macro "bank_install" : tactic => `(tactic| (funext i; fin_cases i <;> first
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
  | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
  | exact RecoveryRootRound.install_other _ _ _ _ (by decide)))

/-- Evaluate docked heads at a concrete tape. -/
macro "bank_dockH" : tactic => `(tactic| (funext i; fin_cases i <;> first
  | exact dockH_slot _ (by decide) _ _ 0
  | exact dockH_slot _ (by decide) _ _ 1
  | exact dockH_slot _ (by decide) _ _ 2
  | exact dockH_slot _ (by decide) _ _ 3
  | exact dockH_slot _ (by decide) _ _ 4
  | exact dockH_other _ _ _ _ (by decide)))

/-- The printer's tapes. -/
structure Bank where
  x : List Bool
  t : List Bool
  r : List Bool
  a : List Bool
  fi : List Bool
  fo : List Bool
  pf : List Bool
  m : List Bool
  z : List Bool
  d : List Bool
  o : List Bool
  u : List Bool
  l1 : List Bool
  l2 : List Bool

def Bank.tapes (b : Bank) : Fin 14 → List Bool :=
  ![b.x, b.t, b.r, b.a, b.fi, b.fo, b.pf, b.m, b.z, b.d, b.o, b.u, b.l1, b.l2]

/-- The heads: all at `0` but the output's. -/
def bh (o : ℕ) : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, 0]

/-! ## Docking through a pick table -/

theorem dockH_of_pick {t u : ℕ} (slots : Fin t → Fin u) (p : Fin u → Option (Fin t))
    (hp : ∀ i, RecoveryFocus.pick slots i = p i) (H : Fin u → ℕ) (v : Fin t → ℕ) :
    dockH slots H v = fun i => match p i with | some j => v j | none => H i := by
  funext i; unfold dockH; rw [hp]
  cases p i <;> rfl

theorem install_of_pick {t u : ℕ} (slots : Fin t → Fin u) (p : Fin u → Option (Fin t))
    (hp : ∀ i, RecoveryFocus.pick slots i = p i) (A : Fin u → List Bool) (v : Fin t → List Bool) :
    RecoveryRootRound.install slots A v = fun i => match p i with | some j => v j | none => A i := by
  funext i; unfold RecoveryRootRound.install; rw [hp]
  cases p i <;> rfl

/-- Prove a pick table of a concrete slot map. -/
macro "pick_table" inj:term : tactic => `(tactic| (intro i; fin_cases i <;> first
  | exact RecoveryFocus.pick_slot _ $inj 0
  | exact RecoveryFocus.pick_slot _ $inj 1
  | exact RecoveryFocus.pick_slot _ $inj 2
  | exact RecoveryFocus.pick_slot _ $inj 3
  | exact RecoveryFocus.pick_slot _ $inj 4
  | decide))

/-! ## The do-nothing step -/

theorem idle_step {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (NearCubicWires.WireExponent3_5.Block.idle t) 0 H A H A := by
  obtain ⟨r, hr, hf, hs⟩ := (Timed.refl (NearCubicWires.WireExponent3_5.Block.idle t)
    ⟨(NearCubicWires.WireExponent3_5.Block.idle t).start, H, A⟩).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], hs.le⟩

/-! ## Cell stages -/

/-- A cell operation on three cells of the bank, the first one rewritten. -/
theorem cell_step (op : Bool → Bool → Bool → Bool) (s : Fin 3 → Fin 14) (hs : Function.Injective s) (o : ℕ)
    (b b' : Bank) (x y z : Bool) (hH : ∀ j, bh o (s j) = 0) (hA : ∀ j, b.tapes (s j) = ![[x], [y], [z]] j)
    (hb : RecoveryRootRound.install s b.tapes ![[op x y z], [y], [z]] = b'.tapes) :
    Step (RecoveryFocus.machine s (GF2.CellOp.machine op)) 1 (bh o) b.tapes (bh o) b'.tapes := by
  have hc : Step (GF2.CellOp.machine op) 1 (fun _ => 0) ![[x], [y], [z]] (fun _ => 0) ![[op x y z], [y], [z]] :=
    ((GF2.CellOp.run op x y z).congr_in (by funext j; fin_cases j <;> rfl) rfl).congr
      (by funext j; fin_cases j <;> rfl) rfl
  have h := Block.dockKeep hc s hs (bh o) b.tapes hH hA
  rwa [hb] at h

/-! ## Word stages, rewound through a log -/

def selTT : Fin 2 → Bool := ![true, true]
def selTTF : Fin 3 → Bool := ![true, true, false]

/-- An in-place ripple on two words of the bank, both cursors rewound through the log. -/
theorem ripple_stage (g h : Bool → Bool → Bool → Bool) (c₀ : Bool) (s : Fin 3 → Fin 14)
    (hs : Function.Injective s) (o : ℕ) (b b' : Bank) (u v : List Bool) (hl : u.length = v.length) (cap : ℕ)
    (hcap : 2 * u.length + 1 ≤ cap) (hH : ∀ j, bh o (s j) = 0)
    (hA : ∀ j, b.tapes (s j) = ![frame u, frame v, List.replicate cap false] j)
    (hb : RecoveryRootRound.install s b.tapes
      ![frame (Block.ripple g h c₀ u v), frame v, List.replicate cap false] = b'.tapes) :
    Step (RecoveryFocus.machine s (MaskedReset.machine (Block.RippleIn.machine g h c₀) selTT))
      (2 * (2 * u.length + 1) + 2) (bh o) b.tapes (bh o) b'.tapes := by
  have hm := maskRun (Block.RippleIn.run g h c₀ u v hl) selTT (by intro j _; fin_cases j <;> rfl) hcap
  have hc : Step (MaskedReset.machine (Block.RippleIn.machine g h c₀) selTT) (2 * (2 * u.length + 1) + 2)
      (fun _ => 0) ![frame u, frame v, List.replicate cap false]
      (fun _ => 0) ![frame (Block.ripple g h c₀ u v), frame v, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc s hs (bh o) b.tapes hH hA
  rwa [hb] at h

/-- A fold of two words of the bank into a cell, the word cursors rewound through the log. -/
theorem fold_stage (f : Bool → Bool → Bool → Bool) (init : Bool) (s : Fin 4 → Fin 14)
    (hs : Function.Injective s) (o : ℕ) (b b' : Bank) (u v : List Bool) (c : Bool) (hl : u.length = v.length)
    (cap : ℕ) (hcap : 2 * u.length + 1 ≤ cap) (hH : ∀ j, bh o (s j) = 0)
    (hA : ∀ j, b.tapes (s j) = ![frame u, frame v, [c], List.replicate cap false] j)
    (hb : RecoveryRootRound.install s b.tapes
      ![frame u, frame v, [Block.foldBits f init u v], List.replicate cap false] = b'.tapes) :
    Step (RecoveryFocus.machine s (MaskedReset.machine (Block.FoldCell.machine f init) selTTF))
      (2 * (2 * u.length + 1) + 2) (bh o) b.tapes (bh o) b'.tapes := by
  have hm := maskRun (Block.FoldCell.run f init u v c hl) selTTF (by intro j _; fin_cases j <;> rfl) hcap
  have hc : Step (MaskedReset.machine (Block.FoldCell.machine f init) selTTF) (2 * (2 * u.length + 1) + 2)
      (fun _ => 0) ![frame u, frame v, [c], List.replicate cap false]
      (fun _ => 0) ![frame u, frame v, [Block.foldBits f init u v], List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc s hs (bh o) b.tapes hH hA
  rwa [hb] at h

/-- The flag `[pop X = d]` into a cell of the bank, the cursors rewound through the log. -/
theorem pop_stage (s : Fin 4 → Fin 14) (hs : Function.Injective s) (o : ℕ) (b b' : Bank) (xs : List Bool)
    (d : ℕ) (tail : List Bool) (c : Bool) (hd : Interp.pop xs ≤ d) (cap : ℕ) (hcap : 2 * xs.length + 1 ≤ cap)
    (hH : ∀ j, bh o (s j) = 0)
    (hA : ∀ j, b.tapes (s j) = ![frame xs, List.replicate d true ++ false :: tail, [c], List.replicate cap false] j)
    (hb : RecoveryRootRound.install s b.tapes
      ![frame xs, List.replicate d true ++ false :: tail, [decide (Interp.pop xs = d)], List.replicate cap false] =
        b'.tapes) :
    Step (RecoveryFocus.machine s (MaskedReset.machine PopEq.machine selTTF))
      (2 * (2 * xs.length + 1) + 2) (bh o) b.tapes (bh o) b'.tapes := by
  have hm := maskRun (PopEq.run xs d tail c hd) selTTF (by intro j _; fin_cases j <;> rfl) hcap
  have hc : Step (MaskedReset.machine PopEq.machine selTTF) (2 * (2 * xs.length + 1) + 2)
      (fun _ => 0) ![frame xs, List.replicate d true ++ false :: tail, [c], List.replicate cap false]
      (fun _ => 0) ![frame xs, List.replicate d true ++ false :: tail, [decide (Interp.pop xs = d)],
        List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have h := Block.dockKeep hc s hs (bh o) b.tapes hH hA
  rwa [hb] at h

/-- The record printer on the bank: tapes (bitmap, position word, output, log, log). -/
def sRec : Fin 5 → Fin 14 := ![0, 11, 10, 12, 13]
theorem sRec_inj : Function.Injective sRec := by decide
def pRec : Fin 14 → Option (Fin 5) :=
  ![some 0, none, none, none, none, none, none, none, none, none, some 2, some 1, some 3, some 4]
theorem pick_sRec : ∀ i, RecoveryFocus.pick sRec i = pRec i := by pick_table sRec_inj

theorem rec_stage (b : Bank) (xs Ub oo B : List Bool) (capU capX : ℕ)
    (hx : b.x = frame xs) (hu : b.u = Ub) (ho : b.o = overlay oo B)
    (h1 : b.l1 = List.replicate capU false) (h2 : b.l2 = List.replicate capX false)
    (hUb : overlay (frame (List.replicate xs.length true)) Ub = Ub)
    (hcapU : armCost xs.length + 2 ≤ capU) (hcapX : recInnerCost xs ≤ capX) :
    Step (RecoveryFocus.machine sRec recM) (2 * recInnerCost xs + 2) (bh oo.length) b.tapes
      (bh (oo ++ Rec.recW (Interp.supp xs)).length) { b with o := overlay (oo ++ Rec.recW (Interp.supp xs)) B }.tapes := by
  have h := dockRun (rec_run xs Ub oo B capU capX hUb hcapU hcapX) sRec sRec_inj (bh oo.length) b.tapes
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hu
        · exact ho
        · exact h1
        · exact h2)
  rw [dockH_of_pick sRec pRec pick_sRec, install_of_pick sRec pRec pick_sRec] at h
  generalize (oo ++ Rec.recW (Interp.supp xs)).length = n at h ⊢
  generalize overlay (oo ++ Rec.recW (Interp.supp xs)) B = w at h ⊢
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> simp [pRec, bh]
  · funext i; fin_cases i <;> simp [pRec, Bank.tapes, hx, hu, h1, h2]

/-- One bit appended at the output cursor. -/
def sOut : Fin 1 → Fin 14 := ![10]
theorem sOut_inj : Function.Injective sOut := by decide
def pOut : Fin 14 → Option (Fin 1) :=
  ![none, none, none, none, none, none, none, none, none, none, some 0, none, none, none]
theorem pick_sOut : ∀ i, RecoveryFocus.pick sOut i = pOut i := by pick_table sOut_inj

theorem put_stage (bit : Bool) (b : Bank) (oo B : List Bool) (ho : b.o = overlay oo B) :
    Step (RecoveryFocus.machine sOut (Put.machine bit)) 1 (bh oo.length) b.tapes
      (bh (oo ++ [bit]).length) { b with o := overlay (oo ++ [bit]) B }.tapes := by
  have h := dockRun (Put.run bit oo B) sOut sOut_inj (bh oo.length) b.tapes
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; exact ho)
  rw [dockH_of_pick sOut pOut pick_sOut, install_of_pick sOut pOut pick_sOut] at h
  generalize (oo ++ [bit]).length = n at h ⊢
  generalize overlay (oo ++ [bit]) B = w at h ⊢
  exact h.congr (by funext i; fin_cases i <;> simp [pOut, bh]) (by funext i; fin_cases i <;> simp [pOut, Bank.tapes])

end NearCubicWires.WireExponent3_5.ListMachine.Print
