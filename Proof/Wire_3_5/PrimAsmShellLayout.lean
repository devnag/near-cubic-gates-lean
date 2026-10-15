import Proof.Wire_3_5.PrimAsmCellLoop
import Proof.Circuits.DecompositionSourceBounds

/-! # PA (d), the writer shell, part 1: the shell's layout and its bookkeeping

The writers' shell (the shared WRITER-SHELL kit: inBank → the scrubbed loop entry → the loop → a masked reset →
`WriterRun`) runs on ONE layout: the cell of the unit machine (`CellLoop.TT x` tapes), the scrub entry's calc
workspace (`Scrub.wk D`), the scrub's log and driver, the loop counter, and the tapes of the polynomial run that
computes the loop bound (`UnaryCalc.tapes D1`). This module names the tapes (`cT`, `wT`, `lgT`, `drT`, `kT`, `eT`),
decomposes a bank into its regions (**`regions`**), and gives the generic facts the stages use:

* `install_eq`, `dockH_eq`: a docked run's exit bank, pointwise;
* **`Step.len`**: a run of `n` steps leaves every tape of length at most `k + n` if it started within `k`
  (base `DecompositionSource.one_tape_support`);
* `ready_of_step`: an all-heads-zero `Step` is a `ClockJoin.ReadyRun`.

Paper quantity: none (machine plumbing for the writers, whose types carry the paper's tapes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Shell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop

/-- The loop's layout: cell, workspace, log, driver, counter. -/
abbrev LT (x D : ℕ) : ℕ := TT x + Scrub.wk D + 1 + 1 + 1

/-- The shell's layout: the loop's, then the bound's polynomial run. -/
abbrev ST (x D D1 : ℕ) : ℕ := LT x D + UnaryCalc.tapes D1

section Tapes
variable {x D D1 : ℕ}

/-- A cell tape. -/
def cT (i : Fin (TT x)) : Fin (ST x D D1) :=
  Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.castAdd (Scrub.wk D) i)))
/-- A workspace tape. -/
def wT (j : Fin (Scrub.wk D)) : Fin (ST x D D1) := Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.natAdd (TT x) j)))
/-- The scrub's log. -/
def lgT : Fin (ST x D D1) := Fin.castAdd _ (Fin.castAdd 1 Scrub.logTape)
/-- The scrub's driver. -/
def drT : Fin (ST x D D1) := Fin.castAdd _ (Fin.castAdd 1 Scrub.driverTape)
/-- The loop counter. -/
def kT : Fin (ST x D D1) := Fin.castAdd _ (Fin.natAdd (TT x + Scrub.wk D + 1 + 1) (0 : Fin 1))
/-- A tape of the bound's polynomial run. -/
def eT (k : Fin (UnaryCalc.tapes D1)) : Fin (ST x D D1) := Fin.natAdd (LT x D) k
/-- A fixed stream of the cell. -/
def cs (k : Fin 161) : Fin (ST x D D1) := cT (sTape (sk x k))

theorem cT_val (i : Fin (TT x)) : (cT (D := D) (D1 := D1) i).val = i.val := rfl
theorem wT_val (j : Fin (Scrub.wk D)) : (wT (x := x) (D1 := D1) j).val = TT x + j.val := rfl
theorem lgT_val : (lgT (x := x) (D := D) (D1 := D1)).val = TT x + Scrub.wk D := rfl
theorem drT_val : (drT (x := x) (D := D) (D1 := D1)).val = TT x + Scrub.wk D + 1 := rfl
theorem kT_val : (kT (x := x) (D := D) (D1 := D1)).val = TT x + Scrub.wk D + 2 := rfl
theorem eT_val (k : Fin (UnaryCalc.tapes D1)) : (eT (x := x) (D := D) k).val = TT x + Scrub.wk D + 3 + k.val := rfl
theorem cs_val (k : Fin 161) : (cs (x := x) (D := D) (D1 := D1) k).val = if k.val = 0 then 0 else k.val + 1 := rfl

theorem cs_lt (k : Fin 161) : (cs (x := x) (D := D) (D1 := D1) k).val < TT x := by
  rw [cs_val]
  have := k.isLt
  unfold TT LNS LNR
  split <;> omega

theorem cT_inj : Function.Injective (cT (x := x) (D := D) (D1 := D1)) := by
  intro a b h
  exact Fin.ext (by simpa [cT_val] using congrArg Fin.val h)

theorem eT_inj : Function.Injective (eT (x := x) (D := D) (D1 := D1)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [eT_val, eT_val] at this
  exact Fin.ext (by omega)

theorem wT_inj : Function.Injective (wT (x := x) (D := D) (D1 := D1)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [wT_val, wT_val] at this
  exact Fin.ext (by omega)

theorem ne_of_val {u : ℕ} {a b : Fin u} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- **A bank is determined by its regions.** -/
theorem regions {α : Type} (B B' : Fin (ST x D D1) → α) (hc : ∀ i, B (cT i) = B' (cT i))
    (hw : ∀ j, B (wT j) = B' (wT j)) (hl : B lgT = B' lgT) (hd : B drT = B' drT) (hk : B kT = B' kT)
    (he : ∀ k, B (eT k) = B' (eT k)) : B = B' := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun k => he k) i
  refine Fin.addCases (fun b => ?_) (fun u => ?_) a
  · refine Fin.addCases (fun c => ?_) (fun u => ?_) b
    · refine Fin.addCases (fun d => ?_) (fun u => ?_) c
      · exact Fin.addCases (fun y => hc y) (fun j => hw j) d
      · have hu : u = 0 := Fin.eq_zero u
        subst hu
        exact hl
    · have hu : u = 0 := Fin.eq_zero u
      subst hu
      exact hd
  · have hu : u = 0 := Fin.eq_zero u
    subst hu
    exact hk

end Tapes

/-! ## Docked runs, lengths, ready runs -/

theorem install_eq {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (L : Fin t → List Bool) (B : Fin u → List Bool) (h1 : ∀ j, B (slots j) = L j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : install slots A L = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot _ hi]
    exact (h1 j).symm
  · have hn : ∀ j, slots j ≠ i := fun j e => h ⟨j, e⟩
    rw [install_other _ _ _ _ hn]
    exact (h2 i hn).symm

theorem dockH_eq {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → ℕ)
    (L : Fin t → ℕ) (B : Fin u → ℕ) (h1 : ∀ j, B (slots j) = L j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : dockH slots A L = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot _ hi]
    exact (h1 j).symm
  · have hn : ∀ j, slots j ≠ i := fun j e => h ⟨j, e⟩
    rw [dockH_other _ _ _ _ hn]
    exact (h2 i hn).symm

/-- **A run's tapes grow by at most its steps.** -/
theorem Step.len {t s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (i : Fin t) (k : ℕ) (hh : hin i ≤ k) (ht : (tin i).length ≤ k) :
    (tout i).length ≤ k + n := by
  obtain ⟨r, hr, _, hT, hs⟩ := h
  have := DecompositionSource.one_tape_support p n ⟨p.start, hin, tin⟩ r i k hr hh ht
  rw [hT] at this
  omega

/-- An all-heads-zero `Step` is a ready run. -/
theorem ready_of_step {t s n : ℕ} {p : Machine t s} {A A' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) A (fun _ => 0) A') : ClockJoin.ReadyRun p n A A' := by
  obtain ⟨r, hr, hH, hT, hs⟩ := h
  exact ⟨r, hr, hT, fun i => by rw [hH], hs⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Shell
