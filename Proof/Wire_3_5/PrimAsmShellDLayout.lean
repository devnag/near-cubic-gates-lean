import Proof.Wire_3_5.PrimAsmCellLoopD
import Proof.Wire_3_5.PrimAsmDataRun

/-! # PA (d), the writer shell with per-call data, part 1: the layout

The SYM writer's shell (`Shell` with the per-call data stage): the cell (`TT x`), the data tape (the call's counts, kept
through the loop, `CellLoopD`), the scrub entry's calc workspace, the log, the driver, the loop counter, then the
extra tapes: the bound's polynomial run (`UnaryCalc.tapes D1`), the data stage's width run and copier
(`UnaryCalc.tapes D2 + 2`), and the data stage (`Data.DS + 2 + Data.DR + 1`).

* the tapes `cT`, `dT`, `wT`, `lgT`, `drT`, `kT`, `e1T`, `e2T`, `e3T`, `cs`; their values; **`regions`**.

Paper quantity: none (machine plumbing for the writers, whose types carry the paper's tapes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop

/-- The loop's layout with the data tape: cell, data, workspace, log, driver, counter. -/
abbrev LTd (x D : ℕ) : ℕ := (TT x + 1) + Scrub.wk D + 1 + 1 + 1

/-- The first extra region: the bound's polynomial run. -/
abbrev E1 (D1 : ℕ) : ℕ := UnaryCalc.tapes D1

/-- The second extra region: the data stage's width run and the copier's two scratch tapes. -/
abbrev E2 (D2 : ℕ) : ℕ := UnaryCalc.tapes D2 + 2

/-- The third extra region: the data stage. -/
abbrev E3 : ℕ := Data.DS + 2 + Data.DR + 1

/-- The shell's layout. -/
abbrev STd (x D D1 D2 : ℕ) : ℕ := LTd x D + (E1 D1 + E2 D2 + E3)

section Tapes
variable {x D D1 D2 : ℕ}

def cT (i : Fin (TT x)) : Fin (STd x D D1 D2) :=
  Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.castAdd (Scrub.wk D) (Fin.castAdd 1 i))))
def dT : Fin (STd x D D1 D2) :=
  Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.castAdd (Scrub.wk D) (Fin.natAdd (TT x) (0 : Fin 1)))))
def wT (j : Fin (Scrub.wk D)) : Fin (STd x D D1 D2) :=
  Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.natAdd (TT x + 1) j)))
def lgT : Fin (STd x D D1 D2) := Fin.castAdd _ (Fin.castAdd 1 Scrub.logTape)
def drT : Fin (STd x D D1 D2) := Fin.castAdd _ (Fin.castAdd 1 Scrub.driverTape)
def kT : Fin (STd x D D1 D2) := Fin.castAdd _ (Fin.natAdd ((TT x + 1) + Scrub.wk D + 1 + 1) (0 : Fin 1))
def e1T (k : Fin (E1 D1)) : Fin (STd x D D1 D2) := Fin.natAdd (LTd x D) (Fin.castAdd E3 (Fin.castAdd (E2 D2) k))
def e2T (k : Fin (E2 D2)) : Fin (STd x D D1 D2) := Fin.natAdd (LTd x D) (Fin.castAdd E3 (Fin.natAdd (E1 D1) k))
def e3T (k : Fin E3) : Fin (STd x D D1 D2) := Fin.natAdd (LTd x D) (Fin.natAdd (E1 D1 + E2 D2) k)
def cs (k : Fin 161) : Fin (STd x D D1 D2) := cT (sTape (sk x k))

theorem cT_val (i : Fin (TT x)) : (cT (D := D) (D1 := D1) (D2 := D2) i).val = i.val := rfl
theorem dT_val : (dT (x := x) (D := D) (D1 := D1) (D2 := D2)).val = TT x := rfl
theorem wT_val (j : Fin (Scrub.wk D)) : (wT (x := x) (D1 := D1) (D2 := D2) j).val = TT x + 1 + j.val := rfl
theorem lgT_val : (lgT (x := x) (D := D) (D1 := D1) (D2 := D2)).val = TT x + 1 + Scrub.wk D := rfl
theorem drT_val : (drT (x := x) (D := D) (D1 := D1) (D2 := D2)).val = TT x + 1 + Scrub.wk D + 1 := rfl
theorem kT_val : (kT (x := x) (D := D) (D1 := D1) (D2 := D2)).val = TT x + 1 + Scrub.wk D + 2 := rfl
theorem e1T_val (k : Fin (E1 D1)) : (e1T (x := x) (D := D) (D2 := D2) k).val = TT x + 1 + Scrub.wk D + 3 + k.val := rfl
theorem e2T_val (k : Fin (E2 D2)) :
    (e2T (x := x) (D := D) (D1 := D1) k).val = TT x + 1 + Scrub.wk D + 3 + E1 D1 + k.val := by
  simp only [e2T, Fin.val_natAdd, Fin.val_castAdd, LTd]
  omega
theorem e3T_val (k : Fin E3) :
    (e3T (x := x) (D := D) (D1 := D1) (D2 := D2) k).val = TT x + 1 + Scrub.wk D + 3 + (E1 D1 + E2 D2) + k.val := by
  simp only [e3T, Fin.val_natAdd, LTd]
  omega
theorem cs_val (k : Fin 161) : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) k).val = if k.val = 0 then 0 else k.val + 1 := rfl

theorem cs_lt (k : Fin 161) : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) k).val < TT x := by
  rw [cs_val]
  have := k.isLt
  unfold TT LNS LNR
  split <;> omega

theorem ne_of_val {u : ℕ} {a b : Fin u} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem cT_inj : Function.Injective (cT (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  exact Fin.ext (by simpa [cT_val] using congrArg Fin.val h)

theorem e1T_inj : Function.Injective (e1T (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [e1T_val, e1T_val] at this
  exact Fin.ext (by omega)

theorem e2T_inj : Function.Injective (e2T (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [e2T_val, e2T_val] at this
  exact Fin.ext (by omega)

theorem e3T_inj : Function.Injective (e3T (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [e3T_val, e3T_val] at this
  exact Fin.ext (by omega)

theorem wT_inj : Function.Injective (wT (x := x) (D := D) (D1 := D1) (D2 := D2)) := by
  intro a b h
  have := congrArg Fin.val h
  rw [wT_val, wT_val] at this
  exact Fin.ext (by omega)

/-- **A bank is determined by its regions.** -/
theorem regions {α : Type} (B B' : Fin (STd x D D1 D2) → α) (hc : ∀ i, B (cT i) = B' (cT i))
    (hdt : B dT = B' dT) (hw : ∀ j, B (wT j) = B' (wT j)) (hl : B lgT = B' lgT) (hd : B drT = B' drT)
    (hk : B kT = B' kT) (h1 : ∀ k, B (e1T k) = B' (e1T k)) (h2 : ∀ k, B (e2T k) = B' (e2T k))
    (h3 : ∀ k, B (e3T k) = B' (e3T k)) : B = B' := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun z => ?_) i
  · refine Fin.addCases (fun b => ?_) (fun u => ?_) a
    · refine Fin.addCases (fun c => ?_) (fun u => ?_) b
      · refine Fin.addCases (fun d => ?_) (fun u => ?_) c
        · refine Fin.addCases (fun y => ?_) (fun j => hw j) d
          exact Fin.addCases (fun y' => hc y') (fun u => by
            have hu : u = 0 := Fin.eq_zero u
            subst hu
            exact hdt) y
        · have hu : u = 0 := Fin.eq_zero u
          subst hu
          exact hl
      · have hu : u = 0 := Fin.eq_zero u
        subst hu
        exact hd
    · have hu : u = 0 := Fin.eq_zero u
      subst hu
      exact hk
  · refine Fin.addCases (fun y => ?_) (fun k => h3 k) z
    exact Fin.addCases (fun k => h1 k) (fun k => h2 k) y

end Tapes

end NearCubicWires.WireExponent3_5.PrimAsm.ShellD
