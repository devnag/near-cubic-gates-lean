import Proof.Wire_3_5.CompilerMachinePoolTarget

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

def aL : Fin 2 → Fin 5 := ![0, 1]
def aZL : Fin 2 → Fin 5 := ![0, 2]
def aR : Fin 2 → Fin 5 := ![0, 3]
def aZR : Fin 2 → Fin 5 := ![0, 4]

theorem aL_inj : Function.Injective aL := by decide

theorem install_aL (A : Fin 5 → List Bool) (v : Fin 2 → List Bool) :
    install aL A v = ![v 0, v 1, A 2, A 3, A 4] := by
  funext i
  fin_cases i
  · exact install_slot aL aL_inj A v 0
  · exact install_slot aL aL_inj A v 1
  · exact install_other aL A v 2 (by decide)
  · exact install_other aL A v 3 (by decide)
  · exact install_other aL A v 4 (by decide)

theorem dockH_aL (H : Fin 5 → ℕ) (v : Fin 2 → ℕ) :
    dockH aL H v = ![v 0, v 1, H 2, H 3, H 4] := by
  funext i
  fin_cases i
  · exact dockH_slot aL aL_inj H v 0
  · exact dockH_slot aL aL_inj H v 1
  · exact dockH_other aL H v 2 (by decide)
  · exact dockH_other aL H v 3 (by decide)
  · exact dockH_other aL H v 4 (by decide)

theorem aZL_inj : Function.Injective aZL := by decide

theorem install_aZL (A : Fin 5 → List Bool) (v : Fin 2 → List Bool) :
    install aZL A v = ![v 0, A 1, v 1, A 3, A 4] := by
  funext i
  fin_cases i
  · exact install_slot aZL aZL_inj A v 0
  · exact install_other aZL A v 1 (by decide)
  · exact install_slot aZL aZL_inj A v 1
  · exact install_other aZL A v 3 (by decide)
  · exact install_other aZL A v 4 (by decide)

theorem dockH_aZL (H : Fin 5 → ℕ) (v : Fin 2 → ℕ) :
    dockH aZL H v = ![v 0, H 1, v 1, H 3, H 4] := by
  funext i
  fin_cases i
  · exact dockH_slot aZL aZL_inj H v 0
  · exact dockH_other aZL H v 1 (by decide)
  · exact dockH_slot aZL aZL_inj H v 1
  · exact dockH_other aZL H v 3 (by decide)
  · exact dockH_other aZL H v 4 (by decide)

theorem aR_inj : Function.Injective aR := by decide

theorem install_aR (A : Fin 5 → List Bool) (v : Fin 2 → List Bool) :
    install aR A v = ![v 0, A 1, A 2, v 1, A 4] := by
  funext i
  fin_cases i
  · exact install_slot aR aR_inj A v 0
  · exact install_other aR A v 1 (by decide)
  · exact install_other aR A v 2 (by decide)
  · exact install_slot aR aR_inj A v 1
  · exact install_other aR A v 4 (by decide)

theorem dockH_aR (H : Fin 5 → ℕ) (v : Fin 2 → ℕ) :
    dockH aR H v = ![v 0, H 1, H 2, v 1, H 4] := by
  funext i
  fin_cases i
  · exact dockH_slot aR aR_inj H v 0
  · exact dockH_other aR H v 1 (by decide)
  · exact dockH_other aR H v 2 (by decide)
  · exact dockH_slot aR aR_inj H v 1
  · exact dockH_other aR H v 4 (by decide)

theorem aZR_inj : Function.Injective aZR := by decide

theorem install_aZR (A : Fin 5 → List Bool) (v : Fin 2 → List Bool) :
    install aZR A v = ![v 0, A 1, A 2, A 3, v 1] := by
  funext i
  fin_cases i
  · exact install_slot aZR aZR_inj A v 0
  · exact install_other aZR A v 1 (by decide)
  · exact install_other aZR A v 2 (by decide)
  · exact install_other aZR A v 3 (by decide)
  · exact install_slot aZR aZR_inj A v 1

theorem dockH_aZR (H : Fin 5 → ℕ) (v : Fin 2 → ℕ) :
    dockH aZR H v = ![v 0, H 1, H 2, H 3, v 1] := by
  funext i
  fin_cases i
  · exact dockH_slot aZR aZR_inj H v 0
  · exact dockH_other aZR H v 1 (by decide)
  · exact dockH_other aZR H v 2 (by decide)
  · exact dockH_other aZR H v 3 (by decide)
  · exact dockH_slot aZR aZR_inj H v 1

/-- The four appends. -/
noncomputable def appA := Composition.machine (RecoveryFocus.machine aL appLoopD) (Composition.machine
  (RecoveryFocus.machine aZL appLoopD) (Composition.machine (RecoveryFocus.machine aR appLoopD)
    (RecoveryFocus.machine aZR appLoopD)))
/-- The four appends with the four source heads returned to `0` (log on tape 5). -/
noncomputable def appR := MaskedReset.machine appA (fun i => decide (i ≠ 0))

def appLoopCost (W m : ℕ) : ℕ := m * (2 * W + 1 + 1 + 1 + 2) + 1

def appCost (W a b c d : ℕ) : ℕ := appLoopCost W a + 1 + (appLoopCost W b + 1 + (appLoopCost W c + 1 + appLoopCost W d))

theorem app_one (slots : Fin 2 → Fin 5) (hi : Function.Injective slots) (E N : List (List Bool)) (staleO Sv : List Bool)
    (W : ℕ) (hN : ∀ r ∈ N, r.length = W) (hW : 1 ≤ W) (H : Fin 5 → ℕ) (A : Fin 5 → List Bool)
    (hH0 : H (slots 0) = (E.flatMap frame).length) (hH1 : H (slots 1) = 0)
    (hA0 : A (slots 0) = overlay (E.flatMap frame) Sv) (hA1 : A (slots 1) = streamTape N staleO) :
    Step (RecoveryFocus.machine slots appLoopD) (appLoopCost W N.length) H A
      (dockH slots H ![((E ++ N).flatMap frame).length, (N.flatMap frame).length])
      (install slots A ![overlay ((E ++ N).flatMap frame) Sv, streamTape N staleO]) :=
  dockRun (app_loop N E staleO Sv W hN hW) slots hi H A (by intro k; fin_cases k <;> simp [hH0, hH1])
    (by intro k; fin_cases k <;> simp [hA0, hA1])

/-- **One dense child's four streams appended to the pool** (the four source heads back at `0`). -/
theorem app_run (E NL ZL NR ZR : List (List Bool)) (Sv sL sZL sR sZR : List Bool) (W cap : ℕ)
    (hNL : ∀ r ∈ NL, r.length = W) (hZL : ∀ r ∈ ZL, r.length = W) (hNR : ∀ r ∈ NR, r.length = W)
    (hZR : ∀ r ∈ ZR, r.length = W) (hW : 1 ≤ W) (hcap : appCost W NL.length ZL.length NR.length ZR.length ≤ cap) :
    Step appR (2 * appCost W NL.length ZL.length NR.length ZR.length + 2)
      (Fin.addCases ![(E.flatMap frame).length, 0, 0, 0, 0] (fun _ : Fin 1 => 0))
      (Fin.addCases ![overlay (E.flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR,
        streamTape ZR sZR] (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases ![((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame).length, 0, 0, 0, 0] (fun _ : Fin 1 => 0))
      (Fin.addCases ![overlay ((E ++ NL ++ ZL ++ NR ++ ZR).flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL,
        streamTape NR sR, streamTape ZR sZR] (fun _ : Fin 1 => List.replicate cap false)) := by
  have e1 := app_one aL aL_inj E NL sL Sv W hNL hW ![(E.flatMap frame).length, 0, 0, 0, 0]
    ![overlay (E.flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR, streamTape ZR sZR]
    rfl rfl rfl rfl
  rw [install_aL, dockH_aL] at e1
  have e2 := app_one aZL aZL_inj (E ++ NL) ZL sZL Sv W hZL hW
    ![((E ++ NL).flatMap frame).length, (NL.flatMap frame).length, 0, 0, 0]
    ![overlay ((E ++ NL).flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR, streamTape ZR sZR]
    rfl rfl rfl rfl
  rw [install_aZL, dockH_aZL] at e2
  have e3 := app_one aR aR_inj (E ++ NL ++ ZL) NR sR Sv W hNR hW
    ![((E ++ NL ++ ZL).flatMap frame).length, (NL.flatMap frame).length, (ZL.flatMap frame).length, 0, 0]
    ![overlay ((E ++ NL ++ ZL).flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR,
      streamTape ZR sZR] rfl rfl rfl rfl
  rw [install_aR, dockH_aR] at e3
  have e4 := app_one aZR aZR_inj (E ++ NL ++ ZL ++ NR) ZR sZR Sv W hZR hW
    ![((E ++ NL ++ ZL ++ NR).flatMap frame).length, (NL.flatMap frame).length, (ZL.flatMap frame).length,
      (NR.flatMap frame).length, 0]
    ![overlay ((E ++ NL ++ ZL ++ NR).flatMap frame) Sv, streamTape NL sL, streamTape ZL sZL, streamTape NR sR,
      streamTape ZR sZR] rfl rfl rfl rfl
  rw [install_aZR, dockH_aZR] at e4
  have j := (e1.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
    ((e2.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
      ((e3.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).seq
        (e4.congr (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))))
  have hm := j.mask (fun i => decide (i ≠ 0)) (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
