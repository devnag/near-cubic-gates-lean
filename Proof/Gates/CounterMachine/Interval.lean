import Proof.Gates.CounterMachine.IntervalVal
import Proof.Gates.CounterMachine.PrintNat
import Proof.Wire_3_5.CompilerMachinePoolConv
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Printing -/

section Print
variable (P : Fin 12 ↪ Fin (ns + 1)) (Q : Fin 10 ↪ Fin nr)

/-- The shared `printNat`, its streams renamed by `P`, its registers by `Q` (`Q 2` holds the width). -/
def printL (X : Fin 12) : WMX ns nr :=
  .wm ((NearCubicWires.WireExponent3_5.FinalPass.Out.P5.printNat X).liftW P Q)

theorem printL_spec (cap W x : ℕ) (X : Fin 12) (hX : X ≠ 0) (ω : WState ns nr) (hW : 1 ≤ W) (hx : x < 2 ^ W)
    (hXst : ω.st (P X) = frame (binary W x)) (hXsh : ω.sh (P X) = 0) (hO : ω.sh (P 0) = (ω.st (P 0)).length)
    (hw : ω.val (Q 2) = W) (hz : ∀ r : Fin 10, r ≠ 2 → ω.val (Q r) = 0) (hcap : 8 * W + 8 ≤ cap) :
    WXExec cap (printL P Q X) ω (((ω.sets (P 0) (ω.st (P 0) ++ natWord x)).seth (P 0)
      ((ω.st (P 0)).length + (natWord x).length)).seth (P X) (2 * natBitLength x + 1))
      (NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost W) := by
  let σ : WState 11 10 := ⟨fun i => ω.sh (P i), fun i => ω.st (P i), fun r => ω.val (Q r), ω.cell⟩
  have hL : LiftW P Q ω σ := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  obtain ⟨ρ, e, h1, h2, h3, h4, h5, h6, h7⟩ := NearCubicWires.WireExponent3_5.FinalPass.Out.P5.printNat_spec' X hX W x σ
    hW hx hXst hXsh hO hw (fun r hr => hz r hr)
  obtain ⟨ω', e', hL', hO'⟩ := WExec.liftW _ cap hcap P P.injective Q Q.injective e ω hL
  refine WXExec.wm (WExec.cast cap e' ?_ le_rfl)
  have hP0 : ∀ i : Fin 12, P i = P 0 → i = 0 := fun i h => P.injective h
  apply WState.eq
  · funext j
    by_cases hj : ∃ i, P i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hL'.sh i]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [WState.seth_sh, WState.sets_sh]
        rw [Function.update_of_ne (P.injective.ne (Ne.symm hX)), Function.update_self]
        have h2' : ρ.sh 0 = (ρ.st 0).length := h2
        have h1' : ρ.st 0 = σ.st 0 ++ natWord x := h1
        rw [h2', h1']; simp [σ]
      · by_cases hiX : i = X
        · subst hiX; simp only [WState.seth_sh, Function.update_self]; exact h7
        · simp only [WState.seth_sh, WState.sets_sh]
          rw [Function.update_of_ne (P.injective.ne hiX), Function.update_of_ne (P.injective.ne hi0)]
          exact h4 i hi0 hiX
    · push Not at hj
      rw [(hO'.1 j hj).1]
      simp only [WState.seth_sh, WState.sets_sh]
      rw [Function.update_of_ne (fun e => hj X e.symm), Function.update_of_ne (fun e => hj 0 e.symm)]
  · funext j
    by_cases hj : ∃ i, P i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hL'.st i]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [WState.seth_st, WState.sets_st, Function.update_self]; exact h1
      · simp only [WState.seth_st, WState.sets_st]
        rw [Function.update_of_ne (P.injective.ne hi0)]
        exact h3 i hi0
    · push Not at hj
      rw [(hO'.1 j hj).2]
      simp only [WState.seth_st, WState.sets_st]
      rw [Function.update_of_ne (fun e => hj 0 e.symm)]
  · funext q
    by_cases hq : ∃ r, Q r = q
    · obtain ⟨r, rfl⟩ := hq
      rw [hL'.val r, h5]; rfl
    · push Not at hq
      rw [hO'.2 q hq]; rfl
  · rw [hL'.cell, h6]; rfl

end Print

/-! ## Reading -/

section Read

def natRead (I K X : Fin (ns + 1)) (C R2 T : Fin nr) : WMX ns nr :=
  .seq (.mach NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convM ![I, K, X])
    (.seq (addR R2 C T) (.wm (WM.rewind X C)))

def natReadCost (W v : ℕ) : ℕ :=
  NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convCost v + 1 + (18 * (2 * W + 1) + 3 + 1 + (5 * (2 * W + 1) + 1))

theorem natRead_spec (cap W kc : ℕ) {I K X : Fin (ns + 1)} (hIK : I ≠ K) (hIX : I ≠ X) (hKX : K ≠ X) {C R2 T : Fin nr}
    (hCR : C ≠ R2) (hCT : C ≠ T) (hRT : R2 ≠ T) (σ : WState ns nr) (pre post : List Bool) (v : ℕ) (hW : 1 ≤ W)
    (hv : v < 2 ^ W) (hI : σ.st I = pre ++ natWord v ++ post) (hIh : σ.sh I = pre.length)
    (hK : σ.st K = false :: List.replicate kc true) (hKh : σ.sh K = 0) (hkc : natBitLength v ≤ kc)
    (hX : σ.st X = frame (binary W 0)) (hXh : σ.sh X = 0) (hC : σ.val C = 0) (hR2 : σ.val R2 = 2 * W + 1)
    (hT : σ.val T = 0) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (natRead I K X C R2 T) σ ((σ.sets X (frame (binary W v))).seth I (pre.length + (natWord v).length))
      (natReadCost W v) := by
  have hinj : Function.Injective ![I, K, X] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hIK.symm, hIX.symm, hKX.symm]
  have hrun := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.conv_run W v hW hv pre post (frame (binary W 0)) kc hkc
  have hL := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le v W hW hv
  have hov : ∀ u : ℕ, overlay (frame (binary W u)) (frame (binary W 0)) = frame (binary W u) := fun u =>
    overlay_short _ _ (by simp [frame_length])
  rw [hov, hov] at hrun
  have esh : (fun j => σ.sh (![I, K, X] j)) = ![pre.length, 0, 0] := by
    funext j; fin_cases j <;> simp [hIh, hKh, hXh]
  have est : (fun j => σ.st (![I, K, X] j)) = ![pre ++ natWord v ++ post, false :: List.replicate kc true,
      frame (binary W 0)] := by
    funext j; fin_cases j <;> simp [hI, hK, hX]
  rw [← esh, ← est] at hrun
  set τ1 := ((σ.sets X (frame (binary W v))).seth X (2 * natBitLength v + 1)).seth I (pre.length + (natWord v).length)
    with hτ1
  have e1 : WXExec cap (WMX.mach NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convM ![I, K, X]) σ τ1
      (NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convCost v) := by
    refine WXExec.mach_of cap hinj hrun ?_ ?_ ?_ rfl rfl
    · intro j; fin_cases j
      · simp [hτ1, Function.update_of_ne hIX, hI]
      · simp [hτ1, Function.update_of_ne hKX, hK]
      · simp [hτ1, Function.update_of_ne hIX.symm]
    · intro j; fin_cases j
      · simp [hτ1]
      · simp [hτ1, Function.update_of_ne hIK.symm, Function.update_of_ne hKX, hKh]
      · simp [hτ1, Function.update_of_ne hIX.symm]
    · intro i hi
      have a : i ≠ I := fun e => hi 0 (by simp [e])
      have b : i ≠ X := fun e => hi 2 (by simp [e])
      simp [hτ1, Function.update_of_ne a, Function.update_of_ne b]
  have e2 := addR_spec cap (A := R2) (B := C) (T := T) hCR.symm hRT (hCT) τ1 (by simp [hτ1, hT])
    (by simp [hτ1, hC, hR2]; omega)
  have v1 : τ1.val = σ.val := by simp [hτ1]
  rw [v1, hC, hR2, Nat.zero_add] at e2
  have e3 := wrewind_spec (cap := cap) X C (2 * W + 1) (τ1.setv C (2 * W + 1)) (by simp) (by simp; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))) ?_ le_rfl
  apply WState.eq
  · funext j
    by_cases hj : j = X
    · subst hj; simp [hτ1, Function.update_of_ne hIX.symm]; omega
    · by_cases hjI : j = I
      · subst hjI; simp [hτ1, Function.update_of_ne hIX]
      · simp [hτ1, Function.update_of_ne hj, Function.update_of_ne hjI]
  · simp [hτ1]
  · funext q
    by_cases hq : q = C
    · subst hq; simp [hC]
    · simp [Function.update_of_ne hq, v1]
  · simp [hτ1]

end Read

end NearCubicGates.Close.CounterMachine
