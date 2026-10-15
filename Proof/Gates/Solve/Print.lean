import Proof.Gates.Solve.Euclid
import Proof.Gates.CounterMachine.Interval2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open NearCubicWires.RepairRepresentation (natWord)

def appO (σ : MS) (bs : List Bool) : MS :=
  (σ.sets sOUT (σ.st sOUT ++ bs)).seth sOUT ((σ.st sOUT).length + bs.length)

theorem appO_st (σ : MS) (bs : List Bool) : (appO σ bs).st sOUT = σ.st sOUT ++ bs := by simp [appO]

theorem appO_sh (σ : MS) (bs : List Bool) : (appO σ bs).sh sOUT = ((appO σ bs).st sOUT).length := by
  simp [appO]

theorem appO_same (σ : MS) (bs : List Bool) : SameExcept σ (appO σ bs) [sOUT] [] :=
  SameExcept.trans (sameExcept_sets σ (by simp) _) (sameExcept_seth _ (by simp) _)

theorem appO_appO (σ : MS) (a b : List Bool) : appO (appO σ a) b = appO σ (a ++ b) := by
  apply WState.eq
  · funext j; by_cases hj : j = sOUT
    · subst hj; simp [appO]; ring
    · simp [appO, Function.update_of_ne hj]
  · funext j; by_cases hj : j = sOUT
    · subst hj; simp [appO]
    · simp [appO, Function.update_of_ne hj]
  · simp [appO]
  · simp [appO]

theorem appO_val (σ : MS) (bs : List Bool) (r : Reg) : (appO σ bs).val r = σ.val r := by simp [appO]

/-- The same output append on both sides. -/
theorem At.appO {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (bs : List Bool) :
    At (appO σ0 bs) (appO σ bs) W v := by
  unfold Solve.appO
  rw [h.st (by decide)]
  exact (h.setsO (by decide) _).sethO (by decide) _

section Ops
variable (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ}

/-- A constant bit list onto the output. -/
theorem opEmit (h : At σ0 σ W v) (bs : List Bool) (hO : σ0.sh sOUT = (σ0.st sOUT).length) :
    Runs cap (CounterMachine.emitL sOUT bs) σ (4 * bs.length) (fun τ => At (appO σ0 bs) τ W v) := by
  have e := CounterMachine.emitL_spec cap sOUT bs σ (by rw [h.sh (by decide), h.st (by decide), hO])
  exact Runs.of e (h.appO bs)

/-- The print layout: stream `0` is the output, `1` and `2` the printed words. -/
def pP : Fin 12 ↪ Str := ⟨![sOUT, wQ, wB, 0, 2, 3, 4, 5, 6, 7, 28, 29], by decide⟩

/-- The print registers: `2` holds the width `W + 1`, the rest are scratch. -/
def pQ : Fin 10 ↪ Reg := ⟨![rF, rR, rWL, rS, rT, rG, rK, rT2, rCA, rCW], by decide⟩

/-- Print the word `pP X` (`X ∈ {1, 2}`), then rewind it. -/
def printW (X : Fin 12) : WMX NS NR :=
  .seq (CounterMachine.printL pP pQ X) (.seq (addR rR2 rCS rTa) (.wm (WM.rewind (pP X) rCS)))

/-- The cost of `printW`. -/
def printCost (W : ℕ) : ℕ :=
  NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost (W + 1) + 1 +
    (18 * (2 * (W + 1) + 1) + 3 + 1 + (5 * (2 * (W + 1) + 1) + 1))

theorem natBitLength_le' (x W : ℕ) (hx : x < 2 ^ (W + 1)) : natBitLength x ≤ W + 1 :=
  NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le x (W + 1) (by omega) hx

theorem opPrint (h : At σ0 σ W v) (X : Fin 12) (hX : X = 1 ∨ X = 2)
    (hO : σ0.sh sOUT = (σ0.st sOUT).length) (hWL : σ0.val rWL = W + 1) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1)
    (hx : v (pP X) < 2 ^ (W + 1)) (hcap : 8 * (W + 1) + 8 ≤ cap) :
    Runs cap (printW X) σ (printCost W) (fun τ => At (appO σ0 (natWord (v (pP X)))) τ W v) := by
  have hXw : pP X ∈ wset := by rcases hX with rfl | rfl <;> decide
  have hX0 : X ≠ 0 := by rcases hX with rfl | rfl <;> decide
  have hXO : pP X ≠ sOUT := by rcases hX with rfl | rfl <;> decide
  have hXCS : (pP X) ≠ sOUT := hXO
  set x := v (pP X) with hxd
  have hnb := natBitLength_le' x W hx
  have e1 := CounterMachine.printL_spec pP pQ cap (W + 1) x X hX0 σ (by omega) hx (h.num hXw).1 (h.num hXw).2
    (by show σ.sh sOUT = (σ.st sOUT).length; rw [h.sh (by decide), h.st (by decide), hO])
    (by show σ.val rWL = W + 1; rw [h.val (by decide), hWL])
    (fun r hr => h.zero (by revert r; decide)) hcap
  set ω1 := ((σ.sets (pP 0) (σ.st (pP 0) ++ natWord x)).seth (pP 0) ((σ.st (pP 0)).length + (natWord x).length)).seth
    (pP X) (2 * natBitLength x + 1) with hω1
  have hv1 : ∀ r, ω1.val r = σ.val r := fun r => by simp [hω1]
  have e2 := addR_spec cap (A := rR2) (B := rCS) (T := rTa) (by decide) (by decide) (by decide) ω1
    (by rw [hv1]; exact h.zero (by decide))
    (by rw [hv1, hv1, h.zero (show rCS ∈ zset by decide), h.val (by decide), hR2]; omega)
  rw [hv1, hv1, h.zero (show rCS ∈ zset by decide), h.val (show rR2 ∉ zset by decide), hR2] at e2
  set ω2 := ω1.setv rCS (0 + (2 * (W + 1) + 1)) with hω2
  have e3 := wrewind_spec (cap := cap) (pP X) rCS (2 * (W + 1) + 1) ω2 (by simp [hω2]) (by simp [hω2]; omega)
  refine Runs.of (WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))) ?_
  have e : (ω2.setv rCS 0).seth (pP X) (ω2.sh (pP X) - (2 * (W + 1) + 1)) = appO σ (natWord x) := by
    have hsh : ω2.sh (pP X) = 2 * natBitLength x + 1 := by simp [hω2, hω1]
    rw [hsh, show 2 * natBitLength x + 1 - (2 * (W + 1) + 1) = 0 by omega]
    have hp0 : pP 0 = sOUT := rfl
    apply WState.eq
    · funext j
      by_cases hj : j = pP X
      · subst hj; simp [appO, Function.update_of_ne hXO, (h.num hXw).2]
      · by_cases hj0 : j = sOUT
        · subst hj0; simp [hω2, hω1, appO, hp0, Function.update_of_ne hj]
        · simp [hω2, hω1, appO, hp0, Function.update_of_ne hj, Function.update_of_ne hj0]
    · funext j
      by_cases hj0 : j = sOUT
      · subst hj0; simp [hω2, hω1, appO, hp0]
      · simp [hω2, hω1, appO, hp0, Function.update_of_ne hj0]
    · funext r
      by_cases hr : r = rCS
      · subst hr; simp [hω2, hω1, appO, h.zero (show rCS ∈ zset by decide)]
      · simp [hω2, hω1, appO, Function.update_of_ne hr]
    · simp [hω2, hω1, appO]
  rw [e]
  exact h.appO _

/-- `wQ := n` (`n` from `rNN`, counted down in `rLV`). -/
def wordNP : WMX NS NR :=
  .seq (BinW.zero wQ wZ rF rR) (.seq (addR rNN rLV rTa) (.whr rLV (.seq (WMX.dec rLV) (BinW.inc wQ wZ rF rR))))

/-- The count-loop invariant of `wordNP`. -/
def NInv (σA : MS) (W : ℕ) (v : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1, At σ1 τ W (Function.update v wQ k) ∧ SameExcept σA σ1 [] [rLV]

def wordNCost (W n : ℕ) : ℕ := 41 * (W + 1) + 3 + 1 + (18 * n + 3 + 1 + (n * (41 * (W + 1) + 7 + 4) + 1))

theorem opWordN (h : At σ0 σ W v) {n : ℕ} (hLV : σ0.val rLV = 0) (hNN : σ0.val rNN = n) (hn : n < 2 ^ (W + 1))
    (hcap : n + 2 * (W + 1) + 1 ≤ cap) :
    Runs cap wordNP σ (wordNCost W n) (fun τ => ∃ σ1, At σ1 τ W (Function.update v wQ n) ∧
      SameExcept σ0 σ1 [] [rLV] ∧ σ1.val rLV = 0) := by
  refine Runs.seq (opZero cap h (X := wQ) (by decide) (by decide) (by omega)) (fun τ1 h1 => ?_)
  refine Runs.seq ((opAddR cap h1 (A := rNN) (B := rLV) (by decide) (by decide) (by decide)
    (by rw [hLV, hNN]; omega)).cost (show 18 * σ0.val rNN + 3 ≤ 18 * n + 3 by rw [hNN])) (fun τ2 h2 => ?_)
  rw [hNN, hLV] at h2
  set σ2 := σ0.setv rLV (0 + n) with hσ2
  have hloop := Runs.count (cap := cap) (K := rLV) (body := BinW.inc wQ wZ rF rR) (41 * (W + 1) + 7) n
    (NInv σ2 W v) (by omega) (fun k hk τ ⟨σ1, hτ, hfr⟩ _ => by
      have hτ' := hτ.setv (r := rLV) (by decide) (n - k - 1)
      refine (opInc cap hτ' (X := wQ) (by decide) (by decide) (by simp; omega) (by omega)).post (fun ρ hρ =>
        ⟨⟨σ1.setv rLV (n - k - 1), ?_, hfr.trans (sameExcept_setv σ1 (by simp) _)⟩, ?_⟩)
      · simpa using hρ
      · rw [hρ.val (by decide)]; simp) τ2 ⟨σ2, by simpa using h2, SameExcept.refl _ _ _⟩
    (by rw [h2.val (by decide)]; simp [hσ2])
  refine hloop.post (fun τ ⟨⟨σ3, h3, hfr3⟩, hK⟩ => ⟨σ3, h3, (sameExcept_setv σ0 (by simp) _).trans hfr3, ?_⟩)
  rw [← h3.val (by decide)]; exact hK

end Ops

end NearCubicGates.Close.Solve
