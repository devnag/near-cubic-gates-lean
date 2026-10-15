import Proof.Gates.Solve.Setup3
import Proof.Gates.CounterMachine.Interval5

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
open StablePartition.Workspace (overlay)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec enc stp)
open NearCubicWires.RepairRepresentation (natWord)

section Ops
variable (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ}

/-- A count field `natWord x` into the register `V` (`V += x`). -/
theorem opReadNat (h : At σ0 σ W v) {V : Reg} (hV : V ∉ zset) (x : ℕ) (pre rest : List Bool)
    (hst : σ0.st sRAW = pre ++ natWord x ++ rest) (hsh : σ0.sh sRAW = pre.length)
    (hcap : σ0.val V + 2 ^ (natBitLength x + 1) ≤ cap) :
    Runs cap (.wm (readNatM false sRAW rCA rCW V rK2 rG)) σ ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40))
      (fun τ => At ((σ0.seth sRAW (pre.length + (natWord x).length)).setv V (σ0.val V + x)) τ W v) := by
  have h1 : rCA ≠ V := fun e => hV (e ▸ by decide)
  have h2 : rCW ≠ V := fun e => hV (e ▸ by decide)
  have h3 : rK2 ≠ V := fun e => hV (e ▸ by decide)
  have h4 : V ≠ rG := fun e => hV (e.symm ▸ by decide)
  have e := readNatM_spec (cap := cap) false sRAW rCA rCW V rK2 rG (by decide) h1 (by decide) (by decide) h2
    (by decide) (by decide) h3 (by decide) h4 x pre rest σ (by rw [h.st (by decide), hst]; rfl)
    (by rw [h.sh (by decide), hsh]) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide))
    (by rw [h.val hV]; exact hcap)
  simp only [stp, Bool.false_eq_true, ↓reduceIte, one_mul] at e
  rw [h.val hV] at e
  exact Runs.of (WXExec.wm e) ((h.sethO (X := sRAW) (by decide) _).setv hV _)

/-- A number field `natWord x` into the word `X` (which holds `0`); ruler on `sRUL`, `rR2 = 2(W+1)+1`. -/
theorem opNatRead (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (hX0 : v X = 0) (x : ℕ) (pre rest : List Bool)
    (hst : σ0.st sRAW = pre ++ natWord x ++ rest) (hsh : σ0.sh sRAW = pre.length)
    (hrul : σ0.st sRUL = false :: List.replicate (W + 1) true) (hrulh : σ0.sh sRUL = 0)
    (hR2 : σ0.val rR2 = 2 * (W + 1) + 1) (hx : x < 2 ^ (W + 1)) (hcap : 4 * (W + 1) + 4 ≤ cap) :
    Runs cap (CounterMachine.natRead sRAW sRUL X rCA rR2 rCW) σ (60 * (W + 2))
      (fun τ => At (σ0.seth sRAW (pre.length + (natWord x).length)) τ W (Function.update v X x)) := by
  have hXR : sRAW ≠ X := fun e => by subst e; revert hX; decide
  have hXU : sRUL ≠ X := fun e => by subst e; revert hX; decide
  have hn := CounterMachine.natRead_spec cap (W + 1) (W + 1) (I := sRAW) (K := sRUL) (X := X) (by decide) hXR hXU
    (C := rCA) (R2 := rR2) (T := rCW) (by decide) (by decide) (by decide) σ pre rest x (by omega) hx
    (by rw [h.st (by decide), hst]) (by rw [h.sh (by decide), hsh]) (by rw [h.st (by decide), hrul])
    (by rw [h.sh (by decide), hrulh]) (NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le x (W + 1)
      (by omega) hx) (by rw [(h.num hX).1, hX0]) (h.num hX).2 (h.zero (by decide)) (by rw [h.val (by decide), hR2])
    (h.zero (by decide)) hcap
  refine Runs.of (WXExec.mono hn (by have := CounterMachine.natReadCost_le (W + 1) x (by omega) hx; omega)) ?_
  have e : (σ.sets X (frame (binary (W + 1) x))).seth sRAW (pre.length + (natWord x).length) =
      (σ.seth sRAW (pre.length + (natWord x).length)).sets X (frame (binary (W + 1) x)) := by
    apply WState.eq <;> rfl
  rw [e]
  exact (h.sethO (X := sRAW) (by decide) _).sets hX x

/-- `X := encS (sval m s)` from the magnitude word `M` and the sign flag `S` (then `S := 0`). -/
theorem opJoin (h : At σ0 σ W v) {M X : Str} (hM : M ∈ wset) (hX : X ∈ wset) (hMX : X ≠ M) {S : Reg}
    (hS : S ∉ zset) (s : Bool) (hSv : σ0.val S = s.toNat) (hm : v M < 2 ^ W) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (SInt.join M X S rF rR) σ (130 * W + 160)
      (fun τ => At (σ0.setv S 0) τ W (Function.update v X (encS (sval (v M) s)))) := by
  have h1 : S ≠ rF := fun e => hS (e ▸ by decide)
  have h2 : S ≠ rR := fun e => hS (e ▸ by decide)
  have e := SInt.join_spec cap W hMX (by decide) h1 h2 σ (v M) (v X) s (h.num hM) hm (h.num hX)
    (by rw [h.val hS, hSv]) (h.zero (by decide)) (h.zero (by decide)) hcap
  exact Runs.of e ((h.sets hX _).setv hS 0 |> fun h' => by
    have e2 : (σ.sets X (frame (binary (W + 1) (encS (sval (v M) s))))).setv S 0 =
        (σ.sets X (frame (binary (W + 1) (encS (sval (v M) s))))).setv S 0 := rfl
    exact h')

/-- `M := |x|`, sign flag `S := [x < 0]` (`S = 0` before). -/
theorem opSplit (h : At σ0 σ W v) {X M : Str} (hX : X ∈ wset) (hM : M ∈ wset) (hXM : X ≠ M) {S : Reg}
    (hS : S ∉ zset) (hS0 : σ0.val S = 0) {x : ℤ} (hvx : v X = encS x) (hx : x.natAbs < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (SInt.split X M S rF rR) σ (76 * W + 125)
      (fun τ => At (σ0.setv S (decide (x < 0)).toNat) τ W (Function.update v M x.natAbs)) := by
  have e := SInt.split_spec (S := S) (F := rF) (R := rR) cap W hXM (by decide) σ x (v M) (h.snum hX hvx hx) (h.num hM)
    (by rw [h.val hS, hS0]) (h.zero (by decide)) (h.zero (by decide)) hcap
  exact Runs.of e ((h.sets hM _).setv hS _)

end Ops

end NearCubicGates.Close.Solve
