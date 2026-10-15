import Proof.Gates.Expand.PolyTabStage7

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
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

theorem U0_ne_ubv_off (i : Fin 10) (X : Fin (NSx te qa + 1)) (hX : X.val ≠ 65 ∧ (X.val < 86 ∨ 95 ≤ X.val)) :
    U0 (te := te) (qa := qa) i ≠ X := by
  intro e
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB_zero] at e; have := congrArg Fin.val e; simp at this; omega
  · rw [UB_succ _ _ i hi] at e; have := congrArg Fin.val e; simp at this; omega

theorem evv_setv {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {τ : WSt}
    (h : EvV U0 RB Wb inp hd e v τ) (k : Fin 64) (hk : k.val < 52) (x : ℕ) :
    EvV U0 RB Wb inp hd e v (τ.setv (rX k) x) :=
  evv_transfer h (fun i => by simp) (fun j => by simp [Function.update_of_ne (RB_ne j k hk)])

theorem evv_out {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {τ : WSt}
    (h : EvV U0 RB Wb inp hd e v τ) (X : Fin (NSx te qa + 1)) (hX : ∀ i, U0 i ≠ X) (l : List Bool) (p : ℕ)
    (k : Fin 64) (hk : k.val < 52) (x : ℕ) :
    EvV U0 RB Wb inp hd e v (((τ.sets X l).seth X p).setv (rX k) x) :=
  evv_transfer h (fun i => by simp [Function.update_of_ne (hX i)])
    (fun j => by simp [Function.update_of_ne (RB_ne j k hk)])

/-- The indicator bits in field order. -/
theorem preN_bit (r : TabReq) (c : ℕ) (hc : c < 2 ^ r.k) :
    (preN r)[pN r + 1 + c]? = (bitsL r)[c]? := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k]) ++ (bitsL r ++ ([r.V] ++ (List.ofFn r.role).flatMap roleN)) := by simp [preN]
  rw [e, List.getElem?_append_right (by simp only [List.length_append, List.length_cons, List.length_nil,
    gates_length, innerL, outerL, List.length_ofFn, pN, ps, pk]; omega)]
  have : pN r + 1 + c - ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++
      [r.s] ++ outerL r ++ [2 ^ r.k]).length = c := by
    simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, List.length_ofFn,
      pN, ps, pk]; omega
  rw [this, List.getElem?_append_left (by simp [bitsL]; exact hc)]

theorem bitsL_le (r : TabReq) (c : ℕ) (hc : c < (bitsL r).length) : (bitsL r)[c] ≤ 1 := by
  simp [bitsL]; split_ifs <;> omega

/-- The records of the points `< c` of `H`. -/
def hOut (Wb : ℕ) (r : TabReq) (c : ℕ) : List Bool :=
  ((List.range c).filter fun c' => (bitsL r).getD c' 0 ≠ 0).flatMap fun c' => frame (binary Wb c')

def hBody : WX :=
  .seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX 2) (rX 9)) <|
  .seq (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4) (rX 6)) <|
  .seq (.ifr (rX 5) (appendRecX (U0 3) (sZ 57) (rX 29) (rX 39)) WMX.skip) <|
  .seq (.wm (WM.clear (rX 5))) <| .seq (BinW.inc (U0 3) (U0 9) (RB 2) (RB 3)) (WMX.inc (rX 2))

/-- The loop invariant after `c` points. -/
structure HInv (Wb : ℕ) (r : TabReq) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt) (c : ℕ)
    (τ : WSt) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB Wb inp hd 0 v τ ∧ v 3 = c ∧ v 4 = 0 ∧ v 8 = 1 ∧ v 9 = 0
  out : OutOn τ (sZ 57) (rX 39) (hOut Wb r c) []
  r2 : τ.val (rX 2) = pN r + 1 + c
  z0 : τ.val (rX 0) = 0
  z1 : τ.val (rX 1) = 0
  z9 : τ.val (rX 9) = 0
  z5 : τ.val (rX 5) = 0
  z3 : τ.val (rX 3) = 0
  z4 : τ.val (rX 4) = 0
  z6 : τ.val (rX 6) = 0
  z29 : τ.val (rX 29) = 0
  tb : τ.st (sS 3) = TB
  tbh : τ.sh (sS 3) = 0
  fr : SameExcept σA τ (sZ 57 :: List.ofFn ubv) (rX 2 :: rX 5 :: rX 39 :: rX 19 :: List.ofFn RB)

theorem hOut_succ (Wb : ℕ) (r : TabReq) (c : ℕ) :
    hOut Wb r (c + 1) = hOut Wb r c ++ (if (bitsL r).getD c 0 ≠ 0 then frame (binary Wb c) else []) := by
  unfold hOut
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil, List.getD_eq_getElem?_getD]
  by_cases h : (bitsL r)[c]?.getD 0 = 0
  · simp [h]
  · simp [h]

theorem ne57 (i : Fin 10) : U0 (te := te) (qa := qa) i ≠ sZ 57 := U0_ne_ubv_off i _ (by simp)
theorem ne3 (i : Fin 10) : U0 (te := te) (qa := qa) i ≠ sS 3 := U0_ne_tb i

end NearCubicGates.Close.Expand.PolyTab
