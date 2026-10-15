import Proof.Gates.Expand.PolyTabStage4
import Proof.Gates.Expand.Ops2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- The block's scratch numbers. -/
def ubv (i : Fin 9) : Fin (NSx te qa + 1) := sS ⟨21 + i.val, by omega⟩

/-- The number block on the parsed stream `X` (`X` not among `sS 21–29`). -/
def UB (X : Fin (NSx te qa + 1)) (hX : ∀ i : Fin 9, X ≠ ubv i) : Fin 10 ↪ Fin (NSx te qa + 1) :=
  ⟨fun i => if h : i.val = 0 then X else ubv ⟨i.val - 1, by omega⟩, fun a b e => by
    simp only at e
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;> simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true] at e
    · exact Fin.ext (by omega)
    · exact absurd e (hX _)
    · exact absurd e.symm (hX _)
    · have := congrArg Fin.val e; simp [ubv] at this; exact Fin.ext (by omega)⟩

def RB : Fin 12 ↪ Fin NRk :=
  ⟨fun j => rX ⟨52 + j.val, by omega⟩, fun a b e => by
    have := congrArg Fin.val e; simp at this; exact Fin.ext (by omega)⟩

theorem UB_zero (X : Fin (NSx te qa + 1)) (hX : ∀ i : Fin 9, X ≠ ubv i) : UB X hX 0 = X := rfl
theorem UB_succ (X : Fin (NSx te qa + 1)) (hX : ∀ i : Fin 9, X ≠ ubv i) (i : Fin 10) (hi : i.val ≠ 0) :
    UB X hX i = ubv ⟨i.val - 1, by omega⟩ := by
  show (if h : i.val = 0 then X else ubv ⟨i.val - 1, by omega⟩) = _
  rw [dif_neg hi]
@[simp] theorem RB_val (j : Fin 12) : (RB j).val = 164 + j.val := by simp [RB]; omega
@[simp] theorem ubv_val (i : Fin 9) : (ubv (te := te) (qa := qa) i).val = 86 + i.val := by simp [ubv]; omega

/-- Initialize the block: `U 1–9 := 0` (width `rX 42`), then `U 8 := 1`. -/
def initB (X : Fin (NSx te qa + 1)) (hX : ∀ i : Fin 9, X ≠ ubv i) : WX :=
  .seq (initNum (ubv 0) (rX 42) (rX 51)) <| .seq (initNum (ubv 1) (rX 42) (rX 51)) <|
  .seq (initNum (ubv 2) (rX 42) (rX 51)) <| .seq (initNum (ubv 3) (rX 42) (rX 51)) <|
  .seq (initNum (ubv 4) (rX 42) (rX 51)) <| .seq (initNum (ubv 5) (rX 42) (rX 51)) <|
  .seq (initNum (ubv 6) (rX 42) (rX 51)) <| .seq (initNum (ubv 7) (rX 42) (rX 51)) <|
  .seq (initNum (ubv 8) (rX 42) (rX 51)) <| BinW.inc (UB X hX 8) (UB X hX 9) (RB 2) (RB 3)

def v0 : Fin 10 → ℕ := fun i => if i = 8 then 1 else 0

theorem initB_spec (cap : ℕ) (X : Fin (NSx te qa + 1)) (hX : ∀ i : Fin 9, X ≠ ubv i) (Wb : ℕ) (hW : 2 ≤ Wb)
    (σ : WSt) (hb : ∀ i : Fin 9, σ.st (ubv i) = [] ∧ σ.sh (ubv i) = 0) (h42 : σ.val (rX 42) = Wb)
    (h51 : σ.val (rX 51) = 0) (hR : ∀ j : Fin 12, σ.val (RB j) = 0) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap (initB X hX) σ (9 * (initCost Wb + 1) + (41 * Wb + 7))
      (fun τ => EvV (UB X hX) RB Wb (σ.st X) (σ.sh X) 0 v0 τ ∧ SameExcept σ τ (List.ofFn ubv) []) := by
  have n4251 : rX 42 ≠ rX 51 := by polyTabNe
  -- the nine zeros
  have step : ∀ (i : Fin 9) (τ : WSt), τ.st (ubv i) = [] → τ.sh (ubv i) = 0 → τ.val (rX 42) = Wb →
      τ.val (rX 51) = 0 → WXExec cap (initNum (ubv i) (rX 42) (rX 51)) τ (τ.sets (ubv i) (frame (binary Wb 0)))
        (initCost Wb) := fun i τ h1 h2 h3 h4 =>
    initNum_spec cap n4251 τ Wb (by rw [h1]; simp) h2 h3 h4 (by omega)
  have hne : ∀ i j : Fin 9, i ≠ j → ubv (te := te) (qa := qa) i ≠ ubv j := fun i j h e => h (by
    have := congrArg Fin.val e; simp at this; exact Fin.ext this)
  -- explicit chain
  have e0 := step 0 σ (hb 0).1 (hb 0).2 h42 h51
  have s1 := fun (i : Fin 9) (τ : WSt) (hτ : τ.st (ubv i) = σ.st (ubv i) ∧ τ.sh (ubv i) = σ.sh (ubv i))
      (h42' : τ.val (rX 42) = Wb) (h51' : τ.val (rX 51) = 0) =>
    step i τ (by rw [hτ.1, (hb i).1]) (by rw [hτ.2, (hb i).2]) h42' h51'
  set σ1 := σ.sets (ubv 0) (frame (binary Wb 0))
  have e1 := s1 1 σ1 (by simp [σ1, Function.update_of_ne (hne 1 0 (by decide))]) (by simp [σ1, h42]) (by simp [σ1, h51])
  set σ2 := σ1.sets (ubv 1) (frame (binary Wb 0))
  have e2 := s1 2 σ2 (by simp [σ2, σ1, Function.update_of_ne (hne 2 0 (by decide)), Function.update_of_ne (hne 2 1 (by decide))])
    (by simp [σ2, σ1, h42]) (by simp [σ2, σ1, h51])
  set σ3 := σ2.sets (ubv 2) (frame (binary Wb 0))
  have e3 := s1 3 σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hne]) (by simp [σ3, σ2, σ1, h42])
    (by simp [σ3, σ2, σ1, h51])
  set σ4 := σ3.sets (ubv 3) (frame (binary Wb 0))
  have e4 := s1 4 σ4 (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne]) (by simp [σ4, σ3, σ2, σ1, h42])
    (by simp [σ4, σ3, σ2, σ1, h51])
  set σ5 := σ4.sets (ubv 4) (frame (binary Wb 0))
  have e5 := s1 5 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne]) (by simp [σ5, σ4, σ3, σ2, σ1, h42])
    (by simp [σ5, σ4, σ3, σ2, σ1, h51])
  set σ6 := σ5.sets (ubv 5) (frame (binary Wb 0))
  have e6 := s1 6 σ6 (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h42]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h51])
  set σ7 := σ6.sets (ubv 6) (frame (binary Wb 0))
  have e7 := s1 7 σ7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h42]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h51])
  set σ8 := σ7.sets (ubv 7) (frame (binary Wb 0))
  have e8 := s1 8 σ8 (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, h42]) (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, h51])
  set σ9 := σ8.sets (ubv 8) (frame (binary Wb 0))
  have hz : ∀ i : Fin 9, NumOn σ9 (ubv i) Wb 0 := by
    intro i
    refine ⟨?_, ?_⟩
    · fin_cases i <;> simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne]
    · rw [show σ9.sh (ubv i) = σ.sh (ubv i) by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]]; exact (hb i).2
  have hRv : ∀ j : Fin 12, σ9.val (RB j) = 0 := fun j => by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hR j]
  have hU8 : UB X hX 8 = ubv 7 := UB_succ X hX 8 (by decide)
  have hU9 : UB X hX 9 = ubv 8 := UB_succ X hX 9 (by decide)
  have hW1 : 0 + 1 < 2 ^ Wb := by have := Nat.one_lt_two_pow (n := Wb) (by omega); omega
  have e10 := BinW.inc_spec cap Wb (A := UB X hX 8) (B := UB X hX 9) (F := RB 2) (R := RB 3)
    (by rw [hU8, hU9]; exact hne 7 8 (by decide)) (by intro e; exact absurd (RB.injective e) (by decide)) σ9 0 0
    (by rw [hU8]; exact hz 7) (by rw [hU9]; exact hz 8) (hRv 2) (hRv 3) hW1 hcap
  refine ⟨_, WXExec.mono (WXExec.seq e0 <| WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <|
    WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 e10) (by omega), ?_, ?_⟩
  · refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      rw [UB_succ X hX i hi', hU8]
      by_cases h8 : i = 8
      · subst h8; simp [v0]; exact ⟨by simp, (hz 7).2⟩
      · have hne8 : (⟨i.val - 1, by omega⟩ : Fin 9) ≠ 7 := fun e => h8 (by
          have := congrArg Fin.val e; simp at this; exact Fin.ext (by simp; omega))
        rw [show v0 i = 0 by simp [v0, h8]]
        exact ⟨by simp [Function.update_of_ne (hne _ _ hne8)]; exact (hz _).1, by simp; exact (hz _).2⟩
    · rw [UB_zero]
      simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hX 0, hX 1, hX 2, hX 3, hX 4, hX 5, hX 6,
        hX 7, hX 8, hU8]
    · rw [UB_zero]; simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [hRv 1]
    · intro j _ _; simp [hRv j]
  · refine ⟨fun x hx => ?_, fun q _ => by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1], by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]⟩
    have hx' : ∀ i : Fin 9, x ≠ ubv i := fun i e => hx (by rw [e]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)
    have h8x : x ≠ UB X hX 8 := by rw [hU8]; exact hx' 7
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_of_ne h8x, Function.update_apply, hx']

end NearCubicGates.Close.Expand.PolyTab
