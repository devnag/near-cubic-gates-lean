import Proof.Wire_3_5.ListConsumer
import Proof.Wire_3_5.RowsSampler

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists Finset

variable {a : ℕ}

def clampState (m t : ℕ) : Fin (m + 1) := if h : t ≤ m then ⟨t, Nat.lt_succ_of_le h⟩ else ⟨0, Nat.succ_pos m⟩

theorem clampState_of_le {m t : ℕ} (h : t ≤ m) : (clampState m t : ℕ) = t := by simp [clampState, h]

def symReportState (m : Fin a → ℕ) (rep : Fin a → ℕ × ℕ) : SymState m :=
  fun j => (clampState (m j) (rep j).1, clampState (m j) (rep j).2)

def symIndicator (m : Fin a → ℕ) (rep : Fin a → ℕ × ℕ) (τ : SymState m) : Bool := decide (τ = symReportState m rep)

theorem symIndicator_sum (m : Fin a → ℕ) (rep : Fin a → ℕ × ℕ) : ∑ τ, bitR (symIndicator m rep τ) = 1 := by
  simp [symIndicator, bitR]

def symReported (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (rep : Fin a → ℕ × ℕ) : Bool :=
  decide (∀ j, g j (score j + symShift m (symReportState m rep) j) = true)

theorem bitR_prod_eq (f : Fin a → Bool) : ∏ j, bitR (f j) = bitR (decide (∀ j, f j = true)) := by
  by_cases h : ∀ j, f j = true
  · simp [h, bitR]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    have hj' : f j = false := by simpa using hj
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj', bitR])]
    have : decide (∀ j, f j = true) = false := by simp; exact ⟨j, hj'⟩
    simp [this, bitR]

theorem symStateSum_eq (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (rep : Fin a → ℕ × ℕ) :
    ∑ τ, bitR (symIndicator m rep τ) * ∏ j, bitR (g j (score j + symShift m τ j)) =
      bitR (symReported m g score rep) := by
  rw [Finset.sum_eq_single (symReportState m rep)]
  · simp only [symIndicator, decide_true, bitR, if_true, one_mul, symReported]
    exact bitR_prod_eq _
  · intro τ _ hne
    simp [symIndicator, hne, bitR]
  · simp

theorem symReported_eq_true_of_correct (P : FlatListParams) (m : Fin a → ℕ) (g : Fin a → ℤ → Bool)
    (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool) (e : P.FlatSeed)
    (hm : ∀ j, (Zp j).length ≤ m j ∧ (Zm j).length ≤ m j)
    (h : ∀ j, P.flatReport e (Zp j) = (Zp j).count true ∧ P.flatReport e (Zm j) = (Zm j).count true) :
    symReported m g score (P.jointState Zp Zm e) = FlatListParams.trueSym g score Zp Zm := by
  unfold symReported FlatListParams.trueSym
  congr 1
  apply propext
  have hshift : ∀ j, symShift m (symReportState m (P.jointState Zp Zm e)) j =
      ((Zp j).count true : ℤ) - (Zm j).count true := by
    intro j
    simp only [symShift, symReportState, FlatListParams.jointState, (h j).1, (h j).2]
    rw [clampState_of_le ((List.count_le_length).trans (hm j).1),
      clampState_of_le ((List.count_le_length).trans (hm j).2)]
  constructor <;> intro hall j <;> have := hall j
  · rw [hshift] at this; rwa [add_sub_assoc]
  · rw [hshift]; rwa [add_sub_assoc] at this

theorem symReported_fail_le (spectrum : ExpanderSpectrumContract) (P : FlatListParams) (m : Fin a → ℕ)
    (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool)
    (hm : ∀ j, (Zp j).length ≤ m j ∧ (Zm j).length ≤ m j)
    (hlen : ∀ j, (Zp j).length ≤ P.M ∧ (Zm j).length ≤ P.M)
    (hcap : ∀ j, (Zp j).count true ≤ P.B ∧ (Zm j).count true ≤ P.B) :
    booleanMean (fun e : P.FlatSeed =>
        decide (symReported m g score (P.jointState Zp Zm e) ≠ FlatListParams.trueSym g score Zp Zm)) ≤
      (2 * a : ℕ) * (1 / 2 ^ P.errExp) := by
  have hbound := booleanMean_unionBound_uniform
    (fun e : P.FlatSeed => decide (symReported m g score (P.jointState Zp Zm e) ≠ FlatListParams.trueSym g score Zp Zm))
    (fun (jb : Fin a × Bool) (e : P.FlatSeed) =>
      decide (P.flatReport e (if jb.2 then Zp jb.1 else Zm jb.1) ≠ (if jb.2 then Zp jb.1 else Zm jb.1).count true))
    (1 / 2 ^ P.errExp)
    (by
      intro e he
      by_contra hno
      push Not at hno
      simp only [decide_eq_true_eq] at he
      apply he
      apply symReported_eq_true_of_correct P m g score Zp Zm e hm
      intro j
      exact ⟨by simpa using hno (j, true), by simpa using hno (j, false)⟩)
    (by
      rintro ⟨j, b⟩
      cases b
      · exact P.flatReport_fail_le spectrum _ (hlen j).2 (hcap j).2
      · exact P.flatReport_fail_le spectrum _ (hlen j).1 (hcap j).1)
  refine hbound.trans (le_of_eq ?_)
  simp [Fintype.card_prod, mul_comm]

end NearCubicWires.WireExponent3_5.Rows
