import Proof.Wire_3_5.ListFlatten

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open Finset

namespace FlatListParams
variable (P : FlatListParams) {a : ℕ}

def jointState (Zp Zm : Fin a → List Bool) (e : P.FlatSeed) : Fin a → ℕ × ℕ :=
  fun j => (P.flatReport e (Zp j), P.flatReport e (Zm j))

/-- The joint state indicator `H_{e,τ}`. -/
def jointIndicator (Zp Zm : Fin a → List Bool) (e : P.FlatSeed) (τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1)) : Bool :=
  decide (∀ j, P.jointState Zp Zm e j = ((τ j).1.val, (τ j).2.val))

theorem jointState_exactlyOne (Zp Zm : Fin a → List Bool) (e : P.FlatSeed) :
    ∃! τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1), P.jointIndicator Zp Zm e τ = true := by
  refine ⟨fun j => (⟨P.flatReport e (Zp j), Nat.lt_succ_of_le (P.flatReport_le e _)⟩,
    ⟨P.flatReport e (Zm j), Nat.lt_succ_of_le (P.flatReport_le e _)⟩), ?_, ?_⟩
  · simp [jointIndicator, jointState]
  · intro τ hτ
    simp only [jointIndicator, jointState, decide_eq_true_eq, Prod.mk.injEq] at hτ
    funext j
    ext
    · simp [(hτ j).1]
    · simp [(hτ j).2]

def reportedSym (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool) (e : P.FlatSeed) : Bool :=
  decide (∀ j, g j (score j + P.flatReport e (Zp j) - P.flatReport e (Zm j)) = true)

def trueSym (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool) : Bool :=
  decide (∀ j, g j (score j + (Zp j).count true - (Zm j).count true) = true)

theorem reportedSym_eq_of_correct (g : Fin a → ℤ → Bool) (score : Fin a → ℤ) (Zp Zm : Fin a → List Bool)
    (e : P.FlatSeed) (h : ∀ j, P.flatReport e (Zp j) = (Zp j).count true ∧ P.flatReport e (Zm j) = (Zm j).count true) :
    P.reportedSym g score Zp Zm e = trueSym g score Zp Zm := by
  unfold reportedSym trueSym
  congr 1
  apply propext
  constructor <;> intro hall j <;> have := hall j <;> rwa [(h j).1, (h j).2] at *

theorem reportedSym_fail_le (spectrum : ExpanderSpectrumContract) (g : Fin a → ℤ → Bool) (score : Fin a → ℤ)
    (Zp Zm : Fin a → List Bool) (hlen : ∀ j, (Zp j).length ≤ P.M ∧ (Zm j).length ≤ P.M)
    (hcap : ∀ j, (Zp j).count true ≤ P.B ∧ (Zm j).count true ≤ P.B) :
    booleanMean (fun e : P.FlatSeed => decide (P.reportedSym g score Zp Zm e ≠ trueSym g score Zp Zm)) ≤
      (2 * a : ℕ) * (1 / 2 ^ P.errExp) := by
  have hbound := booleanMean_unionBound_uniform
    (fun e : P.FlatSeed => decide (P.reportedSym g score Zp Zm e ≠ trueSym g score Zp Zm))
    (fun (jb : Fin a × Bool) (e : P.FlatSeed) =>
      decide (P.flatReport e (if jb.2 then Zp jb.1 else Zm jb.1) ≠ (if jb.2 then Zp jb.1 else Zm jb.1).count true))
    (1 / 2 ^ P.errExp)
    (by
      intro e he
      by_contra hno
      push Not at hno
      simp only [decide_eq_true_eq] at he
      apply he
      apply P.reportedSym_eq_of_correct
      intro j
      exact ⟨by simpa using hno (j, true), by simpa using hno (j, false)⟩)
    (by
      rintro ⟨j, b⟩
      cases b
      · exact P.flatReport_fail_le spectrum _ (hlen j).2 (hcap j).2
      · exact P.flatReport_fail_le spectrum _ (hlen j).1 (hcap j).1)
  refine hbound.trans (le_of_eq ?_)
  simp [Fintype.card_prod, mul_comm]

end FlatListParams

end NearCubicWires.WireExponent3_5.Lists
