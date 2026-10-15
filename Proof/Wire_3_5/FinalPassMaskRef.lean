import Proof.Wire_3_5.FinalPassCornerRef
import Proof.Wire_3_5.FinalPassMask
import Proof.Wire_3_5.StarPartition

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.Filters

/-- The negation of an integer threshold gate: `[Σ(−w_i)x_i ≥ 1 − θ] = ¬[Σw_ix_i ≥ θ]`. -/
def negGate {n : ℕ} (g : NormalizedThresholdGate n) : NormalizedThresholdGate n :=
  ⟨fun i => -g.weight i, 1 - g.threshold⟩

theorem eval_negGate {n : ℕ} (g : NormalizedThresholdGate n) (x : BitInput n) :
    (negGate g).eval x = !g.eval x := by
  unfold negGate NormalizedThresholdGate.eval
  have e : (∑ i, -g.weight i * if x i then (1 : ℤ) else 0) = -(∑ i, g.weight i * if x i then (1 : ℤ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [e]
  by_cases h : g.threshold ≤ ∑ i, g.weight i * if x i then (1 : ℤ) else 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-- The doubled atom list of a carrier: each atom, then its negation. -/
def maskGates {n : ℕ} (X : Carrier n) : List (NormalizedThresholdGate n) := X.flatMap fun g => [g, negGate g]

theorem residualPlus_neg {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualPlus (fun x => !T x) c u v = residualMinus T c u v := by
  unfold residualPlus residualMinus mixedDifference
  beta_reduce
  generalize T (xorInput (xorInput c u) v) = a
  generalize T (xorInput c u) = b
  generalize T (xorInput c v) = b'
  generalize T c = d
  cases a <;> cases b <;> cases b' <;> cases d <;> decide

/-- **The residual vector is stage 3's `Z⁺` on the doubled corner word.** -/
theorem residualBits_eq_pop {n : ℕ} (X : Carrier n) (c u v : BitInput n) :
    Carrier.residualBits X c u v = popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v) := by
  rw [(popBits_cornerWord _ c u v).1]
  unfold Carrier.residualBits maskGates
  rw [List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun g _ => ?_
  simp only [List.map_cons, List.map_nil]
  have e : (negGate g).eval = fun x => !g.eval x := funext (eval_negGate g)
  rw [e, residualPlus_neg]

/-- **The residual vector at `x = c+u+v`** is the carrier's residual vector at the sampled pair (`c` a center). -/
theorem inputResidual_point (P : StarParams) {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c)
    (u v : P.Errors) (X : Carrier P.n) :
    inputResidualBits P σ X (P.point c u v) =
      Carrier.residualBits X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) := by
  unfold inputResidualBits
  rw [P.center_point hc, P.leftErrors_point hc, P.rightErrors_point hc]

/-- **The mask at a sampled pair from the corner words**: stage 3 (`popBits true`) then stage 7 (`filterBits`) on the
corner-word writer's output for each carrier's doubled atom list. -/
theorem maskBits_point (P : StarParams) {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c)
    (u v : P.Errors) (carriers : List (Carrier P.n)) (FP : GapParams) (e : GapSeed FP) :
    maskBits P σ carriers FP e (P.point c u v) = carriers.all fun X =>
      filterBits FP e (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c
        (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v))) := by
  show (carriers.all fun X => filterBits FP e (inputResidualBits P σ X (P.point c u v))) = _
  exact congrArg carriers.all (funext fun X => by rw [inputResidual_point P hc, residualBits_eq_pop])

end NearCubicWires.WireExponent3_5.FinalPass.Corner
