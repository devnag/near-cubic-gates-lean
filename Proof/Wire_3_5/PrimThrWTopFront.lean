import Proof.Wire_3_5.PrimAsmThrDataIface
import Proof.Assembly.Production

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TopFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm

/-- **One circuit's top payload**: its retained top's support size, then its children's exact list word, framed. -/
def payOf (alg : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  frame (natWord c.top.support.card ++ exactListWord (RepairOrdinary.ThresholdRows.children alg c))

/-- The front end's in-ports: the framed request word on `0`, the rest blank. -/
def tfInPorts (w : List Bool) : Fin 9 → List Bool := fun i => if i.val = 0 then frame w else []

/-- The front end's out-ports: the request kept; circuit `i`'s payload on `1 + i`, its native word on `5 + i`. -/
def tfOutPorts (alg : DecompositionAlgorithm) (w : List Bool) {q a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) : Fin 9 → List Bool := fun i =>
  if i.val = 0 then frame w
  else if i.val < 5 then (if h : i.val - 1 < a' then payOf alg (Cs ⟨i.val - 1, h⟩) else [])
  else if h : i.val - 5 < a' then PacketProduction.thrWord (Cs ⟨i.val - 5, h⟩) else []

/-- **The THR front end on ports.** -/
structure TopFrontPort (alg : DecompositionAlgorithm) where
  x : ℕ
  s : ℕ
  M : Machine (9 + x) s
  cost : ℕ → ℕ
  Cc : ℕ
  Dc : ℕ
  cost_poly : ∀ m, ValidatorPolynomialDomination.PolyBounded (cost m) m Cc Dc
  run : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool) (K : ℕ),
    1 ≤ n → 1 ≤ a' → a' ≤ 4 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
    (∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K) →
    ∃ J : Fin x → List Bool, (∀ j, (J j).length ≤ cost (n + K)) ∧
      Step M (cost (n + K)) (fun _ => 0)
        (Fin.addCases (m := 9) (n := x) (motive := fun _ => List Bool)
          (tfInPorts (Data.reqW n true (ReqBridge.thrCodes Cs) codes tl)) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 9) (n := x) (motive := fun _ => List Bool)
          (tfOutPorts alg (Data.reqW n true (ReqBridge.thrCodes Cs) codes tl) Cs) J)

theorem tfOut_pay (alg : DecompositionAlgorithm) (w : List Bool) {q a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) (i : Fin a') (hi : i.val < 4) :
    tfOutPorts alg w Cs ⟨i.val + 1, by omega⟩ = payOf alg (Cs i) := by
  have h1 : i.val + 1 ≠ 0 := by omega
  have h2 : i.val + 1 < 5 := by omega
  have h3 : i.val + 1 - 1 < a' := by have := i.isLt; omega
  simp only [tfOutPorts, h1, h2, h3, if_false, if_true, dif_pos]
  rw [show (⟨i.val + 1 - 1, h3⟩ : Fin a') = i from Fin.ext (by simp)]

theorem tfOut_native (alg : DecompositionAlgorithm) (w : List Bool) {q a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) (i : Fin a') (hi : i.val < 4) :
    tfOutPorts alg w Cs ⟨i.val + 5, by omega⟩ = PacketProduction.thrWord (Cs i) := by
  have h1 : i.val + 5 ≠ 0 := by omega
  have h2 : ¬ i.val + 5 < 5 := by omega
  have h3 : i.val + 5 - 5 < a' := by have := i.isLt; omega
  simp only [tfOutPorts, h1, h2, h3, if_false, dif_neg, dif_pos, not_false_eq_true]
  rw [show (⟨i.val + 5 - 5, h3⟩ : Fin a') = i from Fin.ext (by simp)]

theorem tfOut_req (alg : DecompositionAlgorithm) (w : List Bool) {q a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) : tfOutPorts alg w Cs 0 = frame w := rfl

end NearCubicWires.WireExponent3_5.PrimThrW.TopFront
