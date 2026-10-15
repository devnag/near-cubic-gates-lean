import Proof.Wire_3_5.PrimAsmThrDataIface3
import Proof.Wire_3_5.PrimAsmPlan
import Proof.Wire_3_5.FinalPassSeamsUni

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.Shared

/-- **The THR per-call data stage, v4**: v3 with `x3` extra scratch tapes for the numbers machine. -/
structure ThrDataStage4 (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (capT : ℕ → ℕ)
    extends ThrDataStage2 where
  x3 : ℕ
  s3 : ℕ
  M3 : Machine (DS + 2 + DR + 1 + x3) s3
  cost3 : ∀ {n : ℕ} (a' : ℕ), (Fin a' → NormalizedThresholdThresholdCircuit n) → List (Stars.Carrier n) → ℕ → ℕ → ℕ
  Cc3 : ℕ
  Dc3 : ℕ
  cost3_le : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (L W K : ℕ), a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ L) →
    (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) →
    (∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K) →
    (∀ X ∈ carriers, natBitLength X.code ≤ K) → 2 ≤ n + L →
    ValidatorPolynomialDomination.PolyBounded (cost3 a' Cs carriers L W) (K + n + L + W) Cc3 Dc3
  /-- W6's capacity need at the request's width (the fill `2W + 2` must reach it) -/
  need : ℕ → ℕ
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ n, need n ≤ Kn * (n + 1) ^ Dn
  run3 : ∀ (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (L W : ℕ), a' ≤ 4 → carriers.length ≤ 2 →
    (∀ i, (Cs i).descriptionBits ≤ L) → (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) → 2 ≤ P.n + L →
    natBitLength P.n + 1 ≤ 2 * W + 2 → 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 →
    2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 →
    (∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2) →
    (∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤ 2 * W + 2) →
    2 * (unaryList (hashNums P Cs carriers alg Dexp (capT P.n) ++ thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2 →
    (∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) → need P.n ≤ 2 * W + 2 →
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ) (J : Fin x3 → List Bool),
      Step M3 (cost3 a' Cs carriers L W) (fun _ => 0)
        (Fin.addCases (m := DS + 2 + DR + 1) (n := x3) (motive := fun _ => List Bool)
          (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W)
            (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := DS + 2 + DR + 1) (n := x3) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) ∧
      (∀ j, (J j).length ≤ cost3 a' Cs carriers L W) ∧
      tout (sTape sOUT) = dataWord (hashNums P Cs carriers alg Dexp (capT P.n) ++ thrCounts Cs carriers) ∧
      tout (sTape sIN) =
        RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape tabS) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []

open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan in
/-- **T's v4 data stage at the gate's call families, uniform constants** (StageU order; `ThrStage3U` over v4). -/
abbrev ThrStage4U (l : Literals) : Type :=
  FinalPass.Seams.StageU l
    (fun F kclk coef A a ha => ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
    (fun S => max S.Dc3 S.Dn) (fun S => S.Cc3 + S.Kn)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
