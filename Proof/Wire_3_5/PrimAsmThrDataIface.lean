import Proof.Wire_3_5.PrimAsmDataRun
import Proof.Wire_3_5.PrimAsmReqBridge
import Proof.Wire_3_5.PrimTTabThr

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data

/-- **The THR call's counts**: the carriers' sizes, then the tuple's bottom-occurrence count (the THR pool's slice
lengths up to the carriers' doubling, `Records.thrSlices`). -/
def thrCounts {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) :
    List ℕ :=
  carriers.map (·.length) ++ [(PrimT.ThrTab.tupleG Cs).length]

/-- **The THR per-call data stage** (interface): the machine, the tuple table's stream, the cost with its polynomial
bound, and the run from the THR request (the analogue of `Data.data_step`). -/
structure ThrDataStage where
  s : ℕ
  M : Machine (DS + 2 + DR + 1) s
  tabS : Fin (DS + 1)
  cost : ∀ {n : ℕ} (a' : ℕ), (Fin a' → NormalizedThresholdThresholdCircuit n) → List (Stars.Carrier n) → ℕ → ℕ → ℕ
  Cc : ℕ
  Dc : ℕ
  cost_le : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (L W K : ℕ), 1 ≤ a' → a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ L) →
    (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) →
    (∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K) →
    (∀ X ∈ carriers, natBitLength X.code ≤ K) → 2 ≤ n + L →
    ValidatorPolynomialDomination.PolyBounded (cost a' Cs carriers L W) (K + n + L + W) Cc Dc
  run : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl : List Bool) (L W : ℕ), 1 ≤ a' → a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ L) →
    (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) → 2 ≤ n + L →
    natBitLength n + 1 ≤ 2 * W + 2 → 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 →
    2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 →
    (∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2) →
    (∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2) →
    2 * (unaryList (thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2 →
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step M (cost a' Cs carriers L W) (fun _ => 0)
        (Fin.addCases (rawIn (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (thrCounts Cs carriers) ∧
      tout (sTape sIN) =
        RepairOrdinary.frame (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape tabS) = FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []

/-- The data stage's machine has `Data`'s tape count (the check that `ThrDataStage.M` fits `Data.dataM`'s shape). -/
example : ∃ s, Nonempty (Machine (DS + 2 + DR + 1) s) := ⟨_, ⟨dataM⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
