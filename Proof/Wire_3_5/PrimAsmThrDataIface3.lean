import Proof.Wire_3_5.PrimAsmThrDataIface2
import Proof.Wire_3_5.PrimThrWJoins

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.Shared

/-- The fourteen THR numbers in register order. -/
def thrNumList (v : PrimThrW.Joins.ThrNumVals) : List ℕ := List.ofFn v.get

/-- **The numbers every THR/HASH unit reads, at fixed positions**: the carriers' count, the THR filter's cap, then the
call's THR numbers (W6's `thrNumVals`). -/
def hashNums (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT : ℕ) :
    List ℕ :=
  carriers.length :: capT :: thrNumList (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length capT)

theorem hashNums_length (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp capT : ℕ) :
    (hashNums P Cs carriers alg Dexp capT).length = 16 := by
  simp [hashNums, thrNumList]

structure ThrDataStage3 (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (capT : ℕ → ℕ)
    extends ThrDataStage2 where
  s3 : ℕ
  M3 : Machine (DS + 2 + DR + 1) s3
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
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step M3 (cost3 a' Cs carriers L W) (fun _ => 0)
        (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (hashNums P Cs carriers alg Dexp (capT P.n) ++ thrCounts Cs carriers) ∧
      tout (sTape sIN) =
        RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape tabS) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
