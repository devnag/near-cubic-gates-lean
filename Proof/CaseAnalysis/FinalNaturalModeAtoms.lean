import Proof.CaseAnalysis.FinalSiteWireEnvelope
import Proof.CaseAnalysis.RowsEstimatorParityThreshold

/-!
C10 selects one carried circuit class for a whole witness. Systematic parity
is compiled into that same class (paper.tex:611-626,1427-1434,4292-4306).
This module proves actual site-call mode provenance and exact native maps.
It does not select a supplier, claim a physical run, or alter resource caps.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.SupplierPipeline
open NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
noncomputable section

def ModeAtom {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (symmetric : Bool) : Atom pcpp → Prop
  | .systematic _ => True
  | .symmetric _ => symmetric = true
  | .threshold _ => symmetric = false

theorem decodeCoordinate_mode (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2)))
    {gamma : ℝ} (p : Parameters sources gamma) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    (decodeCoordinate sources k clock p x oracle bits j).FactorsSatisfy
      (ModeAtom (CloseoutWitness.BoundedFields.symmetric bits)) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [decodeCoordinate_sym sources k clock p x oracle bits hs j]
    refine mapPolynomial_factorsSatisfy _ _ _ ?_
    intro monomial hmonomial atom hatom
    exact hs
  · rw [decodeCoordinate_thr sources k clock p x oracle bits hs j]
    refine mapPolynomial_factorsSatisfy _ _ _ ?_
    intro monomial hmonomial atom hatom
    exact Bool.eq_false_iff.mpr hs

theorem actual_site_mode (sources : EightSources) (k : ℕ)
    {gamma : ℝ} (p : Parameters sources gamma) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (phase : CloseoutRowsOriginalSchedule.Phase)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)) :
    (siteCalls phase (pcppOf sources k p x bits)
      (stageCoordinate sources k p n x bits) Atom.systematic address).FactorsSatisfy
      (ModeAtom (CloseoutWitness.BoundedFields.symmetric bits)) := by
  apply siteCalls_factorsSatisfy
  · intro j
    exact decodeCoordinate_mode sources k (PolynomialClock.ordinaryClock k) p x
      (oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits j
  · intro j
    trivial

def nativeThresholdAtom {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} : Atom pcpp → NormalizedThresholdThresholdCircuit q
  | .systematic index => normalizedThresholdParityCircuit (pcpp.systematicSupport index)
  | .threshold atom => atom
  | .symmetric _ => normalizedThresholdParityCircuit ∅

theorem nativeThresholdAtom_eval {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atom : Atom pcpp)
    (hmode : ModeAtom false atom) (input : BitInput q) :
    (nativeThresholdAtom atom).eval input = evaluate atom input := by
  cases atom with
  | systematic index => exact normalizedThresholdParityCircuit_eval _ input
  | threshold atom => rfl
  | symmetric atom => cases hmode

theorem nativeThresholdParity_wires {q : ℕ} (support : Finset (Fin q)) :
    (normalizedThresholdParityCircuit support).wireCount =
      support.card * (support.card + 1) := by
  simp [NormalizedThresholdThresholdCircuit.wireCount,
    normalizedThresholdParityCircuit, thresholdParityTopGate,
    thresholdParityBottomGate, SupportedNormalizedGate.wireCount]

theorem nativeThresholdParity_wires_le {q : ℕ} (support : Finset (Fin q)) :
    (normalizedThresholdParityCircuit support).wireCount ≤ q * (q + 1) := by
  rw [nativeThresholdParity_wires]
  have hcard : support.card ≤ q := by
    simpa using Finset.card_le_univ support
  exact Nat.mul_le_mul hcard (Nat.add_le_add_right hcard 1)

def nativeSymmetricAtom {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} : Atom pcpp → NormalizedSymmetricThresholdCircuit q
  | .systematic index => normalizedParityCircuit (pcpp.systematicSupport index)
  | .symmetric atom => atom
  | .threshold _ => normalizedParityCircuit ∅

theorem nativeSymmetricAtom_eval {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atom : Atom pcpp)
    (hmode : ModeAtom true atom) (input : BitInput q) :
    (nativeSymmetricAtom atom).eval input = evaluate atom input := by
  cases atom with
  | systematic index => exact normalizedParityCircuit_eval _ input
  | symmetric atom => rfl
  | threshold atom => cases hmode

theorem conjunctionBit_nativeThreshold {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hmode : ∀ atom ∈ atoms, ModeAtom false atom) (input : BitInput q) :
    conjunctionBit NormalizedThresholdThresholdCircuit.eval
        (atoms.map nativeThresholdAtom) input = conjunctionBit evaluate atoms input := by
  induction atoms with
  | nil => rfl
  | cons head tail ih =>
    change ((nativeThresholdAtom head).eval input &&
      conjunctionBit NormalizedThresholdThresholdCircuit.eval
        (tail.map nativeThresholdAtom) input) = _
    rw [nativeThresholdAtom_eval head (hmode head (by simp)) input,
      ih (fun atom ha => hmode atom (by simp [ha]))]
    rfl

theorem conjunctionProbability_nativeThreshold {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hmode : ∀ atom ∈ atoms, ModeAtom false atom) :
    conjunctionProbability NormalizedThresholdThresholdCircuit.eval
        (atoms.map nativeThresholdAtom) = conjunctionProbability evaluate atoms := by
  unfold conjunctionProbability
  congr 1
  funext input
  exact conjunctionBit_nativeThreshold atoms hmode input

theorem conjunctionBit_nativeSymmetric {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hmode : ∀ atom ∈ atoms, ModeAtom true atom) (input : BitInput q) :
    conjunctionBit NormalizedSymmetricThresholdCircuit.eval
        (atoms.map nativeSymmetricAtom) input = conjunctionBit evaluate atoms input := by
  induction atoms with
  | nil => rfl
  | cons head tail ih =>
    change ((nativeSymmetricAtom head).eval input &&
      conjunctionBit NormalizedSymmetricThresholdCircuit.eval
        (tail.map nativeSymmetricAtom) input) = _
    rw [nativeSymmetricAtom_eval head (hmode head (by simp)) input,
      ih (fun atom ha => hmode atom (by simp [ha]))]
    rfl

theorem conjunctionProbability_nativeSymmetric {q : ℕ} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (Atom pcpp))
    (hmode : ∀ atom ∈ atoms, ModeAtom true atom) :
    conjunctionProbability NormalizedSymmetricThresholdCircuit.eval
        (atoms.map nativeSymmetricAtom) = conjunctionProbability evaluate atoms := by
  unfold conjunctionProbability
  congr 1
  funext input
  exact conjunctionBit_nativeSymmetric atoms hmode input

end
end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
