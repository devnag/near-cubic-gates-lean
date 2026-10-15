import Proof.Foundations.PCPPClausePadding
import Proof.Foundations.ScheduledRecovery

/-! # Perfect oracle acceptance forces hierarchy acceptance -/

namespace NearCubicWires.TotalSelectorDrivenHierarchyAcceptance

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-- A circuit accepted on every padded outer-PCP row cannot occur on a
hierarchy-NO word.  The proof uses only the published outer soundness bound;
the scheduled source length is positive, so perfect acceptance contradicts
that bound. -/
theorem hierarchy_accepts_of_canonicalAcceptingOracle
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex))
    (oracle : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound requiredDegree)
      (paddedOuterPCP outer) input) :
    source.hierarchyMachine.accepts (sourceLength sourceIndex) input := by
  by_contra hno
  let proof : BitInput
      (2 ^ (paddedOuterPCP outer).nativeWidth
        (sourceLength sourceIndex)) :=
    fun address =>
      oracle.circuit.eval fun bit => address.val.testBit bit.val
  have hproof : ∀ randomness,
      (paddedOuterPCP outer).accepts input proof randomness := by
    intro randomness
    have horacle := oracle.accepts randomness
    unfold acceptsOracleCircuit at horacle
    unfold ProjectionPCP.accepts
    rw [show
      (fun query =>
        proof ((paddedOuterPCP outer).queryAddress input randomness query)) =
      (fun query =>
        oracle.circuit.eval
          (projectedInput (paddedOuterPCP outer) input randomness query)) by
      funext query
      unfold proof ProjectionPCP.queryAddress projectedInput
      congr 1
      funext bit
      rw [binaryAddress_val_eq_ofBits]
      exact Nat.testBit_ofBits_lt _ bit.val bit.isLt]
    exact horacle
  have hfraction :
      (paddedOuterPCP outer).acceptanceFraction input proof = 1 := by
    classical
    unfold ProjectionPCP.acceptanceFraction
    simp only [hproof, Finset.filter_true, Finset.card_univ]
    exact div_self (by positivity)
  have hsound :=
    padProjectionPCP_sound outer.pcp.toSemantic (widthEnvelope outer)
      (nativeWidth_le_widthEnvelope outer) input
      (1 / (((sourceLength sourceIndex + 1 : ℕ) : ℝ) ^ 10))
      (outer.sound (sourceLength sourceIndex) input hno) proof
  change (paddedOuterPCP outer).acceptanceFraction input proof ≤
    1 / (((sourceLength sourceIndex + 1 : ℕ) : ℝ) ^ 10) at hsound
  rw [hfraction] at hsound
  have hlength : (1 : ℝ) < (sourceLength sourceIndex + 1 : ℕ) := by
    exact_mod_cast Nat.add_lt_add_right (by
      simp [sourceLength] : 0 < sourceLength sourceIndex) 1
  have hpower :
      (1 : ℝ) < (((sourceLength sourceIndex + 1 : ℕ) : ℝ) ^ 10) := by
    exact one_lt_pow₀ hlength (by norm_num)
  have hstrict :
      1 / (((sourceLength sourceIndex + 1 : ℕ) : ℝ) ^ 10) < (1 : ℝ) := by
    exact (div_lt_one (by positivity)).2 hpower
  exact (not_lt_of_ge hsound) hstrict

end NearCubicWires.TotalSelectorDrivenHierarchyAcceptance
