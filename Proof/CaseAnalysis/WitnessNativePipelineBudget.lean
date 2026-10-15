import Proof.CaseAnalysis.WitnessNativeScreenBudget

/-! The original guarded native continuation consumes only its actual
source request; all internal short-field envelope premises are discharged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bound (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ) (S Z : ℕ):=
  NativeScreen.bound G Z+1+(NativeCache.bound a Z+1+SourcePolicy.envelope D copies delta S)+1

theorem actual_policy_le (a : PointwisePCPPAlgorithm) (qc qd G D copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR:p.width≤R) (hQ:p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (N : ℕ)
    (hcore:(NativeCache.request a p R Q hR hQ x oracle).arity=R) (hRN:R≤N)
    (hq:Q≤qc*(R+1)^qd) (ho:oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R) :
    let r:=NativeCache.request a p R Q hR hQ x oracle
    SourcePolicy.budget D copies r.arity (a.output r).systematicBits (a.output r).auxiliaryBits
      (a.output r).clauseBits delta≤
      SourcePolicy.envelope D copies delta (FamilyResources.sourceScale a qc qd G D delta copies N) := by
  intro r
  let projections:=(p.normalized R Q hR hQ).queryAddressBits x
  let formula:=(p.normalized R Q hR hQ).decision x (fun _=>false)
  let S:=FamilyResources.sourceScale a qc qd G D delta copies N
  have identity:r=PCPPSubstitution.sourceRequest a oracle projections formula:=rfl
  have core:r.arity=R:=hcore
  have counts:=CloseoutSourceCounts.short_counts a oracle projections formula qc qd G hq ho
  have short:=FamilyResources.counts_bound a qc qd G R N hRN
  have resources:=FamilyResources.source_bounds a qc qd G D delta copies oracle projections formula N hRN hq ho
  have hm:2^(a.output r).clauseBits≤S:=by
    have hs:FamilyResources.countBound (FamilyResources.countCoefficient a qc qd G)
        (FamilyResources.countDegree a qc qd G) N≤S:=by
      dsimp only [S,FamilyResources.sourceScale,FamilyResources.scale]
      omega
    rw [identity]
    exact counts.2.trans (short.trans hs)
  have hV:(a.output r).systematicBits+(a.output r).auxiliaryBits≤S:=by
    rw [identity]
    exact resources.2.1
  have hN:N+1≤S:=resources.1
  apply SourcePolicy.budget_le
  · exact core.le.trans (hRN.trans (by omega))
  · omega
  · omega
  · exact (Nat.lt_two_pow_self).le.trans hm
  · exact hm

theorem budget_le (a : PointwisePCPPAlgorithm) (qc qd D G copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR:p.width≤R) (hQ:p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (N Z : ℕ)
    (hcore:(NativeCache.request a p R Q hR hQ x oracle).arity=R) (hRN:R≤N)
    (hq:Q≤qc*(R+1)^qd) (hz:PCPPNativeResourceCost.sourceParameter oracle p Q≤Z) :
    budget a D G copies delta p R Q hR hQ x oracle≤
      bound a D G copies delta (FamilyResources.sourceScale a qc qd G D delta copies N) Z := by
  have screen:NativeScreen.budget G p R Q oracle.size≤NativeScreen.bound G Z:=
    (NativeScreen.budget_le G p R Q hR hQ oracle).trans (NativeScreen.bound_mono G hz)
  unfold budget bound
  split_ifs with ho
  · have policy:=actual_policy_le a qc qd G D copies delta p R Q hR hQ x oracle N hcore hRN hq ho
    have cache:NativeCache.budget a p R Q hR hQ x oracle≤NativeCache.bound a Z:=by
      apply (NativeCache.budget_le a p R Q hR hQ x oracle).trans
      unfold NativeCache.bound
      gcongr
    dsimp only [NativePolicy.budget]
    omega
  · omega

theorem bound_polynomial (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ) (hD:1≤D)
    {S Z : ℕ→ℕ} (hs:SourcePoly S) (hz:SourcePoly Z) : SourcePoly (fun n=>bound a D G copies delta (S n) (Z n)) := by
  have screen:=NativeScreen.bound_polynomial G hz
  have cache:=NativeCache.bound_polynomial a hz
  have policy:=SourcePolicy.envelope_polynomial D copies delta hD hs
  dsimp only [bound]
  fast_budget_poly

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
