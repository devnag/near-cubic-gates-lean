import Proof.CaseAnalysis.WitnessFamilyFromPolicyRun
import Proof.CaseAnalysis.WitnessLegalRun

/-! The actual native request is definitionally the compact source request.
Its paid policy receives the existing uniform source resource bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyResources
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_fits (a : PointwisePCPPAlgorithm) (qc qd G D : ℕ) (delta : ℚ) (copies K E : ℕ)
    (hbudget : ∀ N,FamilyResources.capacity (FamilyResources.sourceScale a qc qd G D delta copies N)≤K*(N+1)^E)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (N : ℕ) (bits : List Bool)
    (hcore : (NativeCache.request a p R Q hR hQ x oracle).arity=R)
    (hRN : R≤N) (hbits : bits.length≤N) (hq : Q≤qc*(R+1)^qd)
    (ho : oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R) :
    let r:=NativeCache.request a p R Q hR hQ x oracle
    let out:=a.output r
    FamilyResources.Fits (FamilyCapacity.value E K N) (out.systematicBits+out.auxiliaryBits)
      (FamilyResources.coefficientCap delta copies D r.arity out.clauseBits)
      (FamilyResources.termCap delta copies D r.arity out.clauseBits)
      (CloseoutMassThreshold.literalWidth delta copies) bits
      (SignedSortKey.binary (natBitLength r.arity) r.arity) ∧
    out.systematicBits+out.auxiliaryBits≤FamilyResources.sourceScale a qc qd G D delta copies N:=by
  let projections:=(p.normalized R Q hR hQ).queryAddressBits x
  let formula:=(p.normalized R Q hR hQ).decision x (fun _ : Fin R=>false)
  have identity:NativeCache.request a p R Q hR hQ x oracle=
      PCPPSubstitution.sourceRequest a oracle projections formula:=rfl
  have arityBound:(SignedSortKey.binary (natBitLength R) R).length≤N+1:=by
    rw [SignedSortKey.binary_length]
    exact (PCPPQueryCost.width_le R).trans (by omega)
  have fits:=FamilyResources.source_fits a qc qd G D delta copies K E hbudget oracle projections formula
    N bits (SignedSortKey.binary (natBitLength R) R) hRN hbits arityBound hq ho
  have counts:=FamilyResources.source_bounds a qc qd G D delta copies oracle projections formula N hRN hq ho
  dsimp only
  constructor
  · have hc:=congrArg (fun u=>FamilyResources.coefficientCap delta copies D u
        (a.output (NativeCache.request a p R Q hR hQ x oracle)).clauseBits) hcore
    have ht:=congrArg (fun u=>FamilyResources.termCap delta copies D u
        (a.output (NativeCache.request a p R Q hR hQ x oracle)).clauseBits) hcore
    have ha:=congrArg (fun u=>SignedSortKey.binary (natBitLength u) u) hcore
    rw [hc,ht,ha,identity]
    exact fits
  · rw [identity]
    exact counts.2.1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyResources
