import Proof.CaseAnalysis.WitnessSumSeal
import Proof.CaseAnalysis.WitnessFamilyCount

/-! The executed exact-V check and the ordered checked sum identities
produce the same typed family; component canonicality pays its roundtrip. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySeal
open CanonicalWitnessCodec CanonicalBinary RadixSemantics
open PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem checked_family {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ}→Circuit n→ℕ) (limits : LegalSumLimits) (V : ℕ)
    (bits : List Bool) (ss : List (CheckedLegalCircuitSum Circuit wires description limits))
    (hcount : FamilyCount.accepted bits V=true)
    (hcodes : (tree (value bits)).atoms=ss.map (·.code codec)) :
    ∃ family : SumFamily Circuit wires description limits V,
      SumFamily.decode codec wires description limits V (value bits)=some family ∧ family.sums=ss:=by
  obtain ⟨codes,hcode,hlen⟩:=(FamilyCount.decision_exact bits V).mp hcount
  have hlist:codes=ss.map (·.code codec):=by
    rw [←hcode,tree_atoms] at hcodes
    exact hcodes
  have hs:ss.length=V:=by rw [hlist,List.length_map] at hlen;exact hlen
  let family : SumFamily Circuit wires description limits V:=⟨ss,hs⟩
  have he:family.code codec=value bits:=by
    change encodeBalancedList (ss.map (·.code codec))=value bits
    rw [←hlist]
    exact hcode
  refine ⟨family,?_,rfl⟩
  rw [←he]
  exact SumFamily.decode_encode codec family

end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySeal
