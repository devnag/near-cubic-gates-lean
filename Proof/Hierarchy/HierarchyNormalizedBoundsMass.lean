import Proof.Hierarchy.HierarchyNormalizedLayout
import Proof.Hierarchy.HierarchyStreamResource
import Proof.PCP.PCPClauseListBounds

/-! The literal four physical scalar words are bounded by the one checked
normalization resource, including the original native source output. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
open RepairOrdinary PCPSerializerMass CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def resource (k CH Cpad : ℕ) (code x : List Bool) :=
  Streams.resource (source.output (HierarchyStreams.request k CH Cpad code x))
    (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)
def wordCoefficient : ℕ := 6+3*513^5
def wordSize (k CH Cpad : ℕ) (code x : List Bool) :=
  PCPOuter.size (HierarchyClauses.words source k CH Cpad code x 0)
    (HierarchyClauses.words source k CH Cpad code x 1)
    (HierarchyClauses.words source k CH Cpad code x 2)
    (HierarchyClauses.words source k CH Cpad code x 3)

theorem query_mass (k CH Cpad : ℕ) (code x : List Bool) :
    mass (HierarchyQuery.fields source k CH Cpad code x)≤resource source k CH Cpad code x := by
  rw [←PCPTraversal.stream_mass]
  change (QueryBytes.framedCodes (normalizedRows
    (source.output (HierarchyStreams.request k CH Cpad code x))
    (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)).flatten).length≤_
  unfold resource Streams.resource
  omega

theorem clause_mass (k CH Cpad : ℕ) (code x : List Bool) :
    (PCPTripleLoop.stream (HierarchyClauses.groups source k CH Cpad code x)).length≤
      resource source k CH Cpad code x := by
  rw [HierarchyClauses.groups,PCPTripleNative.group_stream]
  unfold resource Streams.resource
  omega

theorem bits_length (n : ℕ) : n.bits.length≤n+1 := by
  exact (HierarchySourceScales.bits_length_le n).trans
    (Nat.add_le_add_right (Nat.log_le_self 2 n) 1)

theorem word_size (k CH Cpad : ℕ) (code x : List Bool) :
    wordSize source k CH Cpad code x+1≤wordCoefficient*(resource source k CH Cpad code x+1)^5 := by
  let M := resource source k CH Cpad code x
  have hm : M+1≤(M+1)^5 := Nat.le_self_pow (by decide) _
  have hone : 1≤(M+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hR : HierarchyStreams.R source k CH Cpad code x+1≤M+1 := by
    dsimp [M,resource,Streams.resource]
    omega
  have hQ : HierarchyStreams.Q source k CH Cpad code x+1≤M+1 := by
    dsimp [M,resource,Streams.resource]
    omega
  have br := (bits_length (HierarchyStreams.R source k CH Cpad code x)).trans (hR.trans hm)
  have bq := (bits_length (HierarchyStreams.Q source k CH Cpad code x)).trans (hQ.trans hm)
  have hqm := query_mass source k CH Cpad code x
  have hcm := clause_mass source k CH Cpad code x
  have hq := PCPTraversal.bounded_code (HierarchyQuery.fields source k CH Cpad code x)
    (mass (HierarchyQuery.fields source k CH Cpad code x)) le_rfl
  have bquery : (PCPTraversal.code (HierarchyQuery.fields source k CH Cpad code x)).bits.length≤3*(M+1)^5 :=
    hq.trans (by gcongr)
  have hc := PCPClauseList.output_bound (HierarchyClauses.groups source k CH Cpad code x)
    (PCPTripleNative.group_three _)
  have bclause : (PCPTraversal.code (PCPClauseList.fields (HierarchyClauses.groups source k CH Cpad code x))).bits.length≤
      3*513^5*(M+1)^5 := hc.trans (by gcongr)
  change (HierarchyStreams.R source k CH Cpad code x).bits.length+
    (HierarchyStreams.Q source k CH Cpad code x).bits.length+
    (PCPTraversal.code (HierarchyQuery.fields source k CH Cpad code x)).bits.length+
    (PCPTraversal.code (PCPClauseList.fields (HierarchyClauses.groups source k CH Cpad code x))).bits.length+1≤
      wordCoefficient*(M+1)^5
  unfold wordCoefficient
  omega

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
