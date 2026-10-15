import Proof.Hierarchy.HierarchyClauseLayout

/-! Four distinct retained physical scalar fields, with exactly the native
balanced encoding required by the normalized PCP output. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses
open LocalBitMultitape RepairOrdinary CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def fourSlots {u : ℕ} (a b : Fin u) : Fin 4 → Fin (u+128+309) :=
  ![(a.castAdd 128).castAdd 309,(b.castAdd 128).castAdd 309,
    ((77 : Fin 128).natAdd u).castAdd 309,(258 : Fin 309).natAdd (u+128)]

theorem fourSlots_injective {u : ℕ} (a b : Fin u) (hab : a≠b) :
    Function.Injective (fourSlots a b) := by
  have ha := a.isLt
  have hb := b.isLt
  have hvab : a.val≠b.val := fun h => hab (Fin.ext h)
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | skip
  all_goals
    exfalso
    have hv := congrArg Fin.val he
    dsimp [fourSlots] at hv
    omega

theorem bits_distinct (k : ℕ) : HierarchyStreams.bitsR source k≠HierarchyStreams.bitsQ source k := by
  intro he
  have hd := HierarchyStreams.dimension_injective source k he
  have hv := congrArg Fin.val hd
  rw [(HierarchyStreams.bit_values source.degrees.proofLog source.degrees.queries).1,
    (HierarchyStreams.bit_values source.degrees.proofLog source.degrees.queries).2] at hv
  omega

theorem fieldSlots_injective (k : ℕ) : Function.Injective (fieldSlots source k) := by
  apply fourSlots_injective
  intro he
  have hv := congrArg (fun i : Fin (HierarchyStreams.tapes source k) => i.val) he
  exact bits_distinct source k (Fin.ext hv)

theorem words_code (k CH Cpad : ℕ) (code x : List Bool) :
    (PCPTraversal.code [words source k CH Cpad code x 0,words source k CH Cpad code x 1,
      words source k CH Cpad code x 2,words source k CH Cpad code x 3]).bits=
      Codec.word (source.output (HierarchyStreams.request k CH Cpad code x))
        (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) := by
  change (PCPTraversal.code [(HierarchyStreams.R source k CH Cpad code x).bits,
    (HierarchyStreams.Q source k CH Cpad code x).bits,
    (PCPTraversal.code (HierarchyQuery.fields source k CH Cpad code x)).bits,
    (PCPTraversal.code (PCPClauseList.fields (groups source k CH Cpad code x))).bits]).bits=_
  unfold HierarchyQuery.fields groups
  rw [PCPTripleNative.query_code,PCPClauseList.native_code]
  exact PCPTripleNative.outer_code _ _ _

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyClauses
