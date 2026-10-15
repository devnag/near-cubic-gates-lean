import Proof.PCP.PCPTraversalEmpty

/-! The cold capacity/count producer establishes the exact common invariant;
its capacities and counts are produced from the actual field stream. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldHeads (pos : ℕ) := PCPSerializerCountEntry.finalHeads (heads pos)

theorem Stable.root_heads {cap pos : ℕ} {source countWord : List Bool}
    {h : Fin 128 → ℕ} {t : Fin 128 → List Bool}
    (st : Stable cap source countWord pos [] [false] [] h t) : h=coldHeads pos := by
  funext i
  by_cases h0 : i=0
  · subst i; exact st.sourceHead
  by_cases h2 : i=2
  · subst i; exact st.countHead
  by_cases h80 : i=80
  · subst i; exact st.right.head
  by_cases h81 : i=81
  · subst i; exact st.continuation.head
  by_cases h82 : i=82
  · subst i; exact st.left.head
  simp only [coldHeads,PCPSerializerCountEntry.finalHeads,heads,h81,h0,h2,↓reduceIte]
  by_cases hi : i.val<39
  · exact st.lowHeads i hi h0 h2
  · exact st.workingHeads i (by omega) h80 h81 h82

theorem cold_stable (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ fuel≤entryFuel (mass fields) fields.length,∃ tapes,
      Timed machine fuel (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)
        (atCall 0 (coldHeads pre.length) tapes) ∧
      Stable (PCPPairReusable.capacity (mass fields)) (pre++FieldList.stream fields++suffix)
        (RepairSource.VerifierDecoding.CompareMachine.word fields.length) pre.length [] [false] []
        (coldHeads pre.length) tapes ∧
      CountAt (PCPPairReusable.capacity (mass fields)) fields.length tapes := by
  obtain ⟨fuel,hfuel,tapes,hpath,hsource,hcount,_,hcap,hcurrent,hcont,hlog,hother⟩ := cold_entry pre fields suffix
  rw [stream_mass] at hfuel hcap
  let cap := PCPPairReusable.capacity (mass fields)
  have hreserve := capacity_reserves (mass fields)
  have hn := (mass_bounds fields).1
  have hc : fields.length+2≤cap := by omega
  have hworking : WorkingHeads (coldHeads pre.length) := by
    intro i hi _ hi81 _
    have hi0 : i≠0 := by intro he; subst i; contradiction
    have hi2 : i≠2 := by intro he; subst i; contradiction
    simp only [coldHeads,PCPSerializerCountEntry.finalHeads,heads,hi81,hi0,hi2,↓reduceIte]
  have hlow : LowHeads (coldHeads pre.length) := by
    intro i hi hi0 hi2
    have hi81 : i≠81 := by intro he; subst i; contradiction
    simp only [coldHeads,PCPSerializerCountEntry.finalHeads,heads,hi81,hi0,hi2,↓reduceIte]
  refine ⟨fuel,hfuel,tapes,hpath,?_,?_⟩
  · refine ⟨?_,hworking,hlow,hsource,rfl,hcount,rfl,hcap,?_,?_,?_,?_,?_⟩
    · intro i hi hi127
      by_cases hi79 : i=79
      · subst i; rw [hcurrent,List.length_replicate]; omega
      by_cases hi81 : i=81
      · subst i; rw [hcont]; change 1≤cap; omega
      by_cases hi88 : i=88
      · subst i; rw [hlog,List.length_replicate]; exact hc
      rw [hother i hi hi79 hi81 hi88]
      exact Nat.zero_le cap
    · exact ⟨0,by omega,hother 127 (by decide) (by decide) (by decide) (by decide)⟩
    · exact ⟨rfl,⟨0,hother 80 (by decide) (by decide) (by decide) (by decide)⟩⟩
    · exact ⟨rfl,⟨0,by simpa only [List.replicate_zero,List.append_nil] using hcont⟩⟩
    · exact ⟨rfl,⟨0,hother 82 (by decide) (by decide) (by decide) (by decide)⟩⟩
    · exact hother 78 (by decide) (by decide) (by decide) (by decide)
  · refine ⟨fields.length,by omega,?_⟩
    simpa only [ZeroPadding.pad,List.length_replicate,Nat.sub_self,List.replicate_zero,List.append_nil] using hcurrent

end NearCubicWires.RepairOrdinary.PCPTraversal
