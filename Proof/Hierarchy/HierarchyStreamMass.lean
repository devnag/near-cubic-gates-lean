import Proof.Hierarchy.HierarchyStreamReady

/-! The serializer's measured input byte mass is bounded by the actual
normalization execution receipt, including the full native source output.
This closes the resource handoff without assuming a compact-source bound. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Streams
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_mass (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q) :
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length ≤ 1025*(p.word.length+R+Q+1)^3 ∧
    (DedupBytes.fields p).length ≤ 1025*(p.word.length+R+Q+1)^3 := by
  let z := p.word.length+R+Q+1
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hz3 : z ≤ z^3 := Nat.le_self_pow (by decide) z
  have hone : 1 ≤ z^3 := hz.trans hz3
  obtain ⟨r,hactual,hs,hquery,_,hclause,_,_,_,_,_⟩ := streams_run p R Q hr hq
  have hb := budget_bound p R Q hr hq
  change budget p R Q ≤ 1024*z^3 at hb
  have hin (i : Fin 48) : (input p R Q i).length ≤ z := by
    rw [input_literal]
    change (if i=0 then p.word else if i=13 then List.replicate R true else
      if i=14 then List.replicate Q true else []).length ≤ z
    split_ifs
    · dsimp [z]; omega
    · simp only [List.length_replicate]; dsimp [z]; omega
    · simp only [List.length_replicate]; dsimp [z]; omega
    · exact Nat.zero_le _
  have support (i : Fin 48) : (r.final.tapes i).length ≤ 1025*z^3 := by
    have h := RecoveryTapeSupport.run_support machine _ _ r hactual z 0
      (by intro j; exact Nat.zero_le _) (fun j => (hin j).trans (Nat.le_max_left _ _)) i
    have hm : max z (0+r.steps+1) ≤ 1025*z^3 := by
      apply max_le <;> omega
    exact h.trans hm
  refine ⟨?_,?_⟩
  · simpa only [hquery] using support 29
  · simpa only [hclause] using support 38

end NearCubicWires.RepairSource.ProjectionNormalization.Streams
