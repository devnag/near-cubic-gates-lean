import Proof.PCP.PCPTripleEnvelope

/-! Exact repeated-call data endpoint. The erase log is retained at its
stabilized length, so the next call starts from literally the same bank. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyTapes (capacity log : ℕ) (source : List Bool) (count : ℕ)
    (out : List Bool) (i : Fin 132) : List Bool :=
  if i=0 then source else if i=2 then CompareMachine.word count
  else if i=129 then out else if i=130 then List.replicate capacity true
  else if i=131 then List.replicate log false else List.replicate capacity false

theorem bodyEntry_heads (capacity log : ℕ) (source : List Bool) (pos count : ℕ)
    (out : List Bool) : (bodyEntry capacity log source pos count out).heads=bodyHeads pos out.length := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config,serializerEntry,
    ZeroPadding.config,Rewind.recording,Rewind.config,PCPTraversal.entry]
  conv_rhs => unfold bodyHeads serializerHeads

theorem bodyEntry_tapes (capacity log : ℕ) (source : List Bool) (pos count : ℕ)
    (out : List Bool) :
    (bodyEntry capacity log source pos count out).tapes=bodyTapes capacity log source count out := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config,serializerEntry,
    ZeroPadding.config,Rewind.recording,Rewind.config,PCPTraversal.entry]
  funext i
  refine Fin.addCases (m:=129) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=128) (n:=1) (fun k => ?_) (fun k => ?_) j
    · simp only [Fin.addCases_left]
      by_cases h0 : k=0
      · subst k
        simp [caps,PCPTraversal.input,bodyTapes]
      by_cases h2 : k=2
      · subst k
        simp [caps,PCPTraversal.input,bodyTapes]
      have hv0 : k.val≠0 := fun h => h0 (Fin.ext h)
      have hv2 : k.val≠2 := fun h => h2 (Fin.ext h)
      have h129 : k.val≠129 := by omega
      have h130 : k.val≠130 := by omega
      have h131 : k.val≠131 := by omega
      simp [caps,PCPTraversal.input,bodyTapes,Fin.ext_iff,hv0,hv2,h129,h130,h131,ZeroPadding.pad]
    · simp only [Fin.addCases_right]
      fin_cases k
      simp [caps,bodyTapes,ZeroPadding.pad]
  · simp only [Fin.addCases_right]
    fin_cases j <;> rfl

theorem scratch_covers (i : Fin 132) (h0 : i≠0) (h2 : i≠2)
    (h129 : i≠129) (h130 : i≠130) (h131 : i≠131) : ∃ j,scratchSlots j=i := by
  by_cases h1 : i=1
  · exact ⟨0,by rw [h1]; rfl⟩
  have hi := i.isLt
  have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
  have hv1 : i.val≠1 := fun h => h1 (Fin.ext h)
  have hv2 : i.val≠2 := fun h => h2 (Fin.ext h)
  have hv129 : i.val≠129 := fun h => h129 (Fin.ext h)
  have hv130 : i.val≠130 := fun h => h130 (Fin.ext h)
  have hv131 : i.val≠131 := fun h => h131 (Fin.ext h)
  refine ⟨⟨i.val-2,by omega⟩,?_⟩
  apply Fin.ext
  simp only [scratchSlots,show i.val-2≠0 by omega,ite_false]
  omega

theorem Result.tapes_eq {s : ℕ} {capacity log pos count : ℕ} {source out : List Bool}
    {final : Configuration 132 s} (h : Result capacity log pos count source out final) :
    final.tapes=bodyTapes capacity (max log (capacity+1)) source count out := by
  rcases h with ⟨_,h0,h2,ho,hd,hl,hs⟩
  funext i
  by_cases hi0 : i=0
  · simpa only [hi0,bodyTapes,ite_true] using h0
  by_cases hi2 : i=2
  · subst i; simpa only [bodyTapes,show (2 : Fin 132)≠0 by decide,ite_false,ite_true] using h2
  by_cases hi129 : i=129
  · subst i; simpa only [bodyTapes,hi0,hi2,ite_false,ite_true] using ho
  by_cases hi130 : i=130
  · subst i; simpa only [bodyTapes,hi0,hi2,hi129,ite_false,ite_true] using hd
  by_cases hi131 : i=131
  · subst i; simpa only [bodyTapes,hi0,hi2,hi129,hi130,ite_false,ite_true] using hl
  obtain ⟨j,hj⟩ := scratch_covers i hi0 hi2 hi129 hi130 hi131
  simpa only [bodyTapes,hi0,hi2,hi129,hi130,hi131,ite_false,hj] using hs j

theorem body_repeated_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool)
    (capacity : ℕ) (hcap : PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine (6*capacity+8)
      (bodyEntry capacity (capacity+1) (pre++FieldList.stream fields++suffix) pre.length fields.length out)=some r ∧
      r.final.heads=(bodyEntry capacity (capacity+1) (pre++FieldList.stream fields++suffix)
        (pre.length+(FieldList.stream fields).length) fields.length (out++frame (PCPTraversal.code fields).bits)).heads ∧
      r.final.tapes=(bodyEntry capacity (capacity+1) (pre++FieldList.stream fields++suffix)
        (pre.length+(FieldList.stream fields).length) fields.length (out++frame (PCPTraversal.code fields).bits)).tapes ∧
      r.steps ≤ 6*capacity+8 := by
  obtain ⟨r,hr,hresult,hs⟩ := body_uniform_run pre fields suffix out capacity (capacity+1) hcap
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [bodyEntry_heads]
    exact hresult.1
  · rw [bodyEntry_tapes]
    simpa only [max_self] using hresult.tapes_eq

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
