import Proof.Circuits.DecompositionBitFields

/-! The SAME shared serializer accepts the actual native parser's sentinel
count, including its trailing false cell. This is transport of the same
executed run through finite zero padding, not free deletion of that cell. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSerializerCount
open LocalBitMultitape
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (count : ℕ) (i : Fin 128) : ℕ := if i=2 then count+2 else 0
def input (source : List Bool) (count : ℕ) (i : Fin 128) : List Bool :=
  if i=0 then source else if i=2 then UnaryTemplate.tape count else []
noncomputable def entry (source : List Bool) (pos count : ℕ) :=
  (⟨PCPTraversal.machine.start,PCPTraversal.heads pos,input source count⟩ : Configuration 128 _)

theorem padded_count (count : ℕ) :
    ZeroPadding.pad (count+2) (CompareMachine.word count)=UnaryTemplate.tape count := by
  unfold ZeroPadding.pad CompareMachine.word UnaryTemplate.tape
  simp only [List.length_cons,List.length_replicate]
  have he : count+2-(count+1)=1 := by omega
  rw [he]
  rfl

theorem padded_entry (source : List Bool) (pos count : ℕ) :
    ZeroPadding.config (caps count) (PCPTraversal.entry source pos count)=entry source pos count := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases h0 : i=0
    · subst i
      exact ZeroPadding.pad_zero source
    by_cases h2 : i=2
    · subst i
      exact padded_count count
    change ZeroPadding.pad (caps count i) (PCPTraversal.input source count i)=input source count i
    simp only [caps,input,PCPTraversal.input,h0,h2,ite_false,ZeroPadding.pad_zero]

theorem cold_run (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ r,runFrom PCPTraversal.machine (PCPTraversal.budget (PCPSerializerMass.mass fields))
      (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)=some r ∧
      r.final.tapes 77=ZeroPadding.pad (PCPPairReusable.capacity (PCPSerializerMass.mass fields))
        (frame (PCPTraversal.code fields).bits) ∧
      r.final.tapes 78=(PCPTraversal.code fields).bits ∧
      r.final.tapes 0=pre++FieldList.stream fields++suffix ∧
      r.final.tapes 2=UnaryTemplate.tape fields.length ∧
      r.final.heads=PCPTraversal.coldHeads (pre.length+(FieldList.stream fields).length) ∧
      r.steps ≤ PCPTraversal.budget (PCPSerializerMass.mass fields) := by
  obtain ⟨base,hb,b77,b78,b0,b2,bh,_,bs⟩ := PCPTraversal.cold_run pre fields suffix
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config PCPTraversal.machine (caps fields.length) _ _ base hb
  rw [padded_entry] at hr
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_⟩
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 77)=_
    rw [ZeroPadding.pad_zero,b77]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 78)=_
    rw [ZeroPadding.pad_zero,b78]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 0)=_
    rw [ZeroPadding.pad_zero,b0]
  · rw [rf]
    change ZeroPadding.pad (fields.length+2) (base.final.tapes 2)=_
    rw [b2,padded_count]
  · rw [rf]
    exact bh
  · omega

end NearCubicWires.RepairOrdinary.DecompositionSerializerCount
