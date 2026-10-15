import Proof.PCP.PCPPNativeQueryReusable

/-! Load one actual counted projection row into the reusable query cache.
Only the destination cursor is reset; the retained hierarchy field stream
advances. The real row-width sentinel and G-sized log are preserved. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryRowLoad
open LocalBitMultitape RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 3) := i==1
noncomputable def machine := MaskedReset.machine FieldList.machine selected
def caps (count G : ℕ) : Fin 4 → ℕ := ![0,G,count+2,G]
def input (bits : List Bool) (count G : ℕ) : Fin 4 → List Bool :=
  ![bits,List.replicate G false,UnaryTemplate.tape count,List.replicate G false]
def heads (cursor : ℕ) : Fin 4 → ℕ := ![cursor,0,1,0]
noncomputable def entry (bits : List Bool) (cursor count G : ℕ) :=
  (⟨machine.start,heads cursor,input bits count G⟩ : Configuration 4 _)
def budget (fields : List (List Bool)) := 2*((FieldList.stream fields).length+3*fields.length+3)+2

theorem input_eq (bits : List Bool) (cursor count G : ℕ) :
    ZeroPadding.config (caps count G) (Rewind.recording (FieldList.cfg 0 bits cursor [] count 1) 0)=
      entry bits cursor count G := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero bits
    · exact PCPPNativeNodeReusable.pad_empty G
    · exact DecompositionSerializerCount.padded_count count
    · exact PCPPNativeNodeReusable.pad_empty G

theorem row_run (pre suffix : List Bool) (fields : List (List Bool)) (G : ℕ)
    (hG : (FieldList.stream fields).length+3*fields.length+4 ≤ G) :
    ∃ result,runFrom machine (budget fields)
      (entry (pre++FieldList.stream fields++suffix) pre.length fields.length G)=some result ∧
      result.steps=budget fields ∧
      result.final.heads=heads (pre.length+(FieldList.stream fields).length) ∧
      result.final.tapes=![pre++FieldList.stream fields++suffix,ZeroPadding.pad G (FieldList.stream fields),
        UnaryTemplate.tape fields.length,List.replicate G false] := by
  obtain ⟨raw,hr,rf,rs⟩ := FieldList.copy_run pre fields suffix []
  have hh : ∀ i,selected i=true → raw.final.heads i ≤ raw.steps := by
    intro i hi
    have he : i=1 := by simpa only [selected,beq_iff_eq] using hi
    subst i
    rw [rf,rs]
    change (FieldList.stream fields).length ≤ (FieldList.stream fields).length+3*fields.length+3
    omega
  obtain ⟨reset,hreset,resetFinal,resetSteps,_⟩ := MaskedReset.reset_run FieldList.machine selected _ _ raw hr hh
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine (caps fields.length G) _ _ reset hreset
  rw [rs,input_eq] at hresult
  refine ⟨result,hresult,by rw [resultSteps,resetSteps,rs]; rfl,?_,?_⟩
  · rw [resultFinal,resetFinal,rf]
    funext i
    fin_cases i <;> rfl
  · rw [resultFinal,resetFinal,rf,rs]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad G ([]++FieldList.stream fields)=ZeroPadding.pad G (FieldList.stream fields)
      rw [List.nil_append]
    · exact DecompositionSerializerCount.padded_count fields.length
    · exact PCPPNativeNodeReusable.pad_zeros G _ (by omega)

end NearCubicWires.RepairOrdinary.PCPPNativeQueryRowLoad
