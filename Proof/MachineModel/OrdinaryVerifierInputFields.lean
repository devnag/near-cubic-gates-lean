import Proof.MachineModel.OrdinaryVerifierFieldLoad

/-! One ordinary extraction of all three fixed-U input fields, preserving
the literal source and resetting every field head. The remaining padding is
not copied or parsed. No scalar-value work is hidden in the input scan. -/
namespace NearCubicWires.RepairOrdinary.VerifierInputFields
open LocalBitMultitape
open VerifierFieldLoad (config machine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source (code input bound padding : List Bool) : List Bool :=
  frame code++(frame input++(frame bound++padding))
def budget (code input bound : List Bool) : ℕ := 4*(code.length+input.length+bound.length)+11

theorem fields_run (code input bound padding : List Bool) :
    ∃ r : ExecutionReceipt 7 12,
      run machine (budget code input bound) (SourceHandoff.sourceTapes (source code input bound padding)) = some r ∧
      r.final = config 11 (source code input bound padding)
        ((frame code).length+(frame input).length+(frame bound).length)
        (frame code) (frame input) (frame bound)
        (frame code).length (frame input).length (frame bound).length := by
  obtain ⟨first,hf,hff⟩ := VerifierFieldLoad.code_run [] code (frame input++(frame bound++padding)) [] [] 0 0
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hf hff
  obtain ⟨middle,hm,hmf⟩ := VerifierFieldLoad.input_run (frame code) input (frame bound++padding)
    (frame code) [] (frame code).length 0
  simp only [List.append_assoc] at hm hmf
  obtain ⟨last,hl,hlf⟩ := VerifierFieldLoad.bound_run (frame code++frame input) bound padding
    (frame code) (frame input) (frame code).length (frame input).length
  simp only [List.append_assoc,List.length_append] at hl hlf
  have hmiddle : Composition.restart middle.final VerifierFieldLoad.boundMachine.start =
      config 0 (source code input bound padding) ((frame code).length+(frame input).length)
        (frame code) (frame input) [] (frame code).length (frame input).length 0 := by rw [hmf]; rfl
  dsimp only [source] at hmiddle
  rw [← hmiddle] at hl
  have htail := Composition.run_join VerifierFieldLoad.inputMachine VerifierFieldLoad.boundMachine
    (4*input.length+3) (4*bound.length+3)
    (config 0 (source code input bound padding) (frame code).length (frame code) [] []
      (frame code).length 0 0) middle last hm hl
  have hfirst : Composition.restart first.final VerifierFieldLoad.tailMachine.start =
      Composition.leftConfig 4 (config 0 (source code input bound padding) (frame code).length
        (frame code) [] [] (frame code).length 0 0) := by rw [hff]; rfl
  rw [← hfirst] at htail
  have hall := Composition.run_join VerifierFieldLoad.codeMachine VerifierFieldLoad.tailMachine
    (4*code.length+3) ((4*input.length+3)+1+(4*bound.length+3))
    (config 0 (source code input bound padding) 0 [] [] [] 0 0 0)
    first (Composition.joinedReceipt middle last) hf htail
  have htime : (4*code.length+3)+1+((4*input.length+3)+1+(4*bound.length+3)) =
      budget code input bound := by dsimp [budget]; omega
  rw [htime] at hall
  have hi : Composition.leftConfig 8 (config 0 (source code input bound padding) 0 [] [] [] 0 0 0) =
      initialConfiguration machine (SourceHandoff.sourceTapes (source code input bound padding)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hi] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt middle last),hall,?_⟩
  simp only [Composition.joinedReceipt,hlf]
  rfl

theorem linear_budget (code input bound padding : List Bool) :
    budget code input bound ≤ 4*(source code input bound padding).length := by
  simp only [budget,source,List.length_append,frame_length]
  omega

end NearCubicWires.RepairOrdinary.VerifierInputFields
