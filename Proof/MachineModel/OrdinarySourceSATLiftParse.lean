import Proof.MachineModel.OrdinarySourceSATLiftParseState

/-! Cold outer-frame removal, exact source-field isolation and physical
unary-budget extraction, including both parser advances and four returns. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parseBudget (input : List Bool) (b : ℕ) :=
  4*(boundInput input b).length+4*input.length+8*b+16

theorem parse_path (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    Path p 0 4 (parseBudget input b) (fun _ => 0) (parsedHeads p input b)
      (cold p input b) (parsed p input b) := by
  classical
  obtain ⟨ra,hra,hha,hta,hsa⟩ := raw_copy (outerSlots p) (outer_injective p) (fun _ => 0)
    (cold p input b) (boundInput input b) (by intro i; rfl)
    (by rfl) (by simp [outerSlots,parse,cold,Program.inputTapes])
    (by simp [outerSlots,parse,cold,Program.inputTapes])
  have ta := call_trace p 0 1 _ (4*(boundInput input b).length+2) _ _ ra.final
    (ordinary_trace (ports p) _ _ _ ra hra) (prefix_of_run _ _ _ ra hra).2 hsa rfl
  rw [hha,hta] at ta
  change Path p 0 1 (4*(boundInput input b).length+3) (fun _ => 0) (fun _ => 0)
    (cold p input b) (aData p input b) at ta
  obtain ⟨rb,hrb,hhb,htb,hsb⟩ := field_advance (firstSlots p) (first_injective p) (fun _ => 0)
    (aData p input b) [] input (frame (List.replicate b true)) 0 rfl rfl rfl
    (by simp [firstSlots,aData,parse,Function.update,boundInput])
    (by simp [firstSlots,aData,cold,Program.inputTapes,parse,core,Function.update])
    (by simp [firstSlots,aData,cold,Program.inputTapes,parse,Function.update])
  have tb := call_trace p 1 2 _ (4*input.length+4) _ _ rb.final
    (ordinary_trace (ports p) _ _ _ rb hrb) (prefix_of_run _ _ _ rb hrb).2 hsb.le rfl
  rw [hhb,htb] at tb
  simp only [List.length_nil,Nat.zero_add,Nat.zero_max] at tb
  change Path p 1 2 (4*input.length+5) (fun _ => 0) (firstHeads p input)
    (aData p input b) (bData p input b) at tb
  obtain ⟨rc,hrc,hhc,htc,hsc⟩ := field_advance (secondSlots p) (second_injective p) (firstHeads p input)
    (bData p input b) (frame input) (List.replicate b true) [] (2*input.length+1)
    (by simp [firstHeads,secondSlots])
    (by simp [firstHeads,secondSlots,parse,Function.update])
    (by simp [firstHeads,secondSlots,parse,Function.update])
    (by simp [secondSlots,bData,aData,core,zeroCore,parse,Function.update,boundInput])
    (by simp [secondSlots,bData,aData,cold,Program.inputTapes,core,zeroCore,parse,Function.update])
    (by simp [secondSlots,bData])
  simp only [List.length_replicate] at hrc hhc htc hsc
  have tc := call_trace p 2 3 _ (4*b+4) _ _ rc.final
    (ordinary_trace (ports p) _ _ _ rc hrc) (prefix_of_run _ _ _ rc hrc).2 hsc.le rfl
  rw [hhc,htc] at tc
  have hheads : Function.update (firstHeads p input) (parse p 0)
      ((frame input).length+2*b+1)=parsedHeads p input b := by
    simp only [firstHeads,parsedHeads,Function.update_idem,frame_length,boundInput_length]
    congr 1
    omega
  change Path p 2 3 (4*b+5) (firstHeads p input)
    (Function.update (firstHeads p input) (parse p 0) ((frame input).length+2*b+1))
    (bData p input b) (cData p input b) at tc
  rw [hheads] at tc
  obtain ⟨rd,hrd,hhd,htd,hsd⟩ := raw_copy (budgetSlots p) (budget_injective p) (parsedHeads p input b)
    (cData p input b) (List.replicate b true)
    (by intro i; fin_cases i <;> simp [budgetSlots,parsedHeads,parse,power,Function.update])
    (by simp [budgetSlots,cData,parse,Function.update])
    (by simp [budgetSlots,cData,bData,aData,cold,Program.inputTapes,parse,power,core,zeroCore,Function.update])
    (by simp [budgetSlots,cData,bData,aData,cold,Program.inputTapes,parse,core,zeroCore,Function.update])
  simp only [List.length_replicate] at hrd htd hsd
  have td := call_trace p 3 4 _ (4*b+2) _ _ rd.final
    (ordinary_trace (ports p) _ _ _ rd hrd) (prefix_of_run _ _ _ rd hrd).2 hsd rfl
  rw [hhd,htd] at td
  change Path p 3 4 (4*b+3) (parsedHeads p input b) (parsedHeads p input b)
    (cData p input b) (parsed p input b) at td
  have whole := ((ta.trans tb).trans tc).trans td
  convert whole using 1
  unfold parseBudget
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
