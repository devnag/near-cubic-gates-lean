import Proof.Amplification.RecoveryPCPFormulaResumeScalars
import Proof.Amplification.RecoveryPCPFormulaResumeEntryRun

/-! Cold consumer of the original hierarchy fields. The real scalar
producer and whole formula serializer share only their ten actual data
ports; all serializer scratch begins in fresh blank tapes. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarSlots (i : Fin 66) : Fin 785 := i.castAdd 719
def formulaSlots (i : Fin 716) : Fin 785 :=
  ⟨if i.val=272 then 67 else if i.val=278 then 37 else if i.val=280 then 68 else
    if i.val=309 then 66 else if i.val=310 then 64 else if i.val=312 then 17 else
    if i.val=314 then 3 else if i.val=315 then 31 else if i.val=318 then 58 else
    if i.val=560 then 61 else 69+i.val,by have hi:=i.isLt; split_ifs <;> omega⟩
theorem scalar_injective : Function.Injective scalarSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 785=>i.val) h)
def formulaInverse (i : Fin 785) : Nat :=
  if i.val=67 then 272 else if i.val=37 then 278 else if i.val=68 then 280 else if i.val=66 then 309 else if i.val=64 then 310 else if i.val=17 then 312 else if i.val=3 then 314 else if i.val=31 then 315 else if i.val=58 then 318 else if i.val=61 then 560 else i.val-69
theorem formula_inverse (i : Fin 716) : formulaInverse (formulaSlots i)=i.val := by
  by_cases h272 : i.val=272
  · have he : i=(272 : Fin 716) := Fin.ext h272
    subst i; rfl
  by_cases h278 : i.val=278
  · have he : i=(278 : Fin 716) := Fin.ext h278
    subst i; rfl
  by_cases h280 : i.val=280
  · have he : i=(280 : Fin 716) := Fin.ext h280
    subst i; rfl
  by_cases h309 : i.val=309
  · have he : i=(309 : Fin 716) := Fin.ext h309
    subst i; rfl
  by_cases h310 : i.val=310
  · have he : i=(310 : Fin 716) := Fin.ext h310
    subst i; rfl
  by_cases h312 : i.val=312
  · have he : i=(312 : Fin 716) := Fin.ext h312
    subst i; rfl
  by_cases h314 : i.val=314
  · have he : i=(314 : Fin 716) := Fin.ext h314
    subst i; rfl
  by_cases h315 : i.val=315
  · have he : i=(315 : Fin 716) := Fin.ext h315
    subst i; rfl
  by_cases h318 : i.val=318
  · have he : i=(318 : Fin 716) := Fin.ext h318
    subst i; rfl
  by_cases h560 : i.val=560
  · have he : i=(560 : Fin 716) := Fin.ext h560
    subst i; rfl
  simp only [formulaSlots,h272,h278,h280,h309,h310,h312,h314,h315,h318,h560,ite_false]
  simp only [formulaInverse]
  split_ifs <;> omega
theorem formula_injective : Function.Injective formulaSlots := by
  intro i j h
  apply Fin.ext
  exact (formula_inverse i).symm.trans ((congrArg formulaInverse h).trans (formula_inverse j))

noncomputable def first := RecoveryFocus.machine scalarSlots RecoveryPCPFormulaResumeColdScalars.machine
noncomputable def last := RecoveryFocus.machine formulaSlots RecoveryPCPFormulaResumeSerialize.machine
noncomputable def machine := Composition.machine first last
noncomputable def input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 785) : List Bool :=
  if i.val=0 then frame R.bits else if i.val=28 then frame Q.bits else
  if i.val=66 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=67 then DedupBytes.fields p else if i.val=68 then CompareMachine.word (Codec.clauses p).length else []

noncomputable def entryLookup (p : RawProjectionPCP) (R Q : Nat) (i : Fin 716) : List Bool :=
  if i.val=272 then DedupBytes.fields p else
  if i.val=278 then List.replicate (RecoverySourceClauseLoad.uniformBudget Q R) true else
  if i.val=280 then CompareMachine.word (Codec.clauses p).length else
  if i.val=309 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=310 then frame (List.ofFn (bitInputOfCode R 0)) else
  if i.val=312 then List.replicate (RecoveryProjectionRows.capacity R) true else
  if i.val=314 then CompareMachine.word R else if i.val=315 then CompareMachine.word Q else
  if i.val=318 then CompareMachine.word (2^R-1) else if i.val=560 then List.replicate (2^R) true else []

theorem entry_lookup (p : RawProjectionPCP) (R Q : Nat) (i : Fin 716) :
    RecoveryPCPFormulaResumeSerialize.entryData p R Q (RecoverySourceClauseLoad.uniformBudget Q R) i=
      entryLookup p R Q i := by
  refine Fin.addCases (m:=319) (n:=397) (fun i=>?_) (fun i=>?_) i
  · have h560 : i.val≠560 := by have hi:=i.isLt; omega
    simp only [RecoveryPCPFormulaResumeSerialize.entryData,RecoveryPCPFormulaResumeSerialize.rowData,
      Fin.addCases_left,entryLookup,Fin.val_castAdd,h560,ite_false]
  · have h272 : 319+i.val≠272 := by omega
    have h278 : 319+i.val≠278 := by omega
    have h280 : 319+i.val≠280 := by omega
    have h309 : 319+i.val≠309 := by omega
    have h310 : 319+i.val≠310 := by omega
    have h312 : 319+i.val≠312 := by omega
    have h314 : 319+i.val≠314 := by omega
    have h315 : 319+i.val≠315 := by omega
    have h318 : 319+i.val≠318 := by omega
    have h560 : 319+i.val=560 ↔ i.val=241 := by omega
    simp only [RecoveryPCPFormulaResumeSerialize.entryData,Fin.addCases_right,entryLookup,Fin.val_natAdd,
      h272,h278,h280,h309,h310,h312,h314,h315,h318,ite_false,h560]

theorem zero_randomness (R : Nat) : List.ofFn (bitInputOfCode R 0)=List.replicate R false := by
  have h : bitInputOfCode R 0=(fun _ : Fin R=>false) := by
    funext i
    exact Nat.zero_testBit i.val
  rw [h]
  exact List.ofFn_const R false

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
