import Proof.CaseAnalysis.CaseTwoNativeConverter

/-! The existing converter's literal cold tape image: only its original
description, paid widths, capacity driver and reset logs are nonempty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
open LocalBitMultitape RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeInput (R B C : ℕ) (description : List Bool) (j : Fin 74):=
  if j=0 then ZeroPadding.pad C description
  else if j=3 then ZeroPadding.pad C (List.replicate 6 true)
  else if j=23 then List.replicate C true
  else if j=24 then List.replicate (C+1) false
  else if j=26 then List.replicate (16*(C+1)) false
  else if j=28 then ZeroPadding.pad C (List.replicate (R+B+1) true)
  else if j=32 then List.replicate R true
  else if j.val≤22 ∨ j=25 then List.replicate C false else []

theorem native_input_eq {R : ℕ} (B C : ℕ) (c : BooleanCircuit R) (hC : 1≤C) :
    nativeInput R B C (frame (canonicalBoundedCircuitDescription B c))=NativeConverter.framedInput C B c:=by
  have hnil : ZeroPadding.pad C []=List.replicate C false:=rfl
  have hflag:=TagPublish.pad_false C hC
  funext j
  fin_cases j <;>
    simp [nativeInput,NativeConverter.framedInput,AppendOutputFrame.input,AppendOutputLength.input,
      NativeConverter.input,NativeConverter.extra,CanonicalWalk.measuredInput,CanonicalWalk.input,
      Traversal.data,TagReady.data,TagReady.localData,TagReady.pads,TagReady.capacity,TagObserve.data,
      boundedCircuitFieldLimit,Fin.addCases,hnil,hflag]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Cold
