import Proof.MachineModel.NativeTemplateReads

/-! Remaining coefficient/template ports complete the exact static payload. -/
namespace NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem read_false (z k : ℕ) : readTapeBit (List.replicate z false) k=false:=by
  simp [readTapeBit,List.getD]
private theorem read_empty (k : ℕ) : readTapeBit [] k=false:=rfl

theorem reads_coefficient {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w C : ℕ)
    (out : List Bool) (i : Fin 14) (pos : ℕ) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes ((i.natAdd 89).castAdd 10)) pos=
      readTapeBit (payload gs Q w ((i.natAdd 89).castAdd 10)) pos:=by
  change readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
    (NativeAllocation.capacity gs Q) Q w C [] out).tapes (((i.natAdd 89).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left,CloseoutRowsLoopLayout.inputTapes]
  simp only [ZeroPadding.read_pad,CloseoutRowsLoopLayout.rawInput,
    CloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input,payload,select,NativeFanout.word,
    NativeMaster.words,read_empty]

theorem reads_tail {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w C : ℕ)
    (out : List Bool) (i : Fin 10) (pos : ℕ)
    (h104 : (i.natAdd 103 : Fin 113)≠104) (h105 : (i.natAdd 103 : Fin 113)≠105)
    (h107 : (i.natAdd 103 : Fin 113)≠107) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes (i.natAdd 103)) pos=
      readTapeBit (payload gs Q w (i.natAdd 103)) pos:=by
  fin_cases i <;> try contradiction
  all_goals simp [entry_tapes,CloseoutRowsLoopLayout.inputTapes,CloseoutRowsLoopLayout.extra,
    CloseoutRowsLoopLayout.templates,Fin.addCases,ZeroPadding.read_pad,payload,select,
    NativeFanout.word,NativeMaster.words,read_false,read_empty]

theorem reads {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w C : ℕ)
    (out : List Bool) (i : Fin 113) (pos : ℕ)
    (h31 : i≠31) (h52 : i≠52) (h104 : i≠104) (h105 : i≠105) (h107 : i≠107) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes i) pos=
      readTapeBit (payload gs Q w i) pos:=by
  revert h31 h52 h104 h105 h107
  refine Fin.addCases (m:=103) (n:=10) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=89) (n:=14) (fun b=>?_) (fun b=>?_) a
    · refine Fin.addCases (m:=49) (n:=40) (fun c=>?_) (fun c=>?_) b
      · refine Fin.addCases (m:=48) (n:=1) (fun d=>?_) (fun d=>?_) c
        · intro h31 _ _ _ _;exact reads_core gs Q w C out d pos h31
        · intro _ _ _ _ _;fin_cases d
          change readTapeBit (ZeroPadding.pad C (ZeroPadding.pad C [])) pos=readTapeBit [] pos
          rw [ZeroPadding.read_pad,ZeroPadding.read_pad]
      · intro _ h52 _ _ _;exact reads_enum gs Q w C out c pos h52
    · intro _ _ _ _ _;exact reads_coefficient gs Q w C out b pos
  · intro _ _ h104 h105 h107;exact reads_tail gs Q w C out a pos h104 h105 h107

end NearCubicWires.ExtIncidence.NativeTemplate
