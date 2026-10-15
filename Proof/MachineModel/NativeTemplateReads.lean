import Proof.MachineModel.NativeTemplate

/-! Native input correspondence is proved through small tape projections;
no concrete ordinary controller is expanded by the field simplifier. -/
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

theorem reads_core {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w C : ℕ)
    (out : List Bool) (i : Fin 48) (pos : ℕ) (h31 : (i.castAdd 65 : Fin 113)≠31) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes (i.castAdd 65)) pos=
      readTapeBit (payload gs Q w (i.castAdd 65)) pos:=by
  rw [core_read]
  fin_cases i <;> try contradiction
  all_goals simp [RowTupleCursorLayout.data,RowCommonReusable.data,Fin.addCases,
    payload,select,NativeFanout.word,NativeMaster.words,RowOccurrenceLoop.word,
    UnaryTemplate.tape,CompareMachine.word,read_false,read_empty]
  all_goals first | exact read_false 2 pos | exact read_false 1 pos

theorem enum_read {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (out : List Bool) (i : Fin 40) (pos : ℕ) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
      ((i.natAdd 49).castAdd 24)) pos=
      readTapeBit (RowTupleEnumeratedEquations.extra w 1 0 i) pos:=by
  change readTapeBit ((CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
    ((((i.natAdd 49).castAdd 14).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left,CloseoutRowsLoopLayout.inputTapes]
  simp only [Fin.addCases_left,ZeroPadding.read_pad,CloseoutRowsLoopLayout.rawInput,
    CloseoutRowsComputedCuts.input,Fin.addCases_left]
  have hn : (i.natAdd 49 : Fin 89)≠48:=by
    intro h;have hv:=congrArg (fun x : Fin 89=>x.val) h
    simp only [Fin.val_natAdd] at hv;omega
  rw [Function.update_of_ne hn]
  simp only [CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,
    TapeEmbedding.config,Fin.addCases_right]
  rfl

theorem reads_enum {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w C : ℕ)
    (out : List Bool) (i : Fin 40) (pos : ℕ) (h52 : ((i.natAdd 49).castAdd 24 : Fin 113)≠52) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w C [] out).tapes ((i.natAdd 49).castAdd 24)) pos=
      readTapeBit (payload gs Q w ((i.natAdd 49).castAdd 24)) pos:=by
  rw [enum_read]
  fin_cases i <;> try contradiction
  all_goals simp [RowTupleEnumeratedEquations.extra,payload,select,NativeFanout.word,
    NativeMaster.words,read_empty]

end NearCubicWires.ExtIncidence.NativeTemplate
