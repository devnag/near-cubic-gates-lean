import Proof.CaseAnalysis.RowsGateFieldsLayout

/-! One cold run decodes the same supported gate's three retained fields.
The only initial data is its raw framed code. All allocation and traversal
costs belong to this run; native weights and support stay at their ports. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics CloseoutWitness
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 998 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=0 then some false else none,fun _=>.stay⟩ else none
noncomputable def header:=RecoveryFocus.machine headerSlots CloseoutRowsGateHeader.machine
noncomputable def weights:=RecoveryFocus.machine weightsSlots CloseoutRowsIntegerCold.readyMachine
noncomputable def threshold:=RecoveryFocus.machine thresholdSlots CloseoutRowsIntegerGuard.machine
noncomputable def support:=RecoveryFocus.machine supportSlots CloseoutRowsBooleanVector.machine
noncomputable def first:=Composition.machine boot header
noncomputable def second:=Composition.machine first weights
noncomputable def third:=Composition.machine second threshold
noncomputable def machine:=Composition.machine third support
def budget (bits : List Bool):=1+1+CloseoutRowsGateHeader.budget bits+1+
  CloseoutRowsIntegerCold.readyBudget (CloseoutRowsGateHeader.codeWord bits 0)+1+
  CloseoutRowsIntegerGuard.budget (CloseoutRowsGateHeader.codeWord bits 1)+1+
  NatCold.budget (CloseoutRowsGateHeader.codeWord bits 2)
noncomputable def result (bits : List Bool) (w : Fin 460→List Bool)
    (th : Fin 212→List Bool) (sup : Fin 178→List Bool):=
  install supportSlots (thresholdDone bits w th) sup

theorem boot_run (bits : List Bool) : ClockJoin.ReadyRun boot 1 (input bits) (booted bits):=by
  let final : Configuration 998 2:=⟨1,fun _=>0,booted bits⟩
  have hs:step boot (initialConfiguration boot (input bits))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=0
      · subst i
        simp [applyAction,initialConfiguration,boot,final,booted,input,writeTapeBit]
      · simp [applyAction,initialConfiguration,boot,final,booted,hi]
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem result_weights (bits : List Bool) (w : Fin 460→List Bool)
    (th : Fin 212→List Bool) (sup : Fin 178→List Bool) (i : Fin 460) :
    result bits w th sup (weightsSlots i)=w i:=by
  rw [result,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [support_val,weights_val] at hv
    split_ifs at hv <;> omega)]
  rw [thresholdDone,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [threshold_val,weights_val] at hv
    split_ifs at hv <;> omega)]
  exact install_slot _ weights_injective _ _ _
theorem result_threshold (bits : List Bool) (w : Fin 460→List Bool)
    (th : Fin 212→List Bool) (sup : Fin 178→List Bool) (i : Fin 212) :
    result bits w th sup (thresholdSlots i)=th i:=by
  rw [result,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [support_val,threshold_val] at hv
    split_ifs at hv <;> omega)]
  exact install_slot _ threshold_injective _ _ _
theorem result_support (bits : List Bool) (w : Fin 460→List Bool)
    (th : Fin 212→List Bool) (sup : Fin 178→List Bool) (i : Fin 178) :
    result bits w th sup (supportSlots i)=sup i:=install_slot _ support_injective _ _ _
theorem result_header (bits : List Bool) (w : Fin 460→List Bool)
    (th : Fin 212→List Bool) (sup : Fin 178→List Bool) :
    result bits w th sup 147=CloseoutRowsGateHeader.output bits 147:=by
  rw [result,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;rw [support_val] at hv;split_ifs at hv <;> omega)]
  rw [thresholdDone,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;rw [threshold_val] at hv;split_ifs at hv <;> omega)]
  change weightsDone bits w (headerSlots 147)=_
  rw [weights_header bits w 147 (by decide)]
  exact install_slot _ header_injective _ _ _

theorem fields_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      (readTapeBit (output 147) 0=true ↔ CompetitorWitnessTriple.structural bits) ∧
      (readTapeBit (output 367) 0=true ↔
        (CanonicalBinary.decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))).isSome) ∧
      (readTapeBit (output 819) 0=true ↔
        (CanonicalBinary.decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))).isSome) ∧
      (readTapeBit (output 996) 0=true ↔
        (CanonicalBinary.decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))).isSome) ∧
      output 625=frame (RecoveryFixedUnpair.leftWord (CloseoutRowsGateHeader.codeWord bits 1)) ∧
      output 802=frame (CloseoutRowsIntegerGuard.payload (CloseoutRowsGateHeader.codeWord bits 1)) ∧
      output 808=NativeWord.word (CloseoutRowsIntegerGuard.payload (CloseoutRowsGateHeader.codeWord bits 1)) ∧
      output 994=frame (BitFields.payload (CloseoutRowsGateHeader.codeWord bits 2)) ∧
      output 861=CompareMachine.word (BitFields.payload (CloseoutRowsGateHeader.codeWord bits 2)).length ∧
      (∀ values,CanonicalBinary.decodeIntList (value (CloseoutRowsGateHeader.codeWord bits 0))=some values →
        output 361=values.flatMap RepairRepresentation.intWord ∧
          output 368=CompareMachine.word values.length) ∧
      (∀ z,CanonicalBinary.decodeInt (value (CloseoutRowsGateHeader.codeWord bits 1))=some z →
        output 808=RepairRepresentation.natWord z.natAbs) ∧
      (∀ values,CanonicalBinary.decodeBoolList (value (CloseoutRowsGateHeader.codeWord bits 2))=some values →
        output 994=frame values):=by
  have hh:=(CloseoutRowsGateHeader.header_run bits).1.focus headerSlots header_injective
    (booted bits) (header_input bits)
  have h0:=ClockJoin.join boot header _ _ _ _ _ (boot_run bits) hh
  obtain ⟨w,hw,_,_,wf,wt⟩:=CloseoutRowsIntegerCold.ready_run (CloseoutRowsGateHeader.codeWord bits 0)
  have hw':=hw.focus weightsSlots weights_injective (headerDone bits) (weights_input bits)
  have h1:=ClockJoin.join first weights _ _ _ _ _ h0 hw'
  obtain ⟨th,ht,tf,ts,tp,tn,tt⟩:=CloseoutRowsIntegerGuard.guard_run (CloseoutRowsGateHeader.codeWord bits 1)
  have ht':=ht.focus thresholdSlots threshold_injective (weightsDone bits w) (threshold_input bits w)
  have h2:=ClockJoin.join second threshold _ _ _ _ _ h1 ht'
  obtain ⟨sup,hs,sp,sc,sf,st⟩:=CloseoutRowsBooleanVector.vector_run (CloseoutRowsGateHeader.codeWord bits 2)
  have hs':=hs.focus supportSlots support_injective (thresholdDone bits w th) (support_input bits w th)
  have h:=ClockJoin.join third support _ _ _ _ _ h2 hs'
  refine ⟨result bits w th sup,h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [result_header]
    exact (CloseoutRowsGateHeader.header_run bits).2.1
  · change readTapeBit (result bits w th sup (weightsSlots 219)) 0=true ↔_
    rw [result_weights]
    exact wf
  · change readTapeBit (result bits w th sup (thresholdSlots 211)) 0=true ↔_
    rw [result_threshold]
    exact tf
  · change readTapeBit (result bits w th sup (supportSlots 176)) 0=true ↔_
    rw [result_support]
    exact sf
  · exact (result_threshold bits w th sup 17).trans ts
  · exact (result_threshold bits w th sup 194).trans tp
  · exact (result_threshold bits w th sup 200).trans tn
  · exact (result_support bits w th sup 174).trans sp
  · exact (result_support bits w th sup 41).trans sc
  · intro values hv
    exact ⟨(result_weights bits w th sup 213).trans (wt values hv).1,
      (result_weights bits w th sup 220).trans (wt values hv).2⟩
  · intro z hz
    exact (result_threshold bits w th sup 200).trans (tt z hz)
  · intro values hv
    exact (result_support bits w th sup 174).trans (st values hv)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
