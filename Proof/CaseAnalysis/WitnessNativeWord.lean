import Proof.CaseAnalysis.WitnessNativeWordHeader

/-! Convert a decoded framed binary value and its retained bit-count word
to the exact source natWord with one shared copy and serializer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeWord
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3→Fin 7:=![1,2,3]
def headerSlots : Fin 4→Fin 7:=![0,2,4,5]
def zeroSlots : Fin 3→Fin 7:=![2,4,6]
theorem copy_injective : Function.Injective copySlots:=by decide
theorem header_injective : Function.Injective headerSlots:=by decide
theorem zero_injective : Function.Injective zeroSlots:=by decide
def input (bits : List Bool) : Fin 7→List Bool:=
  ![frame bits,RepairSource.VerifierDecoding.CompareMachine.word bits.length,[],[],[],[],[]]
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def header:=RecoveryFocus.machine headerSlots MatrixNaturalHeader.resetMachine
noncomputable def patch:=RecoveryFocus.machine zeroSlots Zero.readyMachine
noncomputable def copied (bits : List Bool):=install copySlots (input bits) (UWalkUnary.result false false 0 bits.length)

theorem copy_input (bits : List Bool) : ∀ i,input bits (copySlots i)=UWalkUnary.input 0 bits.length i:=by
  intro i
  fin_cases i <;> simp [input,copySlots,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero]

theorem header_input (bits : List Bool) : ∀ i,copied bits (headerSlots i)=MatrixNaturalHeader.resetInput bits i:=by
  intro i
  fin_cases i
  · change install copySlots (input bits) _ 0=frame bits
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install copySlots (input bits) _ (copySlots 1)=List.replicate bits.length true
    rw [install_slot _ copy_injective]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
  · change install copySlots (input bits) _ 4=[]
    rw [install_other _ _ _ _ (by decide)]
    rfl
  · change install copySlots (input bits) _ 5=[]
    rw [install_other _ _ _ _ (by decide)]
    rfl

theorem zero_input (bits : List Bool) (out : Fin 4→List Bool)
    (hwidth : out 1=List.replicate bits.length true) (hword : out 2=rawWord bits) :
    ∀ i,install headerSlots (copied bits) out (zeroSlots i)=Zero.readyInput bits i:=by
  intro i
  fin_cases i
  · change install headerSlots (copied bits) out (headerSlots 1)=List.replicate bits.length true
    rw [install_slot _ header_injective,hwidth]
  · change install headerSlots (copied bits) out (headerSlots 2)=rawWord bits
    rw [install_slot _ header_injective,hword]
  · change install headerSlots (copied bits) out 6=[]
    rw [install_other _ _ _ _ (by decide)]
    change install copySlots (input bits) _ 6=[]
    rw [install_other _ _ _ _ (by decide)]
    rfl

noncomputable def prefixMachine:=Composition.machine copy header
noncomputable def machine:=Composition.machine prefixMachine patch
def budget (bits : List Bool):=8*bits.length+22

theorem word_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧ output 4=word bits:=by
  have hc:=bounded_focus copySlots copy_injective _ _ _ (UWalkUnary.ready false false 0 bits.length)
    (input bits) (copy_input bits)
  obtain ⟨out,ho,_,hwidth,hword⟩:=header_ready bits
  have hh:=bounded_focus headerSlots header_injective _ _ _ ho (copied bits) (header_input bits)
  have hp:=ClockJoin.join copy header _ _ _ _ _ hc hh
  obtain ⟨last,hl,hresult⟩:=Zero.ready bits
  have hz:=bounded_focus zeroSlots zero_injective _ _ _ hl (install headerSlots (copied bits) out)
    (zero_input bits out hwidth hword)
  have h:=ClockJoin.join prefixMachine patch _ _ _ _ _ hp hz
  have htime:((2*bits.length+6)+1+(6*bits.length+6))+1+8=budget bits:=by unfold budget;omega
  rw [htime] at h
  refine ⟨_,h,?_⟩
  change install zeroSlots (install headerSlots (copied bits) out) last (zeroSlots 1)=_
  rw [install_slot _ zero_injective,hresult]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeWord
