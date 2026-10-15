import Proof.MachineModel.ClosureRawRelabelFamily
import Proof.MachineModel.ClosureBinaryWriter

/-! Consumer-first layout for producing native source 262 before the fixed
cold writer. Raw-family output shares 262, its repeat driver shares 277;
all seven other work tapes and one paid reset log are beyond the 440 bank. -/
namespace NearCubicWires.P1Closure.BinaryPreparedWriter
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 10→Fin 448:=![440,441,442,443,262,444,445,446,277,447]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def prepare:=RecoveryFocus.machine slots
  (MaskedReset.machine RawRelabelFamily.machine (fun i=>decide (i=4)))
noncomputable def writer:=TapeEmbedding.machine 8 CompactColdFamily.machine
noncomputable def machine:=Composition.machine prepare writer

def privateData (N Y S j F : ℕ) (lower : List Bool) : Fin 8→List Bool:=
  let R:=RawRelabelUniform.capacity N Y
  let L:=RawRelabelUniform.logCapacity N Y S
  ![lower,List.replicate N true,false::List.replicate j true,List.replicate R false,
    List.replicate L false,List.replicate R true,List.replicate (R+1) false,List.replicate F false]
def heads (out : List Bool) : Fin 448→ℕ:=
  Fin.addCases (m:=440) (n:=8) (motive:=fun _=>ℕ) (CompactNativeInitialize.heads 0 out) (fun _=>0)

def frame (native : Fin 440→List Bool) (extra : Fin 8→List Bool) : Fin 448→List Bool:=
  Fin.addCases (m:=440) (n:=8) (motive:=fun _=>List Bool) native extra

variable {n : ℕ} (gs : List (ExactThresholdGate n)) [P1Radix gs] (Q w : ℕ)

def state (N Y S j F : ℕ) (source lower out : List Bool) : Fin 448→List Bool:=
  frame (CompactNativeInitialize.input gs Q w Y source out) (privateData N Y S j F lower)

theorem source_pin (Y : ℕ) (source out : List Bool) :
    CompactNativeInitialize.input gs Q w Y source out 262=source := by
  rw [CompactNativeInitialize.input,install_other _ _ _ 262 (by decide)]
  rfl

theorem driver_pin (Y : ℕ) (source out : List Bool) :
    CompactNativeInitialize.input gs Q w Y source out 277=CompareMachine.word Y := by
  rw [CompactNativeInitialize.input,install_other _ _ _ 277 (by decide)]
  rfl

theorem source_other (Y : ℕ) (source before out : List Bool) (i : Fin 440) (hi : i≠262) :
    CompactNativeInitialize.input gs Q w Y source out i=
      CompactNativeInitialize.input gs Q w Y before out i := by
  unfold CompactNativeInitialize.input install
  cases hp:RecoveryFocus.pick CompactNativeInitialize.metadataSlots i with
  | some j=>rfl
  | none=>simp [CompactNativeInitialize.base,hi]

theorem input_slots (N Y S F : ℕ) (P : List (List ℕ)) (tail out : List Bool) (j : Fin 10) :
    state gs Q w N Y S 0 F [] (stream P++tail) out (slots j)=
      Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
        (RawRelabelFamily.familyData N Y S 0 P tail []) (fun _=>List.replicate F false) j := by
  fin_cases j <;> first
    | exact source_pin gs Q w Y [] out
    | exact driver_pin gs Q w Y [] out
    | rfl

theorem head_slots (out : List Bool) (j : Fin 10) :
    heads out (slots j)=Fin.addCases (m:=9) (n:=1) (motive:=fun _=>ℕ)
      (RawRelabelFamily.familyHeads []) (fun _=>0) j := by fin_cases j <;> rfl

theorem exit_heads (out raw : List Bool) :
    dockH slots (heads out)
      (Fin.addCases (m:=9) (n:=1) (motive:=fun _=>ℕ)
        (fun i=>if decide (i=4) then 0 else RawRelabelFamily.familyHeads raw i) (fun _=>0))=heads out := by
  exact dockH_existing _ _ _ (by intro j;fin_cases j <;> rfl)

theorem exit_tapes (N Y S F : ℕ) (P : List (List ℕ)) (tail out raw : List Bool) :
    install slots (state gs Q w N Y S 0 F [] (stream P++tail) out)
      (Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
        (RawRelabelFamily.familyData N Y S Y P tail raw) (fun _=>List.replicate F false))=
      state gs Q w N Y S Y F raw (stream P++tail) out := by
  apply HierarchyAllocation.install_eq slots slots_injective
  · intro j
    fin_cases j <;> first
      | exact source_pin gs Q w Y raw out
      | exact driver_pin gs Q w Y raw out
      | rfl
  · intro i
    refine Fin.addCases (m:=440) (n:=8) (fun j=>?_) (fun j=>?_) i
    · intro hi
      have hj:j≠262:=by intro e;subst j;exact hi 4 rfl
      simpa only [state,frame,Fin.addCases_left] using source_other gs Q w Y raw [] out j hj
    · intro hi
      fin_cases j <;> first
        | rfl
        | exact False.elim (hi 2 rfl)

end
end NearCubicWires.P1Closure.BinaryPreparedWriter
