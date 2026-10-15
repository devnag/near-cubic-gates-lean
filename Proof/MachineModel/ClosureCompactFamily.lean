import Proof.MachineModel.ClosureCompactNativeInitialize

/-! One fixed ordinary program computes the compact metadata, initializes
the bank, then emits the full raw-index family. The source cache, runtime
dimension words, raw family and its loop count remain explicit inputs.
No retained metadata premise survives this composition. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactColdFamily
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtIncidence ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def loopSlots (i : Fin 278) : Fin 440 := i.castAdd 162
theorem loopSlots_injective : Function.Injective loopSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 440 => k.val) h)
noncomputable def last := RecoveryFocus.machine loopSlots P1CompactNativeFamily.machine
noncomputable def machine := Composition.machine CompactNativeInitialize.machine last

variable {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs] (Q w : Nat)
  (ps : List (List (List (Fin gs.length)))) (out pre tail : List Bool)

def source := pre++ps.flatMap P1CompactNativeFamily.rawWord++tail
noncomputable def ambient := CompactNativeInitialize.output gs Q w ps.length (source gs ps pre tail) out
def ambientH := CompactNativeInitialize.heads pre.length out
noncomputable def H : Fin 277 → Nat := ambientH out pre ∘ CompactNativeInitialize.native
noncomputable def A : Fin 277 → List Bool := ambient gs Q w ps out pre tail ∘ CompactNativeInitialize.native
def budget := CompactNativeInitialize.budget gs Q w+1+P1CompactNativeFamily.budget gs Q w ps
noncomputable def finalConfig := RepeatMachine.cfg 3
  (P1CompactNativeFamily.entry gs Q w ps pre tail (H out pre) (A gs Q w ps out pre tail) ps.length
    (out++ps.flatMap (P1CompactNativeFamily.emit gs Q w))) ps.length 1
noncomputable def finalHeads := dockH loopSlots (ambientH out pre) (finalConfig gs Q w ps out pre tail).heads
noncomputable def finalTapes := install loopSlots (ambient gs Q w ps out pre tail)
  (finalConfig gs Q w ps out pre tail).tapes

theorem family_run (hmask : ∀ ms∈ps,P1MaskDegree gs (rawRows ms))
    (hw : ∀ ms∈ps,ms.length<2^w) (hQ : 1≤Q) :
    Step machine (budget gs Q w ps) (ambientH out pre)
      (CompactNativeInitialize.input gs Q w ps.length (source gs ps pre tail) out)
      (finalHeads gs Q w ps out pre tail) (finalTapes gs Q w ps out pre tail) := by
  have first := CompactNativeInitialize.run gs Q w ps.length pre.length (source gs ps pre tail) out
  have fields := CompactNativeInitialize.initialized gs Q w ps.length pre.length (source gs ps pre tail) out
  have master := CompactNativeInitialize.masters gs Q w ps.length pre.length (source gs ps pre tail) out
  obtain ⟨actual,run,final,_steps⟩ := P1CompactNativeFamily.family_run gs Q w ps hmask out pre tail hw hQ
    (H out pre) (A gs Q w ps out pre tail) (fun j=>(master j).1) (fun j=>(master j).2)
  have hh : P1CompactNativeState.heads (H out pre) pre.length out=H out pre :=
    dockH_existing NativeFanoutLayout.bank (H out pre) _ (fun i=>(fields i).1)
  have ht : P1CompactNativeState.tapes (A gs Q w ps out pre tail)
      (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
      (source gs ps pre tail) out=A gs Q w ps out pre tail :=
    install_existing NativeFanoutLayout.bank (A gs Q w ps out pre tail) _ (fun i=>(fields i).2)
  have hi : ∀ i,ambientH out pre (loopSlots i)=
      (RepeatMachine.cfg 0 (P1CompactNativeFamily.entry gs Q w ps pre tail
        (H out pre) (A gs Q w ps out pre tail) 0 out) ps.length 1).heads i := by
    intro i
    refine Fin.addCases (m:=277) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
      change H out pre j = P1CompactNativeState.heads (H out pre)
        (pre.length+((ps.take 0).flatMap P1CompactNativeFamily.rawWord).length) out j
      simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.add_zero,hh]
    · have hj : j=0 := Fin.eq_zero j
      subst j
      rfl
  have ti : ∀ i,ambient gs Q w ps out pre tail (loopSlots i)=
      (RepeatMachine.cfg 0 (P1CompactNativeFamily.entry gs Q w ps pre tail
        (H out pre) (A gs Q w ps out pre tail) 0 out) ps.length 1).tapes i := by
    intro i
    refine Fin.addCases (m:=277) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
      change A gs Q w ps out pre tail j = P1CompactNativeState.tapes (A gs Q w ps out pre tail)
        (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
        (source gs ps pre tail) out j
      rw [ht]
    · have hj : j=0 := Fin.eq_zero j
      subst j
      exact CompactNativeInitialize.output_other gs Q w ps.length (source gs ps pre tail) out 277
        (by decide) (by decide)
  have call := (Step.of_run run (congrArg Configuration.heads final) (congrArg Configuration.tapes final)).focus
    loopSlots loopSlots_injective (ambientH out pre) (ambient gs Q w ps out pre tail)
  have call := call.congr_in (dockH_existing loopSlots _ _ hi) (install_existing loopSlots _ _ ti)
  exact first.seq call

theorem output_word : finalTapes gs Q w ps out pre tail 180 =
    out++ps.flatMap (P1CompactNativeFamily.emit gs Q w) := by
  have h := install_slot loopSlots loopSlots_injective (ambient gs Q w ps out pre tail)
    (finalConfig gs Q w ps out pre tail).tapes 180
  change finalTapes gs Q w ps out pre tail 180 = _ at h
  rw [h]
  change P1CompactNativeState.tapes (A gs Q w ps out pre tail)
    (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
    (source gs ps pre tail) (out++ps.flatMap (P1CompactNativeFamily.emit gs Q w))
    (NativeFanoutLayout.bank 31) = _
  rw [P1CompactNativeState.tapes,install_slot NativeFanoutLayout.bank NativeFanoutLayout.bank_injective]
  rfl

end NearCubicWires.P1Closure.CompactColdFamily
