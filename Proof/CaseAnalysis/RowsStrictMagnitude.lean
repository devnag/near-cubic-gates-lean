import Proof.CaseAnalysis.WitnessNativeWord
import Proof.Hierarchy.HierarchyAllocation
import Proof.Circuits.CanonicalBinaryOutput
import Proof.PCP.PCPPairReusable

/-! The magnitude serializer needed by the strict-threshold request. Its
bit-length word is produced from the actual frame. Positive predecessor
outputs are trimmed in place and handed directly to this same serializer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsStrictMagnitude
open LocalBitMultitape RecoveryRootRound CloseoutWitness CanonicalPositiveOutput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lengthSlots : Fin 2 → Fin 7 := ![0,1]
theorem length_injective : Function.Injective lengthSlots := by decide
def input (bits : List Bool) : Fin 7 → List Bool := ![frame bits,[],[],[],[],[],[]]
noncomputable def lengthPhase := RecoveryFocus.machine lengthSlots ClockNumericPrep.ellMachine
noncomputable def machine := Composition.machine lengthPhase NativeWord.machine

theorem native_run (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (12*bits.length+28) (input bits) out ∧
      out 4=NativeWord.word bits := by
  have hl := (HierarchyAllocation.length_ready bits).focus lengthSlots length_injective
    (input bits) (by intro i;fin_cases i <;> rfl)
  have he : install lengthSlots (input bits)
      ![frame bits,false::List.replicate bits.length true]=NativeWord.input bits := by
    funext i
    fin_cases i
    · exact install_slot _ length_injective _ _ 0
    · exact install_slot _ length_injective _ _ 1
    all_goals exact install_other _ _ _ _ (by decide)
  rw [he] at hl
  obtain ⟨out,ho,h4⟩ := NativeWord.word_run bits
  have h := ClockJoin.join lengthPhase NativeWord.machine _ _ _ _ _ hl ho
  have ht : 4*bits.length+5+1+NativeWord.budget bits=12*bits.length+28 := by
    unfold NativeWord.budget
    omega
  rw [ht] at h
  exact ⟨out,h,h4⟩

def paddedInput (bits : List Bool) (z : ℕ) : Fin 7 → List Bool :=
  ![frame bits++List.replicate z false,[],[],[],[],[],[]]

theorem padded_native_run (bits : List Bool) (z : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (12*bits.length+28) (paddedInput bits z) out ∧
      out 4=NativeWord.word bits := by
  obtain ⟨out,ho,h4⟩ := native_run bits
  let caps : Fin 7 → ℕ := ![(frame bits).length+z,0,0,0,0,0,0]
  have hp := PCPPairReusable.padded_ready machine _ _ ho caps
  have hi : (fun i => ZeroPadding.pad (caps i) (input bits i))=paddedInput bits z := by
    funext i
    fin_cases i <;> simp [caps,input,paddedInput,ZeroPadding.pad]
  rw [hi] at hp
  exact ⟨_,hp,by change ZeroPadding.pad 0 (out 4)=_;simpa using h4⟩

def trimSlots : Fin 2 → Fin 8 := ![0,7]
def nativeSlots (i : Fin 7) : Fin 8 := i.castAdd 1
theorem trim_injective : Function.Injective trimSlots := by decide
theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)
def positiveInput (bits : List Bool) : Fin 8 → List Bool :=
  ![frame bits,[],[],[],[],[],[],[]]
noncomputable def trimPhase := RecoveryFocus.machine trimSlots trimProgram
noncomputable def nativePhase := RecoveryFocus.machine nativeSlots machine
noncomputable def positiveMachine := Composition.machine trimPhase nativePhase

theorem positive_native_run (w n : ℕ) (hn : 0<n) (hfit : n<2^w) : ∃ out,
    ClockJoin.ReadyRun positiveMachine (20*w+31) (positiveInput (SignedSortKey.binary w n)) out ∧
      out 4=RepairRepresentation.natWord n := by
  obtain ⟨pre,hpre⟩ := nat_bits_suffix n hn
  have hlen : pre.length+1=n.bits.length := by rw [hpre];simp
  have hwidth := nat_bits_length_le w n hfit
  let z := w-n.bits.length
  have hb : SignedSortKey.binary w n=pre++[true]++List.replicate z false := by
    rw [binary_padding w n hfit]
    exact congrArg (fun bits => bits++List.replicate z false) hpre
  have ht := (trim_ready pre z).focus trimSlots trim_injective
    (positiveInput (SignedSortKey.binary w n)) (by intro i;fin_cases i <;> simp only [positiveInput,trimSlots,hb] <;> rfl)
  let middle := install trimSlots (positiveInput (SignedSortKey.binary w n))
    ![RepairSource.ProjectionNormalization.DimensionTrim.backTape pre 0 z,
      List.replicate (trimCost pre z) false]
  obtain ⟨out,ho,h4⟩ := padded_native_run n.bits (2*z)
  have hi : ∀ i,middle (nativeSlots i)=paddedInput n.bits (2*z) i := by
    intro i
    fin_cases i
    · change install trimSlots _ _ (trimSlots 0)=_
      rw [install_slot _ trim_injective,back_tape,←hpre]
      rfl
    all_goals
      change install trimSlots _ _ _=[]
      rw [install_other _ _ _ _ (by decide)]
      rfl
  have hnative := ho.focus nativeSlots native_injective middle hi
  have hj := ClockJoin.join trimPhase nativePhase _ _ _ _ _ ht hnative
  have hbudget : 2*trimCost pre z+2+1+(12*n.bits.length+28)≤20*w+31 := by
    unfold trimCost
    dsimp only [z]
    omega
  refine ⟨_,ClockJoin.enlarge _ _ _ _ _ hj hbudget,?_⟩
  change install nativeSlots middle out (nativeSlots 4)=_
  rw [install_slot _ native_injective,h4,NativeWord.word_eq _ (CanonicalBinary.Nat.bits_canonical n),nat_bits_value]

end NearCubicWires.RepairOrdinary.CloseoutRowsStrictMagnitude
