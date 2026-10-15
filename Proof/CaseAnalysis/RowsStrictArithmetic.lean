import Proof.CaseAnalysis.RowsStrictMagnitude
import Proof.Amplification.RecoveryPrefixCounter
import Proof.Amplification.RecoveryListPredecessor

/-! The two unbounded branches of threshold-minus-one use only binary
arithmetic. Both start with the actual canonical magnitude frame and return
the exact native magnitude with every head reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsStrictArithmetic
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def incrementSlots : Fin 2 → Fin 10 := ![0,9]
def predecessorSlots : Fin 3 → Fin 10 := ![0,8,9]
def nativeSlots (i : Fin 7) : Fin 10 := i.castAdd 3
def positiveSlots (i : Fin 8) : Fin 10 := i.castAdd 2
theorem increment_injective : Function.Injective incrementSlots := by decide
theorem predecessor_injective : Function.Injective predecessorSlots := by decide
theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)
theorem positive_injective : Function.Injective positiveSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)
def input (bits : List Bool) : Fin 10 → List Bool :=
  ![frame bits,[],[],[],[],[],[],[],[false],[]]
noncomputable def increment := RecoveryFocus.machine incrementSlots ClockIncrement.machine
noncomputable def predecessor := RecoveryFocus.machine predecessorSlots RecoveryListPredecessor.machine
noncomputable def native := RecoveryFocus.machine nativeSlots CloseoutRowsStrictMagnitude.machine
noncomputable def positive := RecoveryFocus.machine positiveSlots CloseoutRowsStrictMagnitude.positiveMachine
noncomputable def negativeMachine := Composition.machine increment native
noncomputable def positiveMachine := Composition.machine predecessor positive

theorem increment_ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun ClockIncrement.machine (4*bits.length+8) ![frame bits,[]] out ∧
      out 0=frame (ClockIncrement.next bits) := by
  obtain ⟨r,hr,h0,_,hh,hs,_⟩ := ClockIncrement.increment_run bits 0
  have h : ClockJoin.ReadyRun ClockIncrement.machine (2*ClockIncrement.work bits+2)
      ![frame bits,[]] r.final.tapes := by
    refine ⟨r,?_,rfl,hh,hs.le⟩
    convert hr using 2
    funext i
    fin_cases i <;> rfl
  exact ⟨_,ClockJoin.enlarge _ _ _ _ _ h (by have := ClockIncrement.work_bound bits;omega),h0⟩

theorem negative_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun negativeMachine (16*n.bits.length+49) (input n.bits) out ∧
      out 4=RepairRepresentation.natWord (n+1) := by
  obtain ⟨inc,hi,h0⟩ := increment_ready n.bits
  have hinc := hi.focus incrementSlots increment_injective (input n.bits)
    (by intro i;fin_cases i <;> rfl)
  let middle := install incrementSlots (input n.bits) inc
  obtain ⟨out,ho,h4⟩ := CloseoutRowsStrictMagnitude.native_run (n+1).bits
  have hm : ∀ i,middle (nativeSlots i)=CloseoutRowsStrictMagnitude.input (n+1).bits i := by
    intro i
    fin_cases i
    · change install incrementSlots _ inc (incrementSlots 0)=_
      rw [install_slot _ increment_injective,h0,RecoveryPrefixCounter.next_bits]
      rfl
    all_goals
      change install incrementSlots _ inc _=[]
      rw [install_other _ _ _ _ (by decide)]
      rfl
  have hn := ho.focus nativeSlots native_injective middle hm
  have hj := ClockJoin.join increment native _ _ _ _ _ hinc hn
  have hlen : (n+1).bits.length≤n.bits.length+1 := by
    rw [←RecoveryPrefixCounter.next_bits]
    exact (ClockIncrement.next_length n.bits).2
  refine ⟨_,ClockJoin.enlarge _ _ _ _ _ hj (by omega),?_⟩
  change install nativeSlots middle out (nativeSlots 4)=_
  rw [install_slot _ native_injective,h4,NativeWord.word_eq _ (CanonicalBinary.Nat.bits_canonical (n+1)),
    CanonicalPositiveOutput.nat_bits_value]

theorem positive_run (n : ℕ) (hn : 2≤n) : ∃ out,
    ClockJoin.ReadyRun positiveMachine (24*n.bits.length+36) (input n.bits) out ∧
      out 4=RepairRepresentation.natWord (n-1) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := RecoveryListPredecessor.predecessor_ready n.bits false 0
  have hp : ClockJoin.ReadyRun RecoveryListPredecessor.machine (4*n.bits.length+4)
      ![frame n.bits,[false],List.replicate 0 false]
      ![frame (RecoveryListPredecessor.result n.bits true),
        [decide (value n.bits≠0)],List.replicate (max 0 (2*n.bits.length+1)) false] :=
    ⟨r,hr,rt,rh,rs.le⟩
  have hpred := hp.focus predecessorSlots predecessor_injective (input n.bits)
    (by intro i;fin_cases i <;> rfl)
  let middle := install predecessorSlots (input n.bits)
    ![frame (RecoveryListPredecessor.result n.bits true),
      [decide (value n.bits≠0)],List.replicate (max 0 (2*n.bits.length+1)) false]
  have hv : value (RecoveryListPredecessor.result n.bits true)=n-1 := by
    rw [RecoveryListPredecessor.predecessor_value _ (by rw [CanonicalPositiveOutput.nat_bits_value];omega),
      CanonicalPositiveOutput.nat_bits_value]
  have he : RecoveryListPredecessor.result n.bits true=SignedSortKey.binary n.bits.length (n-1) := by
    have h := BoundedCounter.binary_of_value (RecoveryListPredecessor.result n.bits true)
    rw [RecoveryListPredecessor.result_length,hv] at h
    exact h.symm
  have hfit : n-1<2^n.bits.length := by
    have h := value_lt n.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at h
    omega
  obtain ⟨out,ho,h4⟩ := CloseoutRowsStrictMagnitude.positive_native_run n.bits.length (n-1) (by omega) hfit
  have hm : ∀ i,middle (positiveSlots i)=CloseoutRowsStrictMagnitude.positiveInput
      (SignedSortKey.binary n.bits.length (n-1)) i := by
    intro i
    fin_cases i
    · change install predecessorSlots _ _ (predecessorSlots 0)=_
      rw [install_slot _ predecessor_injective,he]
      rfl
    all_goals
      change install predecessorSlots _ _ _=[]
      rw [install_other _ _ _ _ (by decide)]
      rfl
  have hn := ho.focus positiveSlots positive_injective middle hm
  have hj := ClockJoin.join predecessor positive _ _ _ _ _ hpred hn
  have ht : 4*n.bits.length+4+1+(20*n.bits.length+31)=24*n.bits.length+36 := by omega
  rw [ht] at hj
  exact ⟨_,hj,(install_slot _ positive_injective _ _ 4).trans h4⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsStrictArithmetic
