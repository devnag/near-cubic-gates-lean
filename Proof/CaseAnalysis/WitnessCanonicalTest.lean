import Proof.CaseAnalysis.WitnessCanonicalLayout

/-! One cold ordinary canonical-list test. It copies the actual raw input,
executes traversal and serialization, and compares numeric values exactly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CanonicalTest
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def start := Composition.machine copy boot
noncomputable def prefixMachine := Composition.machine start walk
noncomputable def machine := Composition.machine prefixMachine equality
def tail (bits : List Bool) := List.replicate
  (Reencode.backing bits-(frame (Reencode.canonical bits).bits).length) false
def compareInput (bits : List Bool) : Fin 4→List Bool :=
  ![frame bits,ZeroPadding.pad (Reencode.backing bits) (frame (Reencode.canonical bits).bits),[true],[]]
def compareOutput (bits : List Bool) : Fin 4→List Bool :=
  ![frame bits,ZeroPadding.pad (Reencode.backing bits) (frame (Reencode.canonical bits).bits),
    [decide (value bits=value (Reencode.canonical bits).bits)],
    List.replicate (2*max bits.length (Reencode.canonical bits).bits.length+1) false]
def comparisonTime (bits : List Bool) := 4*max bits.length (Reencode.canonical bits).bits.length+4
def time (bits : List Bool) := (8*bits.length+14+1+1)+1+Reencode.readyBudget bits+1+comparisonTime bits
def budget (bits : List Bool) := 16*Reencode.polynomialBudget bits

theorem comparison_input (bits : List Bool) (out : Fin (36+1+3+128+1)→List Bool)
    (hout : out 117=ZeroPadding.pad (Reencode.backing bits) (frame (Reencode.canonical bits).bits))
    (i : Fin 4) : walked bits out (equalSlots i)=compareInput bits i := by
  fin_cases i
  · change walked bits out 0=frame bits
    rw [walked_other bits out 0 (Or.inl rfl),
      primed_other bits 0 (by decide)]
    exact copied_at bits 0
  · change install walkSlots (primed bits) out (walkSlots 117)=_
    rw [install_slot _ walk_injective]
    exact hout
  · change walked bits out 172=[true]
    rw [walked_other bits out 172 (Or.inr (by decide))]
    simp [primed]
  · change walked bits out 173=[]
    rw [walked_other bits out 173 (Or.inr (by decide)),
      primed_other bits 173 (by decide),copied_other bits 173 (by decide)]

theorem comparison_ready (bits : List Bool) :
    ClockJoin.ReadyRun NumericEquality.readyMachine (comparisonTime bits) (compareInput bits) (compareOutput bits) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=NumericEquality.equality_ready bits (Reencode.canonical bits).bits [] (tail bits) true 0
  simp only [List.append_nil,Bool.true_and,Nat.zero_max] at hr ht
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have hw:bits.length≤Reencode.polynomialBudget bits:=by
    have hp:bits.length+1≤(bits.length+1)^24:=Nat.le_self_pow (by decide) _
    unfold Reencode.polynomialBudget
    omega
  have hc:=canonical_bits bits
  have hm:max bits.length (Reencode.canonical bits).bits.length≤Reencode.polynomialBudget bits:=max_le hw hc
  have hp:12≤Reencode.polynomialBudget bits:=by
    have hpos:1≤(bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
    unfold Reencode.polynomialBudget
    omega
  unfold time budget comparisonTime Reencode.readyBudget
  omega

theorem canonical_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 0=frame bits ∧
      (readTapeBit (output 172) 0=true ↔
        ∃ values,CanonicalBinary.encodeBalancedList values=value bits) := by
  obtain ⟨out,ho,hframe,_⟩:=Reencode.reencode_ready bits
  have hs:=ClockJoin.join copy boot _ _ _ _ _ (copy_ready bits) (boot_ready bits)
  have hw:=bounded_focus walkSlots walk_injective _ _ _ ho (primed bits) (walk_input bits)
  have hp:=ClockJoin.join start walk _ _ _ _ _ hs hw
  have he:=bounded_focus equalSlots equal_injective _ _ _ (comparison_ready bits)
    (walked bits out) (comparison_input bits out hframe)
  have h:=ClockJoin.join prefixMachine equality _ _ _ _ _ hp he
  have more:=ClockJoin.enlarge machine (time bits) (budget bits) _ _ h (time_bound bits)
  refine ⟨install equalSlots (walked bits out) (compareOutput bits),more,?_,?_⟩
  · change install equalSlots (walked bits out) (compareOutput bits) (equalSlots 0)=_
    rw [install_slot _ equal_injective]
    rfl
  · change readTapeBit (install equalSlots (walked bits out) (compareOutput bits) (equalSlots 2)) 0=true ↔_
    rw [install_slot _ equal_injective]
    change decide (value bits=value (Reencode.canonical bits).bits)=true ↔_
    rw [decide_eq_true_eq,RecoveryUnpair.bits_value]
    exact eq_comm.trans (PCPPNativeCanonicalTree.tree_canonical_iff (value bits))

end NearCubicWires.RepairOrdinary.CloseoutWitness.CanonicalTest
