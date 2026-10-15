import Proof.Circuits.DecompositionSignFrame

/-! Actual signed-atom pairing from the retained sign bit and the magnitude
serializer's framed code. The operand copy and all local rewinds are paid;
the same canonical pair program supplies the fresh framed result. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSignedPair
open LocalBitMultitape RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signSlots : Fin 2 → Fin 41 := ![0,4]
def copySlots : Fin 3 → Fin 41 := ![1,5,40]
def pairSlots (j : Fin 38) : Fin 41 := ⟨j.val+2,by omega⟩
theorem sign_injective : Function.Injective signSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [pairSlots] at hv
  omega
noncomputable def signProgram := RecoveryFocus.machine signSlots DecompositionSignFrame.machine
noncomputable def copyProgram := RecoveryFocus.machine copySlots PCPFieldMoves.readyMachine
noncomputable def pairProgram := RecoveryFocus.machine pairSlots PCPPairCanonical.machine
noncomputable def first := Composition.machine signProgram copyProgram
noncomputable def machine := Composition.machine first pairProgram
def input (b : Bool) (bits suffix : List Bool) (i : Fin 41) : List Bool :=
  if i=0 then [b] else if i=1 then frame bits++suffix else []
noncomputable def printed (b : Bool) (bits suffix : List Bool) :=
  install signSlots (input b bits suffix) ![[b],frame [b]]
noncomputable def loaded (b : Bool) (bits suffix : List Bool) :=
  install copySlots (printed b bits suffix) (PCPFieldMoves.output [] bits suffix 0 0)
def budget (b : Bool) (bits : List Bool) := PCPPairCanonical.budget [b] bits+4*bits.length+10

theorem copy_input (b : Bool) (bits suffix : List Bool) (j : Fin 3) :
    printed b bits suffix (copySlots j)=
      (![frame bits++suffix,List.replicate 0 false,List.replicate 0 false] : Fin 3 → List Bool) j := by
  rw [printed,install_other signSlots _ _ (copySlots j) (by fin_cases j <;> decide)]
  fin_cases j <;> rfl

theorem pair_input (b : Bool) (bits suffix : List Bool) (j : Fin 38) :
    loaded b bits suffix (pairSlots j)=PCPPairCanonical.input [b] bits j := by
  by_cases h2 : j=2
  · subst j
    change loaded b bits suffix 4=frame [b]
    rw [loaded,install_other copySlots _ _ 4 (by decide)]
    exact install_slot signSlots sign_injective _ _ 1
  by_cases h3 : j=3
  · subst j
    have h := install_slot copySlots copy_injective (printed b bits suffix)
      (PCPFieldMoves.output [] bits suffix 0 0) 1
    change loaded b bits suffix 5=ZeroPadding.pad 0 (frame bits) at h
    rw [ZeroPadding.pad_zero] at h
    exact h
  have hj2 : j.val≠2 := fun h => h2 (Fin.ext h)
  have hj3 : j.val≠3 := fun h => h3 (Fin.ext h)
  have hj := j.isLt
  rw [loaded,install_other copySlots _ _ (pairSlots j) (by
    intro k; fin_cases k <;> intro he
    all_goals have hv := congrArg Fin.val he
    all_goals dsimp [copySlots,pairSlots] at hv
    all_goals omega)]
  rw [printed,install_other signSlots _ _ (pairSlots j) (by
    intro k; fin_cases k <;> intro he
    all_goals have hv := congrArg Fin.val he
    all_goals dsimp [signSlots,pairSlots] at hv
    all_goals omega)]
  have h0 : pairSlots j≠0 := by intro h; have hv := congrArg Fin.val h; dsimp [pairSlots] at hv; omega
  have h1 : pairSlots j≠1 := by intro h; have hv := congrArg Fin.val h; dsimp [pairSlots] at hv; omega
  simp only [input,h0,h1,PCPPairCanonical.input,hj2,hj3,ite_false]

theorem pair_run (b : Bool) (bits suffix : List Bool)
    (hpos : 0<Nat.pair (value [b]) (value bits)) :
    ∃ out,ClockJoin.ReadyRun machine (budget b bits) (input b bits suffix) out ∧
      out 28=ZeroPadding.pad (2*PCPPair.width [b] bits+1)
        (frame (Nat.pair (value [b]) (value bits)).bits) := by
  have hs := CompetitorRationalProducts.bounded_focus signSlots sign_injective _ _ _
    (DecompositionSignFrame.ready b) (input b bits suffix) (by intro j; fin_cases j <;> rfl)
  obtain ⟨copy,hcopy,ct,ch,cs⟩ := PCPFieldMoves.ready_run bits suffix 0 0
  have hc : ClockJoin.ReadyRun PCPFieldMoves.readyMachine (4*bits.length+4)
      ![frame bits++suffix,List.replicate 0 false,List.replicate 0 false]
      (PCPFieldMoves.output [] bits suffix 0 0) := ⟨copy,hcopy,ct,ch,cs.le⟩
  have copied := CompetitorRationalProducts.bounded_focus copySlots copy_injective _ _ _ hc
    (printed b bits suffix) (copy_input b bits suffix)
  have prepared := ClockJoin.join _ _ _ _ _ _ _ hs copied
  obtain ⟨paired,hpaired,p26,_⟩ := PCPPairCanonical.pair_run [b] bits hpos
  have hp := CompetitorRationalProducts.bounded_focus pairSlots pair_injective _ _ _ hpaired
    (loaded b bits suffix) (pair_input b bits suffix)
  have whole := ClockJoin.join _ _ _ _ _ _ _ prepared hp
  refine ⟨install pairSlots (loaded b bits suffix) paired,?_,?_⟩
  · convert whole using 1
    · rfl
    · unfold budget
      omega
  · exact (install_slot pairSlots pair_injective _ _ 26).trans p26

theorem int_pair (z : ℤ) :
    Nat.pair (value [decide (z<0)]) (value (CanonicalBinary.encodeNat z.natAbs).bits)=
      CanonicalBinary.encodeInt z := by
  rw [CanonicalPositiveOutput.nat_bits_value]
  unfold CanonicalBinary.encodeInt
  split_ifs <;> simp_all [value]

end NearCubicWires.RepairOrdinary.DecompositionSignedPair
