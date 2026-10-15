import Proof.Amplification.RecoveryRefuterReplayWhole

/-! An actual canonical legacy list-cell producer.  The cold pair, growing
binary increment, and positive canonical-output machines execute pair(a,b)+1
from the two framed operands.  Zero operands require no exceptional premise. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryPairSuccessor
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots (i : Fin 35) : Fin 39 := ⟨i.val,by omega⟩
def incrementSlots : Fin 2 → Fin 39 := ![26,35]
def outputSlots : Fin 4 → Fin 39 := ![26,36,37,38]
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 39 => k.val) h)
theorem increment_injective : Function.Injective incrementSlots := by decide
theorem output_injective : Function.Injective outputSlots := by decide
noncomputable def pairProgram := RecoveryFocus.machine pairSlots PCPPairCold.machine
noncomputable def incrementProgram := RecoveryFocus.machine incrementSlots ClockIncrement.machine
noncomputable def outputProgram := RecoveryFocus.machine outputSlots CanonicalPositiveOutput.machine
noncomputable def machine := Composition.machine (Composition.machine pairProgram incrementProgram) outputProgram
def input (left right : List Bool) : Fin 39 → List Bool := fun i =>
  if i.val=2 then frame left else if i.val=3 then frame right else []
def budget (left right : List Bool) : Nat :=
  PCPPairCold.budget left right+12*PCPPair.width left right+32

theorem pair_other (ambient : Fin 39 → List Bool) (out : Fin 35 → List Bool)
    (i : Fin 39) (hi : 35 ≤ i.val) : install pairSlots ambient out i=ambient i := by
  apply install_other
  intro j he
  have h := congrArg Fin.val he
  simp only [pairSlots] at h
  have hj := j.isLt
  omega

theorem pair_successor_run (left right : List Bool) :
    ∃ out : Fin 39 → List Bool,
      ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      (∃ padding,out 26=frame (Nat.pair (value left) (value right)+1).bits++List.replicate padding false) ∧
      out 37=(Nat.pair (value left) (value right)+1).bits := by
  let w := PCPPair.width left right
  let n := Nat.pair (value left) (value right)
  let bits := binary w n
  obtain ⟨paired,hpair,hfield⟩ := PCPPairCold.pair_run left right
  have hp := hpair.focus pairSlots pair_injective (input left right)
    (by intro j; fin_cases j <;> rfl)
  let first := install pairSlots (input left right) paired
  have hf : first 26=frame bits :=
    (install_slot pairSlots pair_injective _ _ 26).trans hfield
  have hz : first 35=[] := pair_other _ _ _ (by decide)
  obtain ⟨r,hr,hbits,hcap,hh,hs,_⟩ := ClockIncrement.increment_run bits 0
  have hinput : (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame bits) (fun _ : Fin 1 => List.replicate 0 false))=
      ![frame bits,[]] := by funext i; fin_cases i <;> rfl
  rw [hinput] at hr
  have hout : r.final.tapes=![frame (ClockIncrement.next bits),List.replicate (ClockIncrement.work bits) false] := by
    funext i
    fin_cases i
    · exact hbits
    · simpa using hcap
  have hi : ClockJoin.ReadyRun ClockIncrement.machine (2*ClockIncrement.work bits+2)
      ![frame bits,[]] ![frame (ClockIncrement.next bits),List.replicate (ClockIncrement.work bits) false] :=
    ⟨r,hr,hout,hh,hs.le⟩
  have hinc := hi.focus incrementSlots increment_injective first
    (by intro j; fin_cases j; exact hf; exact hz)
  let second := install incrementSlots first
    ![frame (ClockIncrement.next bits),List.replicate (ClockIncrement.work bits) false]
  have hv : value (ClockIncrement.next bits)=n+1 := by
    rw [ClockIncrement.next_value]
    exact congrArg (fun a => a+1) (binary_value w n (PCPPair.pair_bound left right))
  have hbinary : binary (ClockIncrement.next bits).length (n+1)=ClockIncrement.next bits := by
    have h := BoundedCounter.binary_of_value (ClockIncrement.next bits)
    rw [hv] at h
    exact h
  have hfit : n+1<2^(ClockIncrement.next bits).length := by
    rw [←hv]
    exact value_lt _
  obtain ⟨canonical,hcanonical,hraw,hframed⟩ := CanonicalPositiveOutput.binary_output_fields
    (ClockIncrement.next bits).length (n+1) (by omega) hfit
  rw [hbinary] at hcanonical
  have hin : ∀ j,second (outputSlots j)=CanonicalPositiveOutput.input (ClockIncrement.next bits) j := by
    intro j
    fin_cases j
    · exact install_slot incrementSlots increment_injective _ _ 0
    all_goals
      dsimp only [second,first]
      rw [install_other incrementSlots _ _ _ (by intro k; fin_cases k <;> decide),
        pair_other _ _ _ (by decide)]
      rfl
  have hc := hcanonical.focus outputSlots output_injective second hin
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hp hinc) hc
  have hw : bits.length=w := by simp [bits]
  have hwork := ClockIncrement.work_bound bits
  have hlen := (ClockIncrement.next_length bits).2
  have hbudget : PCPPairCold.budget left right+1+(2*ClockIncrement.work bits+2)+1+
      (8*(ClockIncrement.next bits).length+9) ≤ budget left right := by
    unfold budget
    dsimp [w] at hw
    omega
  refine ⟨install outputSlots second canonical,ClockJoin.enlarge _ _ _ _ _ hwhole hbudget,?_,?_⟩
  · refine ⟨2*(ClockIncrement.next bits).length+1-(frame (n+1).bits).length,?_⟩
    exact (install_slot _ output_injective _ _ 0).trans hframed
  · exact (install_slot _ output_injective _ _ 2).trans hraw

end NearCubicWires.RepairOrdinary.RecoveryQueryPairSuccessor
