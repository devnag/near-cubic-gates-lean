import Proof.Hierarchy.CompetitorResidueCell

/-! Native arithmetic in one aligned signed-plane cell. The two finite sign
branches share the same short multiplier and differ only in which retained
accumulator is added. The enclosing plane controller selects the branch from
the physical sign bit. No global table cursor enters this local program. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlane
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def multiplySlots (i : Fin 14) : Fin 17 := i.castAdd 3
def accumulatorTape (negative : Bool) : Fin 17 := if negative then 15 else 14
def positiveTape (negative : Bool) : Fin 17 := if negative then 14 else 16
def negativeTape (negative : Bool) : Fin 17 := if negative then 16 else 15
def addSlots (negative : Bool) : Fin 4 → Fin 17 := ![3,accumulatorTape negative,16,12]
noncomputable def multiplyProgram := RecoveryFocus.machine multiplySlots HierarchyMultiplyEntry.machine
noncomputable def addProgram (negative : Bool) := RecoveryFocus.machine (addSlots negative) BoundaryAdvance.machine
noncomputable def arithmeticProgram (negative : Bool) := Composition.machine multiplyProgram (addProgram negative)

def arithmeticInput (w count positive negative : ℕ) (bits : List Bool) : Fin 17 → List Bool :=
  Fin.addCases (m := 14) (n := 3) (motive := fun _ => List Bool)
    (HierarchyMultiplyEntry.input14 w count bits)
    ![frame (binary w positive),frame (binary w negative),[]]
def nextPositive (negative : Bool) (positive count : ℕ) (bits : List Bool) :=
  if negative then positive else count*value bits+positive
def nextNegative (negative : Bool) (old count : ℕ) (bits : List Bool) :=
  if negative then count*value bits+old else old
def arithmeticBudget (w : ℕ) (bits : List Bool) := HierarchyMultiplyEntry.budget w bits+4*w+5

theorem multiplySlots_injective : Function.Injective multiplySlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 17 => a.val) h)
theorem addSlots_injective (negative : Bool) : Function.Injective (addSlots negative) := by
  cases negative <;> decide

theorem arithmetic_run (sign : Bool) (w count positive negative : ℕ) (bits : List Bool)
    (hshift : count*2^bits.length<2^w)
    (hadd : count*value bits+(if sign then negative else positive)<2^w) :
    ∃ out,ClockJoin.ReadyRun (arithmeticProgram sign) (arithmeticBudget w bits)
        (arithmeticInput w count positive negative bits) out ∧
      out (positiveTape sign)=frame (binary w (nextPositive sign positive count bits)) ∧
      out (negativeTape sign)=frame (binary w (nextNegative sign negative count bits)) ∧
      out 0=frame bits ∧ out 8=frame (binary w count) ∧
      out 9=List.replicate w true ∧ out 12=List.replicate (2*w+1) false := by
  obtain ⟨base,hr,h3,h0,h8,h9,h12,hh,hs⟩ := HierarchyMultiplyEntry.multiply_run w count bits hshift
  have ready : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine (HierarchyMultiplyEntry.budget w bits)
      (HierarchyMultiplyEntry.input14 w count bits) base.final.tapes := ⟨base,hr,rfl,hh,hs⟩
  have hmul := CompetitorRationalProducts.bounded_focus multiplySlots multiplySlots_injective _ _ _ ready
    (arithmeticInput w count positive negative bits) (by intro j; simp [arithmeticInput,multiplySlots])
  let middle := install multiplySlots (arithmeticInput w count positive negative bits) base.final.tapes
  have hm3 : middle 3=frame (binary w (count*value bits)) :=
    (install_slot multiplySlots multiplySlots_injective _ _ 3).trans h3
  have hm12 : middle 12=List.replicate (2*w+1) false :=
    (install_slot multiplySlots multiplySlots_injective _ _ 12).trans h12
  have hm14 : middle 14=frame (binary w positive) :=
    install_other multiplySlots _ _ 14 (by decide)
  have hm15 : middle 15=frame (binary w negative) :=
    install_other multiplySlots _ _ 15 (by decide)
  have hm16 : middle 16=[] := install_other multiplySlots _ _ 16 (by decide)
  let selected := if sign then negative else positive
  have hmselected : middle (accumulatorTape sign)=frame (binary w selected) := by
    cases sign <;> assumption
  have addReady := HierarchyBinary.add_ready w (count*value bits) selected (2*w+1) [] hadd (by simp)
  simp only [max_self] at addReady
  have haddReady : ClockJoin.ReadyRun BoundaryAdvance.machine (4*w+4)
      ![frame (binary w (count*value bits)),frame (binary w selected),[],List.replicate (2*w+1) false]
      ![frame (binary w (count*value bits)),frame (binary w selected),
        frame (binary w (count*value bits+selected)),List.replicate (2*w+1) false] := by
    obtain ⟨a,ha,hat,hah,has⟩ := addReady
    exact ⟨a,ha,hat,hah,has.le⟩
  have haddRun := CompetitorRationalProducts.bounded_focus (addSlots sign) (addSlots_injective sign) _ _ _ haddReady middle
    (by intro j; fin_cases j; exact hm3; exact hmselected; exact hm16; exact hm12)
  let out := install (addSlots sign) middle
    ![frame (binary w (count*value bits)),frame (binary w selected),
      frame (binary w (count*value bits+selected)),List.replicate (2*w+1) false]
  have hout16 : out 16=frame (binary w (count*value bits+selected)) :=
    install_slot (addSlots sign) (addSlots_injective sign) _ _ 2
  have hout14 : sign=true → out 14=frame (binary w positive) := by
    intro hsign
    subst sign
    exact (install_other (addSlots true) _ _ 14 (by decide)).trans hm14
  have hout15 : sign=false → out 15=frame (binary w negative) := by
    intro hsign
    subst sign
    exact (install_other (addSlots false) _ _ 15 (by decide)).trans hm15
  have joined := ClockJoin.join multiplyProgram (addProgram sign) _ _ _ _ _ hmul haddRun
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · have htime : HierarchyMultiplyEntry.budget w bits+1+(4*w+4)=arithmeticBudget w bits := by
      unfold arithmeticBudget
      omega
    simpa only [htime,arithmeticProgram] using joined
  · cases sign
    · exact hout16
    · exact hout14 rfl
  · cases sign
    · exact hout15 rfl
    · exact hout16
  · exact (install_other (addSlots sign) _ _ 0 (by cases sign <;> decide)).trans
      ((install_slot multiplySlots multiplySlots_injective _ _ 0).trans h0)
  · exact (install_other (addSlots sign) _ _ 8 (by cases sign <;> decide)).trans
      ((install_slot multiplySlots multiplySlots_injective _ _ 8).trans h8)
  · exact (install_other (addSlots sign) _ _ 9 (by cases sign <;> decide)).trans
      ((install_slot multiplySlots multiplySlots_injective _ _ 9).trans h9)
  · exact install_slot (addSlots sign) (addSlots_injective sign) _ _ 3

end NearCubicWires.RepairOrdinary.CompetitorPlane
