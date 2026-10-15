import Proof.Circuits.CanonicalBinaryFields

/-! A complete positive pair-node call with canonical output. Canonicalizing
each stored node permits the serializer to reuse the checked balanced-code
size bound, while padded cells remain explicit in its local workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPairCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots (i : Fin 35) : Fin 38 := ⟨i.val,by omega⟩
def outputSlots : Fin 4 → Fin 38 := ![26,35,36,37]
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 38 => k.val) h)
theorem output_injective : Function.Injective outputSlots := by decide
noncomputable def pairProgram := RecoveryFocus.machine pairSlots PCPPairCold.machine
noncomputable def outputProgram := RecoveryFocus.machine outputSlots CanonicalPositiveOutput.machine
noncomputable def machine := Composition.machine pairProgram outputProgram
def input (left right : List Bool) : Fin 38 → List Bool := fun i =>
  if i.val=2 then frame left else if i.val=3 then frame right else []
def budget (left right : List Bool) : ℕ :=
  PCPPairCold.budget left right+8*PCPPair.width left right+10

theorem pair_run (left right : List Bool) (hpos : 0<Nat.pair (value left) (value right)) :
    ∃ out : Fin 38 → List Bool,
      ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      out 26=ZeroPadding.pad (2*PCPPair.width left right+1)
        (frame (Nat.pair (value left) (value right)).bits) ∧
      out 36=(Nat.pair (value left) (value right)).bits := by
  obtain ⟨paired,hpair,hfield⟩ := PCPPairCold.pair_run left right
  have hp := CompetitorRationalProducts.bounded_focus pairSlots pair_injective _ _ _ hpair
    (input left right) (by intro j; fin_cases j <;> rfl)
  let middle := install pairSlots (input left right) paired
  have hm : middle 26=frame (binary (PCPPair.width left right) (Nat.pair (value left) (value right))) :=
    (install_slot pairSlots pair_injective _ _ 26).trans hfield
  obtain ⟨canonical,hcanonical,hraw,hframed⟩ := CanonicalPositiveOutput.binary_output_fields
    (PCPPair.width left right) (Nat.pair (value left) (value right)) hpos (PCPPair.pair_bound left right)
  have hin : ∀ j,middle (outputSlots j)=CanonicalPositiveOutput.input
      (binary (PCPPair.width left right) (Nat.pair (value left) (value right))) j := by
    intro j
    fin_cases j
    · exact hm
    · exact install_other pairSlots _ _ 35 (by intro k he; have h := congrArg Fin.val he; simp [pairSlots] at h; omega)
    · exact install_other pairSlots _ _ 36 (by intro k he; have h := congrArg Fin.val he; simp [pairSlots] at h; omega)
    · exact install_other pairSlots _ _ 37 (by intro k he; have h := congrArg Fin.val he; simp [pairSlots] at h; omega)
  have hc := CompetitorRationalProducts.bounded_focus outputSlots output_injective _ _ _ hcanonical middle hin
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ hp hc
  refine ⟨install outputSlots middle canonical,?_,?_,?_⟩
  · convert hwhole using 1
    · rfl
    · unfold budget
      omega
  · exact (install_slot outputSlots output_injective _ _ 0).trans hframed
  · exact (install_slot outputSlots output_injective _ _ 2).trans hraw

theorem budget_quadratic (left right : List Bool) :
    budget left right ≤ 2048*(left.length+right.length+1)^2 := by
  have h := PCPPairCold.budget_quadratic left right
  unfold budget PCPPair.width
  have hn : 1 ≤ left.length+right.length+1 := by omega
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPairCanonical
