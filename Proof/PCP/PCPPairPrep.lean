import Proof.PCP.PCPPairWidthRun

/-! Physical pair-node preparation from just the two framed operands.
The width and both normalized copies are produced by ordinary machines. -/
namespace NearCubicWires.RepairOrdinary.PCPPairCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (left right : List Bool) : Fin 35 → List Bool := fun i =>
  if i.val=2 then frame left else if i.val=3 then frame right else []
def sized (left right : List Bool) : Fin 35 → List Bool := fun i =>
  if i.val=4 then List.replicate (PCPPair.width left right) true
  else if i.val=30 then List.replicate (PCPPair.width left right) false
  else input left right i
def leftReady (left right : List Bool) : Fin 35 → List Bool := fun i =>
  if i.val=0 then frame (binary (PCPPair.width left right) (value left))
  else if i.val=31 then [true]
  else if i.val=32 then List.replicate (2*PCPPair.width left right+1) false
  else sized left right i
def prepared (left right : List Bool) : Fin 35 → List Bool := fun i =>
  if i.val=1 then frame (binary (PCPPair.width left right) (value right))
  else if i.val=33 then [true]
  else if i.val=34 then List.replicate (2*PCPPair.width left right+1) false
  else leftReady left right i

def widthSlots : Fin 4 → Fin 35 := ![2,3,4,30]
def leftSlots : Fin 5 → Fin 35 := ![4,2,0,31,32]
def rightSlots : Fin 5 → Fin 35 := ![4,3,1,33,34]
def pairSlots (i : Fin 30) : Fin 35 := ⟨i.val,by omega⟩
theorem width_injective : Function.Injective widthSlots := by decide
theorem left_injective : Function.Injective leftSlots := by decide
theorem right_injective : Function.Injective rightSlots := by decide
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 35 => k.val) h)

noncomputable def widthProgram := RecoveryFocus.machine widthSlots PCPPairWidth.machine
noncomputable def leftProgram := RecoveryFocus.machine leftSlots ClockNormalize.machine
noncomputable def rightProgram := RecoveryFocus.machine rightSlots ClockNormalize.machine
noncomputable def pairProgram := RecoveryFocus.machine pairSlots PCPPair.machine
noncomputable def prepareProgram :=
  Composition.machine (Composition.machine widthProgram leftProgram) rightProgram
noncomputable def machine := Composition.machine prepareProgram pairProgram

theorem width_ready (left right : List Bool) :
    ClockJoin.ReadyRun widthProgram (2*PCPPair.width left right+2)
      (input left right) (sized left right) := by
  have h := CompetitorRationalProducts.bounded_focus widthSlots width_injective
    _ _ _ (PCPPairWidth.width_run left right) (input left right)
    (by intro j; fin_cases j <;> rfl)
  have he : install widthSlots (input left right)
      ![frame left,frame right,List.replicate (PCPPair.width left right) true,
        List.replicate (PCPPair.width left right) false]=sized left right := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot widthSlots width_injective _ _ 0
      | exact install_slot widthSlots width_injective _ _ 1
      | exact install_slot widthSlots width_injective _ _ 2
      | exact install_slot widthSlots width_injective _ _ 3
      | exact install_other widthSlots _ _ _ (by decide)
  exact he ▸ h

theorem normalized_ready (w : ℕ) (bits : List Bool) (hlen : bits.length ≤ w) :
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockNormalize.input w bits)
      ![List.replicate w true,frame bits,frame (binary w (value bits)),[true],
        List.replicate (2*w+1) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w bits hlen
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem left_ready (left right : List Bool) :
    ClockJoin.ReadyRun leftProgram (4*PCPPair.width left right+4)
      (sized left right) (leftReady left right) := by
  have h := CompetitorRationalProducts.bounded_focus leftSlots left_injective
    _ _ _ (normalized_ready (PCPPair.width left right) left (by unfold PCPPair.width; omega))
    (sized left right) (by intro j; fin_cases j <;> rfl)
  have he : install leftSlots (sized left right)
      ![List.replicate (PCPPair.width left right) true,frame left,
        frame (binary (PCPPair.width left right) (value left)),[true],
        List.replicate (2*PCPPair.width left right+1) false]=leftReady left right := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot leftSlots left_injective _ _ 0
      | exact install_slot leftSlots left_injective _ _ 1
      | exact install_slot leftSlots left_injective _ _ 2
      | exact install_slot leftSlots left_injective _ _ 3
      | exact install_slot leftSlots left_injective _ _ 4
      | exact install_other leftSlots _ _ _ (by decide)
  exact he ▸ h

theorem right_ready (left right : List Bool) :
    ClockJoin.ReadyRun rightProgram (4*PCPPair.width left right+4)
      (leftReady left right) (prepared left right) := by
  have h := CompetitorRationalProducts.bounded_focus rightSlots right_injective
    _ _ _ (normalized_ready (PCPPair.width left right) right (by unfold PCPPair.width; omega))
    (leftReady left right) (by intro j; fin_cases j <;> rfl)
  have he : install rightSlots (leftReady left right)
      ![List.replicate (PCPPair.width left right) true,frame right,
        frame (binary (PCPPair.width left right) (value right)),[true],
        List.replicate (2*PCPPair.width left right+1) false]=prepared left right := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot rightSlots right_injective _ _ 0
      | exact install_slot rightSlots right_injective _ _ 1
      | exact install_slot rightSlots right_injective _ _ 2
      | exact install_slot rightSlots right_injective _ _ 3
      | exact install_slot rightSlots right_injective _ _ 4
      | exact install_other rightSlots _ _ _ (by decide)
  exact he ▸ h

theorem prepare_run (left right : List Bool) :
    ClockJoin.ReadyRun prepareProgram (10*PCPPair.width left right+12)
      (input left right) (prepared left right) := by
  have h := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (width_ready left right) (left_ready left right))
    (right_ready left right)
  convert h using 1
  · rfl
  · omega

theorem prepared_pair (left right : List Bool) (i : Fin 30) :
    prepared left right (pairSlots i)=PCPPair.input left right i := by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPPairCold
