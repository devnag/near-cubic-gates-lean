import Proof.Hierarchy.CompetitorCrossScalarDrivers
import Proof.Hierarchy.CompetitorPlaneTablePadding

/-! Tape equations for the whole cold cross-table preparation. The native
35-tape bank is kept separate from the two finite dimension scratch banks. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossTablePrepare
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b w n p : ℕ) (source : List Bool) : Fin 120 → List Bool := fun i =>
  if i.val=9 then List.replicate w true else if i.val=20 then List.replicate b true
  else if i.val=32 then source else if i.val=35 then List.replicate n true
  else if i.val=36 then List.replicate p true else []
def scalarSlots (i : Fin 32) : Fin 120 :=
  if i.val=0 then 9 else if i.val=1 then 20 else if i.val=2 then 35 else if i.val=3 then 36
  else if i.val=4 then 21 else if i.val=23 then 27 else if i.val=26 then 34 else if i.val=30 then 33
  else ⟨i.val+36,by omega⟩
def capacitySlots (i : Fin 53) : Fin 120 :=
  if i.val=0 then 9 else if i.val=1 then 35 else if i.val=51 then 30 else ⟨i.val+66,by omega⟩
def paddingSlots : Fin 6 → Fin 120 := ![9,20,21,27,30,119]
theorem scalar_injective : Function.Injective scalarSlots := by decide
theorem capacity_injective : Function.Injective capacitySlots := by decide
theorem padding_injective : Function.Injective paddingSlots := by decide
theorem scalar_value (i : Fin 32) : (scalarSlots i).val=
    if i.val=0 then 9 else if i.val=1 then 20 else if i.val=2 then 35 else if i.val=3 then 36
    else if i.val=4 then 21 else if i.val=23 then 27 else if i.val=26 then 34 else if i.val=30 then 33
    else i.val+36 := by unfold scalarSlots; split_ifs <;> rfl
theorem capacity_value (i : Fin 53) : (capacitySlots i).val=
    if i.val=0 then 9 else if i.val=1 then 35 else if i.val=51 then 30 else i.val+66 := by
  unfold capacitySlots
  split_ifs <;> rfl

def values (D b w n p : ℕ) (source : List Bool) (i : Fin 37) : List Bool :=
  if i.val=9 then List.replicate w true else if i.val=20 then List.replicate b true
  else if i.val=21 then List.replicate (CompetitorPlane.capacity w) true
  else if i.val=27 then CompareMachine.word n else if i.val=30 then List.replicate D true
  else if i.val=32 then source else if i.val=33 then List.replicate (n*b) true
  else if i.val=34 then CompareMachine.word p else if i.val=35 then List.replicate n true
  else if i.val=36 then List.replicate p true else []
def padFields (b w n : ℕ) : Fin 4 → List Bool :=
  ![List.replicate w true,List.replicate b true,List.replicate (CompetitorPlane.capacity w) true,CompareMachine.word n]

theorem scalar_input (b w n p : ℕ) (source : List Bool) :
    ∀ i,input b w n p source (scalarSlots i)=CompetitorCrossScalarDrivers.input w b n p i := by
  intro i
  fin_cases i <;> rfl

theorem scalar_fields (b w n p : ℕ) (source : List Bool) (out : Fin 32 → List Bool)
    (hkeep : ∀ i : Fin 4,out (i.castAdd 28)=CompetitorCrossScalarDrivers.input w b n p (i.castAdd 28))
    (h4 : out 4=List.replicate (CompetitorPlane.capacity w) true)
    (h23 : out 23=CompareMachine.word n) (h26 : out 26=CompareMachine.word p)
    (h30 : out 30=List.replicate (n*b) true) :
    ∀ i : Fin 37,install scalarSlots (input b w n p source) out (i.castAdd 83)=values 0 b w n p source i := by
  intro i
  fin_cases i
  all_goals first
    | exact (install_slot scalarSlots scalar_injective _ out 0).trans (hkeep 0)
    | exact (install_slot scalarSlots scalar_injective _ out 1).trans (hkeep 1)
    | exact (install_slot scalarSlots scalar_injective _ out 2).trans (hkeep 2)
    | exact (install_slot scalarSlots scalar_injective _ out 3).trans (hkeep 3)
    | exact (install_slot scalarSlots scalar_injective _ out 4).trans h4
    | exact (install_slot scalarSlots scalar_injective _ out 23).trans h23
    | exact (install_slot scalarSlots scalar_injective _ out 26).trans h26
    | exact (install_slot scalarSlots scalar_injective _ out 30).trans h30
    | exact install_other scalarSlots _ _ _ (by decide)

theorem scalar_fresh (b w n p : ℕ) (source : List Bool) (out : Fin 32 → List Bool)
    (i : Fin 120) (hi : 68 ≤ i.val) : install scalarSlots (input b w n p source) out i=[] := by
  rw [install_other _ _ _ _ (by
    intro j hj
    have hv := congrArg Fin.val hj
    rw [scalar_value] at hv
    split_ifs at hv <;> omega)]
  simp [input,show i.val≠9 by omega,show i.val≠20 by omega,show i.val≠32 by omega,
    show i.val≠35 by omega,show i.val≠36 by omega]

theorem capacity_input (b w n p : ℕ) (source : List Bool) (out : Fin 32 → List Bool)
    (hfields : ∀ i : Fin 37,install scalarSlots (input b w n p source) out (i.castAdd 83)=values 0 b w n p source i) :
    ∀ i,install scalarSlots (input b w n p source) out (capacitySlots i)=CompetitorCrossCapacity.input w n i := by
  intro i
  by_cases h0 : i.val=0
  · have he : i=0 := Fin.ext h0
    subst i
    exact hfields 9
  by_cases h1 : i.val=1
  · have he : i=1 := Fin.ext h1
    subst i
    exact hfields 35
  by_cases h51 : i.val=51
  · have he : i=51 := Fin.ext h51
    subst i
    exact hfields 30
  · rw [scalar_fresh _ _ _ _ _ _ _ (by rw [capacity_value,if_neg h0,if_neg h1,if_neg h51]; omega)]
    simp [CompetitorCrossCapacity.input,h0,h1]

theorem capacity_fields (D b w n p : ℕ) (source : List Bool) (ambient : Fin 120 → List Bool)
    (out : Fin 53 → List Bool)
    (hfields : ∀ i : Fin 37,ambient (i.castAdd 83)=values 0 b w n p source i)
    (h0 : out 0=List.replicate w true) (h1 : out 1=List.replicate n true)
    (h51 : out 51=List.replicate D true) :
    ∀ i : Fin 37,install capacitySlots ambient out (i.castAdd 83)=values D b w n p source i := by
  intro i
  fin_cases i
  all_goals first
    | exact (install_slot capacitySlots capacity_injective _ out 0).trans h0
    | exact (install_slot capacitySlots capacity_injective _ out 1).trans h1
    | exact (install_slot capacitySlots capacity_injective _ out 51).trans h51
    | exact (install_other capacitySlots _ _ _ (by decide)).trans (hfields _)

theorem padding_input (b w n p : ℕ) (source : List Bool) (ambient : Fin 120 → List Bool)
    (hfields : ∀ i : Fin 37,ambient (i.castAdd 83)=values (CompetitorPlanePacketPass.capacity w n) b w n p source i)
    (hfresh : ambient 119=[]) : ∀ i,ambient (paddingSlots i)=
      CompetitorPlaneTablePadding.input (CompetitorPlanePacketPass.capacity w n) (padFields b w n) i := by
  intro i
  fin_cases i
  · exact hfields 9
  · exact hfields 20
  · exact hfields 21
  · exact hfields 27
  · exact hfields 30
  · exact hfresh

theorem padding_fields (b w n p : ℕ) (source : List Bool) (ambient : Fin 120 → List Bool)
    (hfields : ∀ i : Fin 37,ambient (i.castAdd 83)=values (CompetitorPlanePacketPass.capacity w n) b w n p source i) :
    ∀ i : Fin 35,install paddingSlots ambient
      (CompetitorPlaneTablePadding.output (CompetitorPlanePacketPass.capacity w n) (padFields b w n))
      (i.castAdd 85)=CompetitorPlaneTableCold.input b w n p source i := by
  intro i
  have hf := hfields (i.castAdd 2)
  fin_cases i
  all_goals first
    | exact install_slot paddingSlots padding_injective _ _ 0
    | exact install_slot paddingSlots padding_injective _ _ 1
    | exact install_slot paddingSlots padding_injective _ _ 2
    | exact install_slot paddingSlots padding_injective _ _ 3
    | exact install_slot paddingSlots padding_injective _ _ 4
    | exact (install_other paddingSlots _ _ _ (by decide)).trans hf

end NearCubicWires.RepairOrdinary.CompetitorCrossTablePrepare
