import Proof.PCP.PCPPQueryIndexPadding

/-! Physical first allocation of the reusable clause-query bank. Source,
raw arity and raw capacity are the only nonblank inputs. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseBank
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templateSlots : Fin 3→Fin 21 := ![19,13,20]
def allocateSlots : Fin 17→Fin 21 := ![1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18]
theorem template_injective : Function.Injective templateSlots := by decide
theorem allocate_injective : Function.Injective allocateSlots := by decide
theorem template_pick (j : Fin 21) : RecoveryFocus.pick templateSlots j=
    (![none,none,none,none,none,none,none,none,none,none,none,none,none,some 1,none,none,none,none,none,some 0,some 2] : Fin 21→Option (Fin 3)) j := by
  fin_cases j
  all_goals first
    | exact RecoveryFocus.pick_slot templateSlots template_injective 0
    | exact RecoveryFocus.pick_slot templateSlots template_injective 1
    | exact RecoveryFocus.pick_slot templateSlots template_injective 2
    | decide

theorem allocate_pick (j : Fin 21) : RecoveryFocus.pick allocateSlots j=
    (![none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,none,some 12,some 13,some 14,some 15,some 16,none,none] : Fin 21→Option (Fin 17)) j := by
  fin_cases j
  all_goals first
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 0
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 1
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 2
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 3
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 4
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 5
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 6
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 7
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 8
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 9
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 10
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 11
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 12
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 13
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 14
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 15
    | exact RecoveryFocus.pick_slot allocateSlots allocate_injective 16
    | decide

def input (source : List Bool) (arity C : ℕ) : Fin 21→List Bool := fun j=>
  if j=0 then source else if j=17 then List.replicate C true else if j=19 then List.replicate arity true else []
noncomputable def middle (source : List Bool) (arity C : ℕ) :=
  install templateSlots (input source arity C) (DimensionTemplate.output false arity)
noncomputable def first := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
noncomputable def last := RecoveryFocus.machine allocateSlots (RecoveryScratchErase.resetMachine 15)
noncomputable def machine := Composition.machine first last
def output (source : List Bool) (arity C : ℕ) : Fin 21→List Bool :=
  ![source,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    UnaryTemplate.tape arity,
    List.replicate C false,
    List.replicate C false,
    List.replicate C false,
    List.replicate C true,
    List.replicate (C+1) false,
    List.replicate arity true,
    List.replicate (arity+3) false]

theorem prepare_ready (source : List Bool) (arity C : ℕ) :
    ClockJoin.ReadyRun machine (2*arity+2*C+13) (input source arity C) (output source arity C) := by
  have ht := (DimensionTemplate.ready false arity).focus templateSlots template_injective
    (input source arity C) (by intro j; fin_cases j <;> rfl)
  change ClockJoin.ReadyRun first (2*arity+8) (input source arity C) (middle source arity C) at ht
  obtain ⟨base,hbase,bt,bh,bs⟩ := RecoveryScratchErase.erase_ready C 0 (fun _ : Fin 15=>[]) (by intro j; simp)
  have hb : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 15) (2*C+4)
      (Fin.addCases (Fin.addCases (fun _ : Fin 15=>[]) (fun _ : Fin 1=>List.replicate C true))
        (fun _ : Fin 1=>List.replicate 0 false))
      (Fin.addCases (Fin.addCases (fun _ : Fin 15=>List.replicate C false) (fun _ : Fin 1=>List.replicate C true))
        (fun _ : Fin 1=>List.replicate (max 0 (C+1)) false)) := ⟨base,hbase,bt,bh,bs.le⟩
  have ha := hb.focus allocateSlots allocate_injective (middle source arity C) (by
    intro j
    fin_cases j <;> simp [middle,install,template_pick,input,allocateSlots,Fin.addCases])
  have hj := ClockJoin.join _ _ _ _ _ _ _ ht ha
  have hcost : (2*arity+8)+1+(2*C+4)=2*arity+2*C+13 := by omega
  rw [hcost] at hj
  change ClockJoin.ReadyRun machine (2*arity+2*C+13) (input source arity C) _ at hj
  convert hj using 1
  funext j
  fin_cases j <;> simp [install,allocate_pick,middle,template_pick,output,input,
    DimensionTemplate.output,Fin.addCases]

end NearCubicWires.RepairOrdinary.PCPPQueryClauseBank
