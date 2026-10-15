import Proof.Amplification.RecoveryPrefixPrepare
import Proof.Amplification.RecoveryPrefixSearchReady
import Proof.Amplification.RecoveryPrefixDriverSeal
import Proof.Amplification.RecoveryPrefixOutputWhole
import Proof.MachineModel.UInputFields

/-! The cold canonical prefix search's fixed five-call program. Original
outer framing is removed once; actual capacity preparation, oracle iteration,
sentinel sealing and bounded exact output extraction follow in order. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unwrapSlots : Fin 3→Fin 389 := ![0,1,381]
def coldSlots (i : Fin 380) : Fin 389 := ⟨i.val+1,by have h:=i.isLt; omega⟩
def loopSlots (i : Fin 361) : Fin 389 := ⟨i.val+1,by have h:=i.isLt; omega⟩
def sealSlots : Fin 2→Fin 389 := ![361,388]
def outputSlots : Fin 8→Fin 389 := ![2,361,382,383,384,385,386,387]
theorem unwrap_injective : Function.Injective unwrapSlots := by decide
theorem cold_injective : Function.Injective coldSlots := by
  intro a b h; apply Fin.ext; have hv:=congrArg (fun i : Fin 389=>i.val) h; dsimp [coldSlots] at hv; omega
theorem loop_injective : Function.Injective loopSlots := by
  intro a b h; apply Fin.ext; have hv:=congrArg (fun i : Fin 389=>i.val) h; dsimp [loopSlots] at hv; omega
theorem seal_injective : Function.Injective sealSlots := by decide
theorem output_injective : Function.Injective outputSlots := by decide

def ports : Ports 389 := ⟨by decide,386,by decide,344,by decide⟩
noncomputable def unwrap := RecoveryFocus.machine unwrapSlots Streaming.machine
noncomputable def prepare (C : Nat) := RecoveryFocus.machine coldSlots (RecoveryPrefixColdPrepare.machine C)
noncomputable def sealProgram := RecoveryFocus.machine sealSlots RecoveryPrefixDriverSeal.machine
noncomputable def output := RecoveryFocus.machine outputSlots RecoveryPrefixOutput.machine
noncomputable def pieces (C : Nat) (flat : Bool) : Fin 5→Piece 389
  | ⟨0,_⟩ => ordinary unwrap
  | ⟨1,_⟩ => ordinary (prepare C)
  | ⟨2,_⟩ => focused (RecoveryPrefixSearch.program flat) loopSlots
  | ⟨3,_⟩ => ordinary sealProgram
  | ⟨4,_⟩ => ordinary output
  | ⟨n+5,h⟩ => False.elim (by omega)
def next (C : Nat) (flat : Bool) (j : Fin 5) (_ : Fin (pieces C flat j).states)
    (_ : Fin 389→Bool) : Option (Fin 5) := if h : j.val<4 then some ⟨j.val+1,by omega⟩ else none
noncomputable abbrev program (C : Nat) (flat : Bool) := ports.program (graph (pieces C flat) 0 (next C flat))

theorem loop_query (flat : Bool) : loopSlots (RecoveryPrefixSearch.program flat).queryTape=ports.queryTape := rfl

def input (payload total : Nat) : Fin 389→List Bool :=
  fun i=>if i.val=0 then frame (RecoveryPrefixMeasure.request payload total) else []
noncomputable def unwrapped (payload total : Nat) := install unwrapSlots (input payload total)
  ![frame (RecoveryPrefixMeasure.request payload total),RecoveryPrefixMeasure.request payload total,
    List.replicate (RecoveryPrefixMeasure.request payload total).length false]

def budget (C payload total : Nat) :=
  (4*(RecoveryPrefixMeasure.request payload total).length+2)+
  RecoveryPrefixColdPrepare.budget C payload total+
  RecoveryPrefixSearch.budget (RecoveryPrefixColdPrepare.capacity C payload total) total+
  (2*total+6)+RecoveryPrefixOutput.budget total+5

theorem capacity_covers (C payload total : Nat) (hC : 1073741824≤C) :
    RecoveryPrefix.workspace payload total≤RecoveryPrefixColdPrepare.capacity C payload total := by
  rw [←RecoveryPrefixMeasure.capacity_eq]
  exact Nat.mul_le_mul_right _ hC

theorem capacity_large (C payload total : Nat) (hC : 1073741824≤C) :
    5≤RecoveryPrefixColdPrepare.capacity C payload total := by
  have hp : 1≤(RecoveryPrefixMeasure.mass payload total+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_left C hp
  dsimp [RecoveryPrefixColdPrepare.capacity]
  omega

end NearCubicWires.RepairSource.RecoveryPrefixCold
