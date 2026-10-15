import Proof.PCP.PCPUnaryCopy
import Proof.PCP.PCPSerializerCapacityAmbient
import Proof.PCP.PCPSerializerCountReady
import Proof.Hierarchy.HierarchyFixedWord
import Proof.Amplification.RecoveryScratchErase

namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Packed := Σ s : ℕ,Machine 128 s
def pack {s : ℕ} (p : Machine 128 s) : Packed := ⟨s,p⟩
noncomputable def focused {t s : ℕ} (slots : Fin t → Fin 128) (p : Machine t s) : Packed :=
  pack (RecoveryFocus.machine slots p)

def eraseSlots {t : ℕ} (slots : Fin t → Fin 128) : Fin (t+1+1) → Fin 128 :=
  Fin.addCases (Fin.addCases slots (fun _ : Fin 1 => 28)) (fun _ : Fin 1 => 127)
noncomputable def clear {t : ℕ} (slots : Fin t → Fin 128) : Packed :=
  focused (eraseSlots slots) (RecoveryScratchErase.resetMachine t)
def bank (i : Fin 38) : Fin 128 := ⟨39+i.val,by omega⟩
def pairSlots (i : Fin 38) : Fin 128 :=
  if i.val=2 then 83 else if i.val=3 then 84 else bank i
def capacitySlots (i : Fin 39) : Fin 128 := ⟨i.val,by omega⟩

theorem bank_injective : Function.Injective bank := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [bank] at hv
  omega
theorem pair_injective : Function.Injective pairSlots := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [pairSlots,bank] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem capacity_injective : Function.Injective capacitySlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

noncomputable def printer (bits : List Bool) (out log : Fin 128) : Packed :=
  focused ![out,log] (HierarchyFixedWord.machine bits)
noncomputable def copyField (source out log : Fin 128) : Packed :=
  focused ![source,out,log] PCPFieldMoves.readyMachine
noncomputable def emptyProgram : Packed :=
  pack (Composition.machine (clear ![77,89]).2 (printer (frame []) 77 89).2)

noncomputable def call : Fin 39 → Packed
  | 0 => focused ![79] PCPControlOps.testMachine
  | 1 => emptyProgram
  | 2 => clear ![83,84,89,90]
  | 3 => printer (frame (1 : ℕ).bits) 83 89
  | 4 => focused ![0,84,90] PCPFieldMoves.advanceMachine
  | 5 => clear bank
  | 6 => focused pairSlots PCPPairCanonical.machine
  | 7 => clear ![77,91]
  | 8 => copyField 65 77 91
  | 9 => focused ![81] PCPContinuation.machine
  | 10 => clear ![92]
  | 11 => focused ![77,82,92] PCPStackPush.machine
  | 12 => clear ![93,94,79,95]
  | 13 => focused ![80,93,94,79,95] PCPUnaryStackPop.machine
  | 14 => clear ![85,86,87]
  | 15 => focused ![79,85,86,87] PCPUnarySplit.machine
  | 16 => clear ![92]
  | 17 => focused ![86,80,92] PCPUnaryStackPush.machine
  | 18 => focused ![81] PCPControlOps.pushMachine
  | 19 => clear ![79,96]
  | 20 => focused ![85,79,96] PCPUnaryCopy.machine
  | 21 => clear ![83,84,90,92]
  | 22 => focused ![82,83,92] PCPStackReady.machine
  | 23 => copyField 77 84 90
  | 24 => clear bank
  | 25 => focused pairSlots PCPPairCanonical.machine
  | 26 => clear ![77,91]
  | 27 => copyField 65 77 91
  | 28 => clear ![83,84,89,90]
  | 29 => printer (frame (2 : ℕ).bits) 83 89
  | 30 => copyField 77 84 90
  | 31 => clear bank
  | 32 => focused pairSlots PCPPairCanonical.machine
  | 33 => clear ![77,91]
  | 34 => copyField 65 77 91
  | 35 => clear ![97]
  | 36 => focused ![77,78,97] Streaming.machine
  | 37 => focused capacitySlots (PCPSerializerCapacity.machine 10 131072)
  | _ => pack PCPSerializerCountEntry.machine

noncomputable def sizes (j : Fin 39) := (call j).1
noncomputable def programs (j : Fin 39) : Machine 128 (sizes j) := (call j).2
noncomputable def next (j : Fin 39) (q : Fin (sizes j)) (_ : Fin 128 → Bool) : Option (Fin 39) :=
  if j=0 then if q.val=2 then some 1 else if q.val=3 then some 2 else some 14
  else if j=1 then some 35
  else if j=8 then some 9
  else if j=9 then if q.val=5 then some 10 else if q.val=6 then some 35 else some 21
  else if j=13 then some 0
  else if j=20 then some 0
  else if j=27 then some 28
  else if j=34 then some 9
  else if j=36 then none
  else if j=38 then some 0
  else some ⟨(j.val+1)%39,Nat.mod_lt _ (by decide)⟩
noncomputable def machine := RecoveryCalls.machine sizes programs 37 next

def input (source : List Bool) (count : ℕ) : Fin 128 → List Bool :=
  fun i => if i=0 then source else if i=2 then RepairSource.VerifierDecoding.CompareMachine.word count else []
def heads (pos : ℕ) : Fin 128 → ℕ := fun i => if i=0 then pos else if i=2 then 1 else 0
noncomputable def entry (source : List Bool) (pos count : ℕ) :=
  (⟨machine.start,heads pos,input source count⟩ : Configuration 128 _)
def budget (B : ℕ) : ℕ := 1000000000000*(B+1)^12

theorem raw_output_slot : pairSlots 26=65 := rfl
theorem operands_distinct : pairSlots 2=83 ∧ pairSlots 3=84 := ⟨rfl,rfl⟩
theorem clear_preserves_drivers (i : Fin 38) : bank i≠28 ∧ bank i≠127 := by
  constructor <;> intro h <;> have hv := congrArg Fin.val h <;> simp only [bank] at hv <;> omega

end NearCubicWires.RepairOrdinary.PCPTraversal
