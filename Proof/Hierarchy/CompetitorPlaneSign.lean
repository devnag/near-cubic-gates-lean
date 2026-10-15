import Proof.Hierarchy.CompetitorPlaneEntry
import Proof.Amplification.RecoveryCursorCalls

/-! One fixed ordinary plane machine reads the actual sign tape once,
executes the corresponding complete cold pass, and returns with every head
reset. The sign is not a runtime choice of a different program. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneSign
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 29) : Fin 30 := i.castAdd 1
def machineStates {t s : ℕ} (_ : Machine t s) := s
def idle : Machine 30 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def sizes : Fin 3 → ℕ := ![1,machineStates (CompetitorPlaneEntry.machine false),machineStates (CompetitorPlaneEntry.machine true)]
noncomputable def programs : (j : Fin 3) → Machine 30 (sizes j)
  | 0 => idle
  | 1 => RecoveryFocus.machine native (CompetitorPlaneEntry.machine false)
  | 2 => RecoveryFocus.machine native (CompetitorPlaneEntry.machine true)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 30 → Bool) : Option (Fin 3) :=
  if j.val=0 then if bits 29 then some 2 else some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell) : Fin 30 → List Bool :=
  Fin.addCases (m := 29) (n := 1) (motive := fun _ => List Bool)
    (CompetitorPlaneEntry.readyInput b w bits xs) (fun _ => [sign])
def budget (w n : ℕ) := CompetitorPlaneEntry.readyBudget w n+2

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 30 => a.val) h)
theorem native_avoids (i : Fin 29) : native i≠29 := by
  intro h
  have hv := congrArg (fun a : Fin 30 => a.val) h
  change i.val=29 at hv
  omega

theorem run_plane (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ out,ClockJoin.ReadyRun machine (budget w xs.length) (input sign b w bits xs) out ∧
      out 17=newWords sign w bits xs ∧ out 18=countWords b xs ∧ out 19=oldWords w xs ∧
      out 0=frame bits ∧ out 9=List.replicate w true ∧ out 20=List.replicate b true ∧
      out 27=CompareMachine.word xs.length ∧ out 29=[sign] := by
  obtain ⟨produced,ready,h17,h18,h19,h0,h9,h20,h27⟩ := CompetitorPlaneEntry.ready_plane_run sign b w bits xs hb hbits hv
  have focused := CompetitorRationalProducts.bounded_focus native native_injective _ _ _ ready
    (input sign b w bits xs) (by intro j; simp [input,native])
  let node : Fin 3 := if sign then 2 else 1
  let output := install native (input sign b w bits xs) produced
  have selected : ClockJoin.ReadyRun (programs node) (CompetitorPlaneEntry.readyBudget w xs.length)
      (input sign b w bits xs) output := by
    cases sign <;> exact focused
  obtain ⟨child,hchild,hct,hch,hcs⟩ := selected
  let start : Configuration 30 1 := initialConfiguration idle (input sign b w bits xs)
  have hsign : start.scanned 29=sign := by
    simp [start,Configuration.scanned,initialConfiguration,input,Fin.addCases,readTapeBit]
  have hstep := RecoveryCalls.return_step sizes programs 0 next 0 node start (by rfl)
    (by change (if start.scanned 29 then some 2 else some 1)=some node; rw [hsign]; cases sign <;> rfl)
  have hbranch : Timed machine 1 (initialConfiguration machine (input sign b w bits xs))
      (controlConfig (RecoveryCalls.code sizes node) (initialConfiguration (programs node) (input sign b w bits xs))) :=
    Timed.single (by simp [machine,RecoveryCalls.machine,RecoveryCalls.code,initialConfiguration]) hstep
  obtain ⟨time,htime,path⟩ := stop_receipt sizes programs 0 next node
    (CompetitorPlaneEntry.readyBudget w xs.length) _ child hchild (by cases sign <;> rfl)
  have all := hbranch.trans path
  obtain ⟨r,hr,hf,hs⟩ := all.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hcost : 1+time≤budget w xs.length := by unfold budget; omega
  have hmore := runFrom_moreFuel machine _ (budget w xs.length-(1+time)) _ r hr
  rw [Nat.add_sub_of_le hcost] at hmore
  have hout : r.final.tapes=output := by rw [hf]; exact hct
  refine ⟨output,⟨r,hmore,hout,?_,by omega⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hch i
  · exact (install_slot native native_injective _ _ 17).trans h17
  · exact (install_slot native native_injective _ _ 18).trans h18
  · exact (install_slot native native_injective _ _ 19).trans h19
  · exact (install_slot native native_injective _ _ 0).trans h0
  · exact (install_slot native native_injective _ _ 9).trans h9
  · exact (install_slot native native_injective _ _ 20).trans h20
  · exact (install_slot native native_injective _ _ 27).trans h27
  · exact install_other native _ _ 29 native_avoids

end NearCubicWires.RepairOrdinary.CompetitorPlaneSign
