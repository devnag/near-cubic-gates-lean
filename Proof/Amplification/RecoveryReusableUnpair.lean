import Proof.Amplification.RecoveryEraseDriver
import Proof.Amplification.RecoveryScratchErase

/-! The repeated-call boundary for compact decoding. Arbitrary bounded
scratch is physically erased before the actual fixed-width unpair program.
Retained zero backing is charged; it is never identified with blank storage. -/
namespace NearCubicWires.RepairOrdinary.RecoveryReusableUnpair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (bits : List Bool) := RecoveryTapeSupport.capacity bits

def padding (bits : List Bool) (i : Fin 21) := if i.val=0 then 0 else capacity bits

def localInput (bits : List Bool) (i : Fin 21) : List Bool :=
  if i.val=0 then frame bits else List.replicate (capacity bits) false

def localOutput (bits : List Bool) (i : Fin 21) : List Bool :=
  ZeroPadding.pad (padding bits i) (RecoveryFixedUnpair.output3 bits i)

theorem padded_ready (bits : List Bool) : ReadyRun RecoveryFixedUnpair.machine (RecoveryFixedUnpair.time bits)
    (localInput bits) (localOutput bits) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryFixedUnpair.fixed_unpair_ready bits
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config RecoveryFixedUnpair.machine (padding bits) _ _ base hr
  have hin : ZeroPadding.config (padding bits)
      (initialConfiguration RecoveryFixedUnpair.machine (RecoveryFixedUnpair.input bits)) =
      initialConfiguration RecoveryFixedUnpair.machine (localInput bits) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=0 <;>
        simp [ZeroPadding.config,initialConfiguration,RecoveryFixedUnpair.input,localInput,padding,hi,ZeroPadding.pad]
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    funext i
    simp only [ZeroPadding.config,ht,localOutput]
  · intro i
    rw [hf]
    exact hh i

theorem local_support (bits : List Bool) (i : Fin 21) (hi : i.val≠0) :
    (localOutput bits i).length=capacity bits := by
  obtain ⟨r,hr,ht,_,_⟩ := RecoveryFixedUnpair.fixed_unpair_ready bits
  have hmore := run_moreFuel RecoveryFixedUnpair.machine (RecoveryFixedUnpair.time bits)
    (RecoveryFixedUnpair.budget bits-RecoveryFixedUnpair.time bits) _ r hr
  rw [Nat.add_sub_of_le (RecoveryFixedUnpair.time_bound bits)] at hmore
  have hb := RecoveryTapeSupport.fixed_unpair_support bits r hmore i
  rw [ht] at hb
  simp only [localOutput,ZeroPadding.pad_length,padding,hi,↓reduceIte]
  exact max_eq_left hb

def eraseSlots (i : Fin 22) : Fin 23 := i.natAdd 1
def nativeSlots (i : Fin 21) : Fin 23 := i.castAdd 2
theorem eraseSlots_injective : Function.Injective eraseSlots := by
  intro i j h
  have hv := congrArg (fun k : Fin 23 => k.val) h
  apply Fin.ext
  simp only [eraseSlots,Fin.val_natAdd] at hv
  omega
theorem nativeSlots_injective : Function.Injective nativeSlots := by
  intro i j h
  have hv := congrArg (fun k : Fin 23 => k.val) h
  exact Fin.ext hv

def input (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool) : Fin 23 → List Bool :=
  Fin.addCases (m := 1) (n := 22) (motive := fun _ => List Bool) (fun _ => frame bits)
    (Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool) backing (fun _ : Fin 1 => List.replicate (capacity bits) true))
      (fun _ : Fin 1 => List.replicate resetCapacity false))

def erased (bits : List Bool) (resetCapacity : Nat) : Fin 23 → List Bool :=
  Fin.addCases (m := 1) (n := 22) (motive := fun _ => List Bool) (fun _ => frame bits)
    (Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool) (fun _ : Fin 20 => List.replicate (capacity bits) false)
      (fun _ : Fin 1 => List.replicate (capacity bits) true))
      (fun _ : Fin 1 => List.replicate (max resetCapacity (capacity bits+1)) false))

def output (bits : List Bool) (resetCapacity : Nat) : Fin 23 → List Bool :=
  Fin.addCases (m := 21) (n := 2) (motive := fun _ => List Bool) (localOutput bits)
    ![List.replicate (capacity bits) true,List.replicate (max resetCapacity (capacity bits+1)) false]

noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 20)
noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots RecoveryFixedUnpair.machine

theorem erase_ready (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool)
    (hb : ∀ i,(backing i).length≤capacity bits) :
    ReadyRun eraseMachine (2*capacity bits+4) (input bits resetCapacity backing) (erased bits resetCapacity) := by
  have h := (RecoveryScratchErase.erase_ready (capacity bits) resetCapacity backing hb).focus
    eraseSlots eraseSlots_injective (input bits resetCapacity backing)
    (by intro j; simp [input,eraseSlots])
  have he : install eraseSlots (input bits resetCapacity backing)
      (Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool) (fun _ : Fin 20 => List.replicate (capacity bits) false)
        (fun _ : Fin 1 => List.replicate (capacity bits) true))
        (fun _ : Fin 1 => List.replicate (max resetCapacity (capacity bits+1)) false)) = erased bits resetCapacity := by
    funext i
    refine Fin.addCases (m := 1) (n := 22) (motive := fun j : Fin 23 =>
      install eraseSlots (input bits resetCapacity backing) _ j = erased bits resetCapacity j) ?_ ?_ i
    · intro j
      fin_cases j
      rw [install_other eraseSlots _ _ _ (by
        intro k hk
        have hv := congrArg (fun q : Fin 23 => q.val) hk
        simp only [eraseSlots,Fin.val_natAdd,Fin.val_castAdd] at hv
        omega)]
      rfl
    · intro j
      rw [erased,Fin.addCases_right]
      exact install_slot eraseSlots eraseSlots_injective _ _ j
  rw [he] at h
  exact h

theorem native_ready (bits : List Bool) (resetCapacity : Nat) :
    ReadyRun nativeMachine (RecoveryFixedUnpair.time bits) (erased bits resetCapacity) (output bits resetCapacity) := by
  have h := (padded_ready bits).focus nativeSlots nativeSlots_injective (erased bits resetCapacity)
    (by intro j; fin_cases j <;> rfl)
  have he : install nativeSlots (erased bits resetCapacity) (localOutput bits) = output bits resetCapacity := by
    funext i
    refine Fin.addCases (m := 21) (n := 2) (motive := fun j : Fin 23 =>
      install nativeSlots (erased bits resetCapacity) (localOutput bits) j = output bits resetCapacity j) ?_ ?_ i
    · intro j
      rw [output,Fin.addCases_left]
      exact install_slot nativeSlots nativeSlots_injective _ _ j
    · intro j
      rw [install_other nativeSlots _ _ _ (by
        intro k hk
        have hv := congrArg (fun q : Fin 23 => q.val) hk
        simp only [nativeSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      fin_cases j <;> rfl
  rw [he] at h
  exact h

abbrev nativeStates := Fintype.card (RecoveryCalls.Control RecoveryFixedUnpair.sizes)
def sizes : Fin 2 → Nat := ![4,nativeStates]
noncomputable def programs : (j : Fin 2) → Machine 23 (sizes j)
  | ⟨0,_⟩ => eraseMachine
  | ⟨1,_⟩ => nativeMachine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (_ : Fin 23 → Bool) : Option (Fin 2) :=
  if j.val=0 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def time (bits : List Bool) := (2*capacity bits+4+1)+(RecoveryFixedUnpair.time bits+1)
def budget (bits : List Bool) := 32768*(bits.length+1)^2

theorem reusable_ready (bits : List Bool) (resetCapacity : Nat) (backing : Fin 20 → List Bool)
    (hb : ∀ i,(backing i).length≤capacity bits) :
    ReadyRun machine (time bits) (input bits resetCapacity backing) (output bits resetCapacity) := by
  have he := (erase_ready bits resetCapacity backing hb).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hn := (native_ready bits resetCapacity).stop sizes programs 0 next 1 (by intro q; rfl)
  have h := he.trans hn
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs 0) (input bits resetCapacity backing)) =
      initialConfiguration machine (input bits resetCapacity backing) := by rfl
  rw [hin] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i; simp [hf,RecoveryCalls.stopped],hs⟩

theorem time_bound (bits : List Bool) : time bits≤budget bits := by
  have h := RecoveryFixedUnpair.time_bound bits
  unfold time capacity RecoveryTapeSupport.capacity budget RecoveryFixedUnpair.budget at *
  have hp : 0 < (bits.length+1)^2 := by positivity
  omega

theorem output_components (bits : List Bool) (resetCapacity : Nat) :
    output bits resetCapacity 17 = ZeroPadding.pad (capacity bits) (frame (RecoveryFixedUnpair.leftWord bits)) ∧
    output bits resetCapacity 18 = ZeroPadding.pad (capacity bits) (frame (RecoveryFixedUnpair.rightWord bits)) := by
  exact ⟨rfl,rfl⟩

theorem output_support (bits : List Bool) (resetCapacity : Nat) (i : Fin 21) (hi : i.val≠0) :
    (output bits resetCapacity (nativeSlots i)).length=capacity bits := by
  simp only [output,nativeSlots,Fin.addCases_left]
  exact local_support bits i hi

end NearCubicWires.RepairOrdinary.RecoveryReusableUnpair
