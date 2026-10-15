import Proof.CaseAnalysis.WitnessTraversalRun

/-! Cold ports for the shared traversal. The existing quadratic driver
produces the actual capacity; an executed sweep prepares reusable scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverSlots : Fin 9→Fin 36 := ![0,29,30,31,21,32,33,34,35]
def eraseSlots : Fin 23→Fin 36 :=
  Fin.addCases (m:=21) (n:=2) (motive:=fun _=>Fin 36)
    (Fin.addCases (m:=20) (n:=1) (motive:=fun _=>Fin 36)
      (fun i=>⟨i.val+1,by omega⟩) (fun _=>26)) ![21,22]
def walkSlots (i : Fin 29) : Fin 36 := i.castAdd 7
theorem driver_injective : Function.Injective driverSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide
theorem walk_injective : Function.Injective walkSlots := by
  intro i j h;exact Fin.ext (congrArg (fun q : Fin 36=>q.val) h)

def input (bits : List Bool) (i : Fin 36) := if i.val=0 then frame bits else []
noncomputable def driver := RecoveryFocus.machine driverSlots RecoveryEraseDriver.machine
noncomputable def driven (bits : List Bool) :=
  install driverSlots (input bits) (RecoveryEraseDriver.output3 bits)

theorem driver_ready (bits : List Bool) :
    ReadyRun driver (RecoveryEraseDriver.time bits) (input bits) (driven bits) :=
  (RecoveryEraseDriver.driver_ready bits).focus driverSlots driver_injective (input bits)
    (by intro j;fin_cases j <;> rfl)

theorem driven_core (bits : List Bool) (i : Fin 29) :
    driven bits (walkSlots i)=
      if i.val=0 then frame bits
      else if i.val=21 then List.replicate (RecoveryReusableUnpair.capacity bits) true else [] := by
  by_cases h0:i=0
  · subst i
    exact install_slot driverSlots driver_injective _ _ 0
  by_cases h21:i=21
  · subst i
    change install driverSlots (input bits) (RecoveryEraseDriver.output3 bits) (driverSlots 4)=_
    rw [install_slot driverSlots driver_injective]
    change List.replicate (8192*(bits.length+1)*(bits.length+1)) true=
      List.replicate (8192*(bits.length+1)^2) true
    rw [pow_two,Nat.mul_assoc]
  have hv0:i.val≠0:=by intro h;exact h0 (Fin.ext h)
  have hv21:i.val≠21:=by intro h;exact h21 (Fin.ext h)
  change install driverSlots (input bits) (RecoveryEraseDriver.output3 bits) (walkSlots i)=_
  rw [install_other driverSlots _ _ _ (by
    intro j h
    have hv:(driverSlots j).val=i.val:=congrArg (fun q : Fin 36=>q.val) h
    fin_cases j <;> norm_num [driverSlots] at hv <;> omega)]
  simp only [input,walkSlots,Fin.val_castAdd,hv0,hv21,↓reduceIte]

def eraseOutput (bits : List Bool) : Fin 23→List Bool :=
  Fin.addCases (m:=22) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=21) (n:=1) (motive:=fun _=>List Bool)
      (fun _=>List.replicate (RecoveryReusableUnpair.capacity bits) false)
      (fun _=>List.replicate (RecoveryReusableUnpair.capacity bits) true))
    (fun _=>List.replicate (RecoveryReusableUnpair.capacity bits+1) false)
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 21)
noncomputable def cleared (bits : List Bool) := install eraseSlots (driven bits) (eraseOutput bits)

theorem driven_erase (bits : List Bool) (j : Fin 23) : driven bits (eraseSlots j)=
    (Fin.addCases (motive:=fun _=>List Bool)
      (Fin.addCases (motive:=fun _=>List Bool) (fun _ : Fin 21=>[]) (fun _ : Fin 1=>
        List.replicate (RecoveryReusableUnpair.capacity bits) true)) (fun _ : Fin 1=>[])) j := by
  let k : Fin 29:=⟨(eraseSlots j).val,by fin_cases j <;> decide⟩
  have he:walkSlots k=eraseSlots j:=Fin.ext rfl
  rw [←he,driven_core]
  fin_cases j <;> rfl

theorem erase_ready (bits : List Bool) :
    ReadyRun erase (2*RecoveryReusableUnpair.capacity bits+4) (driven bits) (cleared bits) := by
  have h:=RecoveryScratchErase.erase_ready (RecoveryReusableUnpair.capacity bits) 0
    (fun _ : Fin 21=>[]) (by intro i;exact Nat.zero_le _)
  simp only [Nat.zero_max] at h
  exact h.focus eraseSlots erase_injective (driven bits) (driven_erase bits)

theorem cleared_core (bits : List Bool) (i : Fin 29) :
    cleared bits (walkSlots i)=
      if i.val=0 then frame bits
      else if i.val≤20 ∨ i.val=26 then List.replicate (RecoveryReusableUnpair.capacity bits) false
      else if i.val=21 then List.replicate (RecoveryReusableUnpair.capacity bits) true
      else if i.val=22 then List.replicate (RecoveryReusableUnpair.capacity bits+1) false else [] := by
  by_cases he:∃ j,eraseSlots j=walkSlots i
  · obtain ⟨j,hj⟩:=he
    have hv:(eraseSlots j).val=i.val:=congrArg (fun q : Fin 36=>q.val) hj
    rw [cleared,←hj,install_slot eraseSlots erase_injective,←hv]
    fin_cases j <;> rfl
  · rw [cleared,install_other eraseSlots _ _ _ (by intro j hj;exact he ⟨j,hj⟩),driven_core]
    fin_cases i
    all_goals first | rfl | exact False.elim (he (by decide))

def state (bits : List Bool) : State :=
  ⟨⟨bits,RecoveryReusableUnpair.capacity bits+1,
      fun _=>List.replicate (RecoveryReusableUnpair.capacity bits) false,fun _=>false⟩,
    [false],[],0,RecoveryReusableUnpair.capacity bits⟩

theorem state_valid (bits : List Bool) : (state bits).Valid := by
  refine ⟨?_,rfl,le_refl _,?_⟩
  · intro i;exact List.length_replicate.le
  · change 1≤8192*(bits.length+1)^2
    have h:0<(bits.length+1)^2:=pow_pos (by omega) _
    omega

def boot : Machine 36 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i.val=23 ∨ i.val=24 ∨ i.val=25 then some false else none,
    fun i=>if i.val=26 then .right else .stay⟩ else none
noncomputable def initialized (bits : List Bool) : Configuration 36 2 :=
  ⟨1,fun i=>if i.val=26 then 1 else 0,
    fun i=>if i.val=23 ∨ i.val=24 ∨ i.val=25 then [false] else cleared bits i⟩

theorem initialize_run (bits : List Bool) :
    ∃ r,run boot 1 (cleared bits)=some r ∧ r.final=initialized bits ∧ r.steps=1 := by
  have h:step boot (initialConfiguration boot (cleared bits))=some (initialized bits):=by
    simp only [step,boot,initialConfiguration,Fin.val_zero,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i
      by_cases hi:i.val=23 ∨ i.val=24 ∨ i.val=25
      · have hc:cleared bits i=[]:=by
          rcases hi with h|h|h
          · have he:i=walkSlots 23:=Fin.ext h
            rw [he,cleared_core];rfl
          · have he:i=walkSlots 24:=Fin.ext h
            rw [he,cleared_core];rfl
          · have he:i=walkSlots 25:=Fin.ext h
            rw [he,cleared_core];rfl
        simp only [applyAction,initialized,hi,↓reduceIte,hc]
        rfl
      · simp only [applyAction,initialized,hi,↓reduceIte]
  exact (Timed.single (by rfl) h).run (by rfl)

theorem initialized_tapes (bits : List Bool) (j : Fin 29) :
    (initialized bits).tapes (walkSlots j)=(state bits).tapes j := by
  change (if j.val=23 ∨ j.val=24 ∨ j.val=25 then [false] else cleared bits (walkSlots j))=_
  rw [cleared_core]
  fin_cases j <;> rfl

theorem initialized_heads (bits : List Bool) (j : Fin 29) :
    (initialized bits).heads (walkSlots j)=(state bits).heads j := by
  fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.TraversalCold
