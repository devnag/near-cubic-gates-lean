import Proof.Amplification.RecoveryHeaderCap

/-! Physically count and copy the complete finite witness. Canonical witness
length is polynomial; accepted-run soundness does not assume a witness-size
promise. The actual produced unary length drives the framed copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdWitnessCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 4 := ![0,2]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def countMachine := RecoveryFocus.machine slots LengthMachine.machine

def input (bits : List Bool) : Fin 4→List Bool := ![frame bits,[],[],[]]
def counted (bits : List Bool) : Fin 4→List Bool := ![frame bits,[],CompareMachine.word bits.length,[]]
def countHeads : Fin 4→Nat := ![0,0,1,0]
def output (bits : List Bool) : Fin 4→List Bool :=
  ![frame bits,frame bits,CompareMachine.word bits.length,List.replicate (2*bits.length+3) false]

theorem pick_eq (i : Fin 4) : RecoveryFocus.pick slots i=![some 0,none,some 1,none] i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots slots_injective 0
  · have hn : ¬∃ j,slots j=(1 : Fin 4) := by decide
    simp [RecoveryFocus.pick,hn]
  · exact RecoveryFocus.pick_slot slots slots_injective 1
  · have hn : ¬∃ j,slots j=(3 : Fin 4) := by decide
    simp [RecoveryFocus.pick,hn]

theorem count_run (bits : List Bool) :
    ∃ r,run countMachine (4*bits.length+3) (input bits)=some r ∧
      r.final.heads=countHeads ∧ r.final.tapes=counted bits ∧ r.steps=4*bits.length+3 := by
  obtain ⟨b,hb,hf,hs,_⟩ := LengthMachine.length_run bits
  obtain ⟨r,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config slots slots_injective LengthMachine.machine
    (fun _=>0) (input bits) (4*bits.length+3) _ b hb
  have hi : RecoveryFocus.config slots (fun _=>0) (input bits)
      (initialConfiguration LengthMachine.machine ![frame bits,[]])=
      initialConfiguration countMachine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,initialConfiguration]
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,pick_eq,initialConfiguration,input]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hsteps.trans hs⟩
  · rw [hfinal,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,LengthMachine.cfg,countHeads]
  · rw [hfinal,hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick_eq,LengthMachine.cfg,counted,input,CompareMachine.word]

def positionMachine : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun _=>none,![.stay,.stay,.left,.stay]⟩ else none

theorem position_run (bits : List Bool) :
    ∃ r,runFrom positionMachine 1 ⟨0,countHeads,counted bits⟩=some r ∧
      r.final.heads=(fun _=>0) ∧ r.final.tapes=counted bits ∧ r.steps=1 := by
  have h : step positionMachine ⟨0,countHeads,counted bits⟩=
      some (⟨1,fun _=>0,counted bits⟩ : Configuration 4 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

noncomputable def frontMachine := Composition.machine countMachine positionMachine

theorem front_ready (bits : List Bool) : ReadyRun frontMachine (4*bits.length+5) (input bits) (counted bits) := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := count_run bits
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := position_run bits
  have hi : Composition.restart first.final positionMachine.start=
      (⟨0,countHeads,counted bits⟩ : Configuration 4 2) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hi] at hlast
  have h := Composition.run_join countMachine positionMachine (4*bits.length+3) 1 _ first last hfirst hlast
  rw [show 4*bits.length+3+1+1=4*bits.length+5 by omega] at h
  refine ⟨Composition.joinedReceipt first last,h,hlt,?_,?_⟩
  · intro i
    exact congrFun hlh i
  · simp only [Composition.joinedReceipt,hfs,hls]

noncomputable def machine := Composition.machine frontMachine RecoveryColdPaddedCopy.machine

theorem copy_ready (bits : List Bool) : ReadyRun machine (8*bits.length+14) (input bits) (output bits) := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := front_ready bits
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := RecoveryColdPaddedCopy.copy_ready bits bits.length
  have hi : Composition.restart first.final RecoveryColdPaddedCopy.machine.start=
      initialConfiguration RecoveryColdPaddedCopy.machine (counted bits) := by
    apply configuration_ext
    · rfl
    · exact funext hfh
    · exact hft
  unfold run at hlast
  unfold counted at hi
  rw [←hi] at hlast
  have h := Composition.run_join frontMachine RecoveryColdPaddedCopy.machine
    (4*bits.length+5) (4*bits.length+8) _ first last hfirst hlast
  rw [show 4*bits.length+5+1+(4*bits.length+8)=8*bits.length+14 by omega] at h
  have he : RecoveryColdPaddedCopy.data bits bits.length=bits := by
    simpa using RecoveryColdPaddedCopy.data_eq_pad bits bits.length (Nat.le_refl _)
  rw [he] at hlt
  refine ⟨Composition.joinedReceipt first last,h,hlt,hlh,?_⟩
  simp only [Composition.joinedReceipt,hfs,hls]
  omega

end NearCubicWires.RepairOrdinary.RecoveryColdWitnessCopy
