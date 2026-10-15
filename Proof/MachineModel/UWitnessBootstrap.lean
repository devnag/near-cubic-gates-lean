import Proof.MachineModel.UInputOrdinary

/-! From the physical raw width alone, allocate a framed binary zero, a
2w+1-cell reset capacity, and the exact sentinel unary width at head1. -/
namespace NearCubicWires.RepairOrdinary.UWitnessBootstrap
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,
    fun i => if i.val=1 then some false else none,fun _ => .stay⟩ else none
def initial5 (w : ℕ) : Fin 5 → List Bool := ![List.replicate w true,[],[],[],[]]
def output5 (w : ℕ) : Fin 5 → List Bool :=
  ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false]
def zeroMachine := Composition.machine mark ClockNormalize.machine

theorem zero_ready (w : ℕ) : ClockJoin.ReadyRun zeroMachine (4*w+6) (initial5 w) (output5 w) := by
  let c : Configuration 5 2 := ⟨1,fun _ => 0,ClockNormalize.input w []⟩
  have hm : step mark (initialConfiguration mark (initial5 w))=some c := by
    simp [step,mark,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,initial5,c,ClockNormalize.input,frame,writeTapeBit,Fin.addCases]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) hm).run (by rfl)
  have hmark : ClockJoin.ReadyRun mark 1 (initial5 w) (ClockNormalize.input w []) :=
    ⟨r,hr,by rw [hf],by intro i; rw [hf],hs.le⟩
  have hn := ClockBoundGuard.normalize_ready w []
  have ho : ClockBoundGuard.normalizeOutput w []=output5 w := by
    funext i
    fin_cases i <;> simp [ClockBoundGuard.normalizeOutput,output5,frame,
      ClockScalarFields.resize_binary w [] (by simp),RadixSemantics.value]
  rw [ho] at hn
  have h := ClockJoin.join mark ClockNormalize.machine _ _ _ _ _ hmark hn
  have he : 1+1+(4*w+4)=4*w+6 := by omega
  rwa [he] at h

def input (w : ℕ) : Fin 6 → List Bool := ![List.replicate w true,[],[],[],[],[]]
def middle (w : ℕ) : Fin 6 → List Bool :=
  ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false,[]]
def output (w : ℕ) : Fin 6 → List Bool :=
  ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false,
    RepairSource.VerifierDecoding.CompareMachine.word w]
def heads : Fin 6 → ℕ := ![0,0,0,0,0,1]
def zeroSlots (j : Fin 5) : Fin 6 := j.castSucc
theorem zero_injective : Function.Injective zeroSlots := by decide
noncomputable def zeroPhase := RecoveryFocus.machine zeroSlots zeroMachine
def lengthSlots : Fin 2 → Fin 6 := ![2,5]
theorem length_injective : Function.Injective lengthSlots := by decide
noncomputable def lengthPhase := RecoveryFocus.machine lengthSlots RepairSource.VerifierDecoding.LengthMachine.machine
noncomputable def machine := Composition.machine zeroPhase lengthPhase

theorem zero_phase (w : ℕ) : ClockJoin.ReadyRun zeroPhase (4*w+6) (input w) (middle w) := by
  have h := (zero_ready w).focus zeroSlots zero_injective (input w)
    (by intro j; fin_cases j <;> rfl)
  have ho : install zeroSlots (input w) (output5 w)=middle w := by
    apply HierarchyWidth.install_eq _ zero_injective
    · intro j; fin_cases j <;> rfl
    · intro i hi
      simp only [Fin.forall_fin_succ] at hi
      fin_cases i <;> simp_all [zeroSlots,middle,input]
  rw [ho] at h
  exact h

theorem length_run (w : ℕ) :
    ∃ r,run lengthPhase (4*w+3) (middle w)=some r ∧
      r.final.tapes=output w ∧ r.final.heads=heads ∧ r.steps=4*w+3 := by
  obtain ⟨base,hb,hf,hs,_⟩ := RepairSource.VerifierDecoding.LengthMachine.length_run (binary w 0)
  simp only [binary_length] at hb hf hs
  obtain ⟨r,hr,hrt,hrs⟩ := RecoveryFocus.run_config lengthSlots length_injective
    RepairSource.VerifierDecoding.LengthMachine.machine (fun _ => 0) (middle w) (4*w+3) _ base hb
  have hi : RecoveryFocus.config lengthSlots (fun _ => 0) (middle w)
      (initialConfiguration RepairSource.VerifierDecoding.LengthMachine.machine
        ![frame (binary w 0),[]])=initialConfiguration lengthPhase (middle w) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick lengthSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing lengthSlots _ _ (by intro j; fin_cases j <;> rfl)
  change runFrom (RecoveryFocus.machine lengthSlots RepairSource.VerifierDecoding.LengthMachine.machine)
    (4*w+3) (RecoveryFocus.config lengthSlots (fun _ => 0) (middle w)
      (initialConfiguration RepairSource.VerifierDecoding.LengthMachine.machine ![frame (binary w 0),[]]))=some r at hr
  rw [hi] at hr
  have hp (i : Fin 6) : RecoveryFocus.pick lengthSlots i=
      (![none,none,some 0,none,none,some 1] : Fin 6 → Option (Fin 2)) i := by
    have other (i : Fin 6) (hi : ∀ j,lengthSlots j≠i) : RecoveryFocus.pick lengthSlots i=none := by
      have hn : ¬∃ j,lengthSlots j=i := by simpa using hi
      simp [RecoveryFocus.pick,hn]
    fin_cases i
    · exact other _ (by intro j; fin_cases j <;> decide)
    · exact other _ (by intro j; fin_cases j <;> decide)
    · exact RecoveryFocus.pick_slot _ length_injective 0
    · exact other _ (by intro j; fin_cases j <;> decide)
    · exact other _ (by intro j; fin_cases j <;> decide)
    · exact RecoveryFocus.pick_slot _ length_injective 1
  refine ⟨r,hr,?_,?_,hrs.trans hs⟩
  · funext i
    fin_cases i <;> simp [hrt,RecoveryFocus.config,hp,hf,RepairSource.VerifierDecoding.LengthMachine.cfg,output,middle]
    rfl
  · funext i
    fin_cases i <;> simp [hrt,RecoveryFocus.config,hp,hf,RepairSource.VerifierDecoding.LengthMachine.cfg,heads]

theorem bootstrap_run (w : ℕ) :
    ∃ r,run machine (8*w+10) (input w)=some r ∧
      r.final.tapes=output w ∧ r.final.heads=heads ∧ r.steps ≤ 8*w+10 := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := zero_phase w
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := length_run w
  have he : Composition.restart first.final lengthPhase.start=initialConfiguration lengthPhase (middle w) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  unfold run at hlast
  rw [←he] at hlast
  have h := Composition.run_join zeroPhase lengthPhase (4*w+6) (4*w+3) _ first last hfirst hlast
  have htime : (4*w+6)+1+(4*w+3)=8*w+10 := by omega
  rw [htime] at h
  refine ⟨Composition.joinedReceipt first last,h,hlt,hlh,?_⟩
  dsimp only [Composition.joinedReceipt]
  omega

end NearCubicWires.RepairOrdinary.UWitnessBootstrap
