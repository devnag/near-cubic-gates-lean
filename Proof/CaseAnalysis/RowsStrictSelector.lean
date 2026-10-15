import Proof.CaseAnalysis.RowsStrictArithmetic
import Proof.MachineModel.ClockSmallInput

/-! A constant-time physical selector for strict threshold subtraction.
It retains the sign, distinguishes zero/one/larger canonical magnitudes,
and supplies the predecessor flag by an actual write. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsStrictSelector
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def negative (source : List Bool) := readTapeBit source 1
def resultSign (source bits : List Bool) := negative source || bits.isEmpty
def input (source bits : List Bool) : Fin 13 → List Bool :=
  ![frame bits,[],[],[],[],[],[],[],[],[],source,[],[]]
def prepared (source bits : List Bool) (i : Fin 13) : List Bool :=
  if i.val=8 then [false] else if i.val=11 then [false,resultSign source bits]
  else if i.val=12 then [negative source] else input source bits i
def rawInput (source bits : List Bool) : Fin 5 → List Bool :=
  ![source,frame bits,[],[],[]]
def rawPrepared (source bits : List Bool) : Fin 5 → List Bool :=
  ![source,frame bits,[false],[false,resultSign source bits],[negative source]]
def rawBoot : Machine 5 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scanned => if q.val=0 then
      some ⟨1,![none,none,none,some false,none],![.right,.stay,.stay,.right,.stay]⟩
    else if q.val=1 then
      some ⟨2,![none,none,some false,some (scanned 0 || !scanned 1),some (scanned 0)],
        ![.left,.stay,.stay,.left,.stay]⟩
    else none

theorem frame_start (bits : List Bool) : readTapeBit (frame bits) 0 = !bits.isEmpty := by
  cases bits <;> rfl

def bootMiddle (source bits : List Bool) : Configuration 5 3 :=
  ⟨1,![1,0,0,1,0],![source,frame bits,[],[false],[]]⟩
def bootFinal (source bits : List Bool) : Configuration 5 3 :=
  ⟨2,fun _ => 0,rawPrepared source bits⟩

theorem boot_first (source bits : List Bool) :
    step rawBoot (initialConfiguration rawBoot (rawInput source bits))=some (bootMiddle source bits) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

theorem boot_last (source bits : List Bool) :
    step rawBoot (bootMiddle source bits)=some (bootFinal source bits) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [applyAction,bootMiddle,bootFinal,rawPrepared,
      Configuration.scanned,negative,resultSign,frame_start,writeTapeBit]

theorem raw_boot_run (source bits : List Bool) : ∃ r,
    run rawBoot 2 (rawInput source bits)=some r ∧ r.final=bootFinal source bits ∧ r.steps=2 :=
  ((Timed.single (by rfl) (boot_first source bits)).trans
    (Timed.single (by rfl) (boot_last source bits))).run (by rfl)

def bootSlots : Fin 5 → Fin 13 := ![10,0,8,11,12]
theorem boot_injective : Function.Injective bootSlots := by decide
noncomputable def boot := RecoveryFocus.machine bootSlots rawBoot

theorem boot_run (source bits : List Bool) : ∃ r,
    run boot 2 (input source bits)=some r ∧
      r.final=⟨2,fun _ => 0,prepared source bits⟩ ∧ r.steps=2 := by
  obtain ⟨base,hb,bf,bs⟩ := raw_boot_run source bits
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config bootSlots boot_injective rawBoot
    (fun _ => 0) (input source bits) 2 (initialConfiguration rawBoot (rawInput source bits)) base hb
  have hi : RecoveryFocus.config bootSlots (fun _ => 0) (input source bits)
      (initialConfiguration rawBoot (rawInput source bits))=initialConfiguration boot (input source bits) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick bootSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing _ _ _ (by intro i;fin_cases i <;> rfl)
  rw [hi] at hr
  refine ⟨r,hr,?_,hs.trans bs⟩
  rw [hf,bf]
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick bootSlots i <;> simp [RecoveryFocus.config,hp,bootFinal]
  · change install bootSlots (input source bits) (rawPrepared source bits)=prepared source bits
    apply HierarchyAllocation.install_eq _ boot_injective
    · intro i;fin_cases i <;> rfl
    · intro i hi
      have h8 : i.val≠8 := by intro h;exact hi 2 (Fin.ext h.symm)
      have h11 : i.val≠11 := by intro h;exact hi 3 (Fin.ext h.symm)
      have h12 : i.val≠12 := by intro h;exact hi 4 (Fin.ext h.symm)
      simp only [prepared,if_neg h8,if_neg h11,if_neg h12]

def guardSlots : Fin 1 → Fin 13 := fun _ => 0
theorem guard_injective : Function.Injective guardSlots := by intro i j _;exact Subsingleton.elim i j
noncomputable def guard := RecoveryFocus.machine guardSlots ClockSmallInput.machine
noncomputable def machine := Composition.machine boot guard

theorem selector_run (source bits : List Bool) : ∃ r,
    run machine 7 (input source bits)=some r ∧
      r.final=⟨if 2≤bits.length then 9 else 8,fun _ => 0,prepared source bits⟩ ∧ r.steps≤7 := by
  obtain ⟨first,hfirst,ff,fs⟩ := boot_run source bits
  obtain ⟨base,hbase,bf,bs⟩ := ClockSmallInput.guard_run bits
  obtain ⟨last,hl,hf,hs⟩ := RecoveryFocus.run_config guardSlots guard_injective ClockSmallInput.machine
    (fun _ => 0) (prepared source bits) 4 (initialConfiguration ClockSmallInput.machine (fun _ => frame bits)) base hbase
  have hi : RecoveryFocus.config guardSlots (fun _ => 0) (prepared source bits)
      (initialConfiguration ClockSmallInput.machine (fun _ => frame bits))=
      initialConfiguration guard (prepared source bits) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick guardSlots i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing _ _ _ (by intro i;rfl)
  rw [hi] at hl
  have he : last.final=⟨if 2≤bits.length then 6 else 5,fun _ => 0,prepared source bits⟩ := by
    rw [hf,bf]
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick guardSlots i <;> simp [RecoveryFocus.config,hp,ClockSmallInput.cfg]
    · exact install_existing _ _ _ (by intro i;rfl)
  have hre : Composition.restart first.final guard.start=initialConfiguration guard (prepared source bits) := by
    rw [ff]
    rfl
  have hlast : runFrom guard 4 (Composition.restart first.final guard.start)=some last := by rw [hre];exact hl
  have hj := Composition.run_join boot guard 2 4 _ first last hfirst hlast
  refine ⟨_,hj,?_,?_⟩
  · change Composition.rightConfig 3 last.final=_
    rw [he]
    split_ifs <;> rfl
  · change first.steps+1+last.steps≤7
    rw [fs,hs]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsStrictSelector
