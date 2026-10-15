import Proof.Hierarchy.HierarchyBinaryMultiplyLoop

/-! Multiplier initialization from the two framed operands, a paid raw width,
and blank workspace. The accumulator zero and both multiplicand copies are
written by actual machines before entering the factor loop. -/
namespace NearCubicWires.RepairOrdinary.HierarchyMultiplyEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w a : ℕ) (bits : List Bool) : Fin 13 → List Bool :=
  fun i => if i.val=0 then frame bits else if i.val=8 then frame (binary w a)
    else if i.val=9 then List.replicate w true else []
def marked (w a : ℕ) (bits : List Bool) : Fin 13 → List Bool :=
  fun i => if i.val=10 then [false] else input w a bits i
def zeroed (w a : ℕ) (bits : List Bool) : Fin 13 → List Bool :=
  fun i => if i.val=3 then frame (binary w 0) else if i.val=11 then [true]
    else if i.val=12 then List.replicate (2*w+1) false else marked w a bits i
def copied (w a : ℕ) (bits : List Bool) : Fin 13 → List Bool :=
  fun i => if i.val=1 then frame (binary w a) else if i.val=6 then List.replicate (2*w+1) false
    else if i.val=7 then List.replicate (4*w+3) false else zeroed w a bits i
def prepared (w a : ℕ) (bits : List Bool) : Fin 13 → List Bool :=
  fun i => if i.val=2 then frame (binary w a) else copied w a bits i

def markMachine : Machine 13 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i.val=10 then some false else none,fun _ => .stay⟩ else none
def zeroSlots : Fin 5 → Fin 13 := ![9,10,3,11,12]
def copySlots : Fin 4 → Fin 13 := ![8,1,6,7]
def duplicateSlots : Fin 4 → Fin 13 := ![1,2,6,7]
theorem zero_injective : Function.Injective zeroSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
theorem duplicate_injective : Function.Injective duplicateSlots := by decide
noncomputable def zeroProgram := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def duplicateProgram := RecoveryFocus.machine duplicateSlots copyMachine
noncomputable def bootstrap := Composition.machine
  (Composition.machine (Composition.machine markMachine zeroProgram) copyProgram) duplicateProgram

theorem mark_ready (w a : ℕ) (bits : List Bool) :
    ReadyRun markMachine 1 (input w a bits) (marked w a bits) := by
  have h : step markMachine (initialConfiguration markMachine (input w a bits))=
      some (⟨1,fun _ => 0,marked w a bits⟩ : Configuration 13 2) := by
    simp [step,markMachine,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,input,marked,writeTapeBit]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem scalar_zero_ready (w : ℕ) :
    ReadyRun ClockNormalize.machine (4*w+4)
      ![List.replicate w true,[false],[],[],[]]
      ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w [] (by simp)
  have hi : ClockNormalize.input w []=![List.replicate w true,[false],[],[],[]] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs⟩
  funext i; fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem zero_input (w a : ℕ) (bits : List Bool) (j : Fin 5) :
    marked w a bits (zeroSlots j)=![List.replicate w true,[false],[],[],[]] j := by
  fin_cases j <;> rfl

theorem zero_install (w a : ℕ) (bits : List Bool) : install zeroSlots (marked w a bits)
      ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false]=
      zeroed w a bits := by
  funext i; fin_cases i
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_slot zeroSlots zero_injective _ _ 2
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_slot zeroSlots zero_injective _ _ 0
  · exact install_slot zeroSlots zero_injective _ _ 1
  · exact install_slot zeroSlots zero_injective _ _ 3
  · exact install_slot zeroSlots zero_injective _ _ 4
theorem zero_ready (w a : ℕ) (bits : List Bool) :
    ReadyRun zeroProgram (4*w+4) (marked w a bits) (zeroed w a bits) := by
  have h := (scalar_zero_ready w).focus zeroSlots zero_injective (marked w a bits) (zero_input w a bits)
  rw [zero_install] at h
  exact h

theorem copy_input (w a : ℕ) (bits : List Bool) (j : Fin 4) :
    zeroed w a bits (copySlots j)=![frame (binary w a),[],[],[]] j := by
  fin_cases j <;> rfl

theorem copy_install (w a : ℕ) (bits : List Bool) : install copySlots (zeroed w a bits)
      ![frame (binary w a),frame (binary w a),List.replicate (2*w+1) false,
        List.replicate (4*w+3) false]=copied w a bits := by
  funext i; fin_cases i
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_slot copySlots copy_injective _ _ 1
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_slot copySlots copy_injective _ _ 2
  · exact install_slot copySlots copy_injective _ _ 3
  · exact install_slot copySlots copy_injective _ _ 0
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
  · exact install_other copySlots _ _ _ (by decide)
theorem copy_ready (w a : ℕ) (bits : List Bool) :
    ReadyRun copyProgram (8*w+8) (zeroed w a bits) (copied w a bits) := by
  have hb := RecoveryRootRound.copy_ready (binary w a) [] 0 0 (by simp)
  simp only [binary_length,max_eq_right (Nat.zero_le _),List.replicate_zero] at hb
  have h := hb.focus copySlots copy_injective (zeroed w a bits) (copy_input w a bits)
  rw [copy_install] at h
  exact h

theorem duplicate_ready (w a : ℕ) (bits : List Bool) :
    ReadyRun duplicateProgram (8*w+8) (copied w a bits) (prepared w a bits) := by
  have hb := RecoveryRootRound.copy_ready (binary w a) [] (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at hb
  have h := hb.focus duplicateSlots duplicate_injective (copied w a bits) (by intro j; fin_cases j <;> rfl)
  have he : install duplicateSlots (copied w a bits)
      ![frame (binary w a),frame (binary w a),List.replicate (2*w+1) false,
        List.replicate (4*w+3) false]=prepared w a bits := by
    funext i; fin_cases i
    all_goals first
      | exact install_slot duplicateSlots duplicate_injective _ _ 0
      | exact install_slot duplicateSlots duplicate_injective _ _ 1
      | exact install_slot duplicateSlots duplicate_injective _ _ 2
      | exact install_slot duplicateSlots duplicate_injective _ _ 3
      | exact install_other duplicateSlots _ _ _ (by decide)
  rw [he] at h
  exact h

theorem join_exact {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (input middle output : Fin t → List Bool)
    (hp : ReadyRun p fp input middle) (hq : ReadyRun q fq middle output) :
    ReadyRun (Composition.machine p q) (fp+1+fq) input output := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := hp
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := hq
  have he : Composition.restart first.final q.start=initialConfiguration q middle := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  have hl : runFrom q fq (Composition.restart first.final q.start)=some last := by rw [he]; exact hlast
  exact ⟨Composition.joinedReceipt first last,Composition.run_join p q fp fq _ first last hfirst hl,
    hlt,hlh,by simp [Composition.joinedReceipt,hs,hls]⟩

theorem bootstrap_ready (w a : ℕ) (bits : List Bool) :
    ReadyRun bootstrap (20*w+24) (input w a bits) (prepared w a bits) := by
  have h0 := join_exact markMachine zeroProgram 1 (4*w+4) _ _ _
    (mark_ready w a bits) (zero_ready w a bits)
  have h1 := join_exact (Composition.machine markMachine zeroProgram) copyProgram _ (8*w+8) _ _ _
    h0 (copy_ready w a bits)
  have h2 := join_exact (Composition.machine (Composition.machine markMachine zeroProgram) copyProgram)
    duplicateProgram _ (8*w+8) _ _ _ h1 (duplicate_ready w a bits)
  have he : ((1+1+(4*w+4))+1+(8*w+8))+1+(8*w+8)=20*w+24 := by omega
  simpa only [bootstrap,he] using h2

end NearCubicWires.RepairOrdinary.HierarchyMultiplyEntry
