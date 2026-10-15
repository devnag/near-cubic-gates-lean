import Proof.Hierarchy.HierarchyBinaryPower
import Proof.MachineModel.OrdinaryFramedIncrement

/-! A fixed-width successor with its reset capacity generated on the actual
input tapes. The caller supplies no free zero workspace. -/
namespace NearCubicWires.RepairOrdinary.HierarchySuccessor
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w a : ℕ) : Fin 6 → List Bool :=
  ![frame (binary w a),List.replicate w true,[],[],[],[]]
def marked (w a : ℕ) : Fin 6 → List Bool :=
  ![frame (binary w a),List.replicate w true,[false],[],[],[]]
def prepared (w a : ℕ) : Fin 6 → List Bool :=
  ![frame (binary w a),List.replicate w true,[false],frame (binary w 0),[true],
    List.replicate (2*w+1) false]
def output (w a : ℕ) : Fin 6 → List Bool :=
  ![frame (binary w (a+1)),List.replicate w true,[false],frame (binary w 0),[true],
    List.replicate (2*w+1) false]
def mark : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==1
  rule := fun s _ => if s.val=0 then some ⟨1,fun i => if i.val=2 then some false else none,
    fun _ => .stay⟩ else none
def normalizeSlots : Fin 5 → Fin 6 := ![1,2,3,4,5]
def incrementSlots : Fin 2 → Fin 6 := ![0,5]
theorem normalize_injective : Function.Injective normalizeSlots := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [normalizeSlots] at h ⊢
theorem increment_injective : Function.Injective incrementSlots := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [incrementSlots] at h ⊢
noncomputable def normalize := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def increment := RecoveryFocus.machine incrementSlots FramedIncrement.machine
noncomputable def machine := Composition.machine (Composition.machine mark normalize) increment

theorem mark_ready (w a : ℕ) : ReadyRun mark 1 (input w a) (marked w a) := by
  let c : Configuration 6 2 := ⟨1,fun _ => 0,marked w a⟩
  have hp : step mark (initialConfiguration mark (input w a))=some c := by
    simp [step,mark,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [input,marked,applyAction,writeTapeBit,c]
  have h := Timed.single (by rfl) hp
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem normalize_ready (w a : ℕ) :
    ReadyRun normalize (4*w+4) (marked w a) (prepared w a) := by
  have h := (HierarchyMultiplyEntry.scalar_zero_ready w).focus normalizeSlots normalize_injective
    (marked w a) (by intro j; fin_cases j <;> rfl)
  have he : install normalizeSlots (marked w a)
      ![List.replicate w true,[false],frame (binary w 0),[true],List.replicate (2*w+1) false]=
      prepared w a := by
    funext i
    fin_cases i
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · exact install_slot _ normalize_injective _ _ 0
    · exact install_slot _ normalize_injective _ _ 1
    · exact install_slot _ normalize_injective _ _ 2
    · exact install_slot _ normalize_injective _ _ 3
    · exact install_slot _ normalize_injective _ _ 4
  rw [he] at h
  exact h

theorem increment_ready (w a : ℕ) (ha : a+1<2^w) :
    ClockJoin.ReadyRun increment (4*w+2) (prepared w a) (output w a) := by
  obtain ⟨r,hr,h0,h1,hh,hs,_⟩ := FramedIncrement.increment_run w a (2*w+1) ha (by omega)
  have hi : (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame (binary w a)) (fun _ : Fin 1 => List.replicate (2*w+1) false))=
      ![frame (binary w a),List.replicate (2*w+1) false] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  have ht : r.final.tapes=![frame (binary w (a+1)),List.replicate (2*w+1) false] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
  have h := (show ClockJoin.ReadyRun FramedIncrement.machine (4*w+2) _ _ from ⟨r,hr,ht,hh,hs⟩).focus
    incrementSlots increment_injective (prepared w a) (by intro j; fin_cases j <;> rfl)
  have he : install incrementSlots (prepared w a)
      ![frame (binary w (a+1)),List.replicate (2*w+1) false]=output w a := by
    funext i
    fin_cases i
    · exact install_slot _ increment_injective _ _ 0
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]; rfl
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]; rfl
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]; rfl
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]; rfl
    · exact install_slot _ increment_injective _ _ 1
  rw [he] at h
  exact h

theorem successor_ready (w a : ℕ) (ha : a+1<2^w) :
    ClockJoin.ReadyRun machine (8*w+9) (input w a) (output w a) := by
  have hp := HierarchyMultiplyEntry.join_exact mark normalize 1 (4*w+4) _ _ _
    (mark_ready w a) (normalize_ready w a)
  obtain ⟨r,hr,ht,hh,hs⟩ := hp
  have h := ClockJoin.join (Composition.machine mark normalize) increment (1+1+(4*w+4)) (4*w+2)
    _ _ _ ⟨r,hr,ht,hh,hs.le⟩ (increment_ready w a ha)
  have he : 1+1+(4*w+4)+1+(4*w+2)=8*w+9 := by omega
  simpa only [machine,he] using h

end NearCubicWires.RepairOrdinary.HierarchySuccessor
