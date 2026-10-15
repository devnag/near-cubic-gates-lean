import Proof.Amplification.RecoveryLiteralDecode

/-! Boolean-tag validation reuses two executed binary-predecessor passes.
It scans the whole bounded word, preserves the literal sign on one tape,
and writes tag validity on another. It never treats a nonzero natural tag
as a Boolean without checking that its value is exactly one. -/
namespace NearCubicWires.RepairOrdinary.RecoveryLiteralTag
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open RecoveryListPredecessor
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def predWord (bits : List Bool) := result bits true
def nonzero (bits : List Bool) := decide (value bits≠0)
def tagValid (bits : List Bool) := !nonzero bits || !nonzero (predWord bits)
theorem tagValid_eq (bits : List Bool) : tagValid bits=decide (value bits≤1) := by
  by_cases hz : value bits=0
  · have hn : nonzero bits=false := decide_eq_false (fun h => h hz)
    rw [tagValid,hn]
    simp [hz]
  · have hfirst : nonzero bits=true := decide_eq_true hz
    have hp : value (predWord bits)=value bits-1 := predecessor_value bits hz
    have hsecond : nonzero (predWord bits)=false ↔ value bits≤1 := by
      change decide (value (predWord bits)≠0)=false ↔ value bits≤1
      rw [decide_eq_false_iff_not,not_not,hp]
      omega
    apply Bool.eq_iff_iff.mpr
    rw [tagValid,hfirst]
    simpa only [Bool.not_true,Bool.false_or,Bool.not_eq_true',decide_eq_true_eq] using hsecond

def tapes (bits : List Bool) (sign valid : Bool) (capacity : Nat) : Fin 4→List Bool :=
  ![frame bits,[sign],[valid],List.replicate capacity false]
def firstSlots : Fin 3→Fin 4 := ![0,1,3]
def secondSlots : Fin 3→Fin 4 := ![0,2,3]
noncomputable def firstMachine := RecoveryFocus.machine firstSlots RecoveryListPredecessor.machine
noncomputable def secondMachine := RecoveryFocus.machine secondSlots RecoveryListPredecessor.machine

theorem first_ready (bits : List Bool) (sign valid : Bool) (capacity : Nat) :
    ReadyRun firstMachine (4*bits.length+4) (tapes bits sign valid capacity)
      (tapes (predWord bits) (nonzero bits) valid (max capacity (2*bits.length+1))) := by
  have h := (predecessor_ready bits sign capacity).focus firstSlots (by decide)
    (tapes bits sign valid capacity) (by intro j; fin_cases j <;> rfl)
  have he : install firstSlots (tapes bits sign valid capacity)
      ![frame (result bits true),[decide (value bits≠0)],List.replicate (max capacity (2*bits.length+1)) false]=
      tapes (predWord bits) (nonzero bits) valid (max capacity (2*bits.length+1)) := by
    funext i; fin_cases i
    · exact install_slot firstSlots (by decide) _ _ 0
    · exact install_slot firstSlots (by decide) _ _ 1
    · exact install_other firstSlots _ _ _ (by intro j; fin_cases j <;> decide)
    · exact install_slot firstSlots (by decide) _ _ 2
  rw [he] at h
  exact h

theorem second_ready (bits : List Bool) (sign valid : Bool) (capacity : Nat) :
    ReadyRun secondMachine (4*bits.length+4) (tapes bits sign valid capacity)
      (tapes (predWord bits) sign (nonzero bits) (max capacity (2*bits.length+1))) := by
  have h := (predecessor_ready bits valid capacity).focus secondSlots (by decide)
    (tapes bits sign valid capacity) (by intro j; fin_cases j <;> rfl)
  have he : install secondSlots (tapes bits sign valid capacity)
      ![frame (result bits true),[decide (value bits≠0)],List.replicate (max capacity (2*bits.length+1)) false]=
      tapes (predWord bits) sign (nonzero bits) (max capacity (2*bits.length+1)) := by
    funext i; fin_cases i
    · exact install_slot secondSlots (by decide) _ _ 0
    · exact install_other secondSlots _ _ _ (by intro j; fin_cases j <;> decide)
    · exact install_slot secondSlots (by decide) _ _ 1
    · exact install_slot secondSlots (by decide) _ _ 2
  rw [he] at h
  exact h

def gate : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q scanned => if q.val=0 then
    some ⟨1,fun i => if i=2 then some (!scanned 1 || !scanned 2) else none,fun _ => .stay⟩ else none

theorem gate_ready (bits : List Bool) (sign bad : Bool) (capacity : Nat) :
    ReadyRun gate 1 (tapes bits sign bad capacity) (tapes bits sign (!sign || !bad) capacity) := by
  let final : Configuration 4 2 := ⟨1,fun _ => 0,tapes bits sign (!sign || !bad) capacity⟩
  have hs : step gate (initialConfiguration gate (tapes bits sign bad capacity))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

def sizes : Fin 3→Nat := ![7,7,2]
noncomputable def programs : (j : Fin 3)→Machine 4 (sizes j)
  | ⟨0,_⟩ => firstMachine
  | ⟨1,_⟩ => secondMachine
  | ⟨2,_⟩ => gate
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (_ : Fin 4→Bool) : Option (Fin 3) :=
  ![some 1,some 2,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def time (bits : List Bool) := ((4*bits.length+4+1)+(4*bits.length+4+1))+(1+1)
theorem time_eq (bits : List Bool) : time bits=8*bits.length+12 := by unfold time; omega

theorem tag_ready (bits : List Bool) (sign valid : Bool) (capacity : Nat) :
    ReadyRun machine (time bits) (tapes bits sign valid capacity)
      (tapes (predWord (predWord bits)) (nonzero bits) (decide (value bits≤1))
        (max capacity (2*bits.length+1))) := by
  have hfirst := (first_ready bits sign valid capacity).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hsecond := second_ready (predWord bits) (nonzero bits) valid (max capacity (2*bits.length+1))
  simp only [predWord,result_length,max_self,max_assoc] at hsecond
  have hcall := hsecond.call sizes programs 0 next 1 2 (by intro q; rfl)
  have hgate := (gate_ready (predWord (predWord bits)) (nonzero bits) (nonzero (predWord bits))
    (max capacity (2*bits.length+1))).stop sizes programs 0 next 2 (by intro q; rfl)
  have h := (hfirst.trans hcall).trans hgate
  have hi : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs 0) (tapes bits sign valid capacity))=
      initialConfiguration machine (tapes bits sign valid capacity) := rfl
  rw [hi] at h
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨r,hr,?_,by intro i; simp [hf,RecoveryCalls.stopped],ht⟩
  rw [hf]
  change tapes (predWord (predWord bits)) (nonzero bits) (tagValid bits) _=_
  rw [tagValid_eq]

theorem padded_tag_ready (bits : List Bool) (sign valid : Bool) (capacity padding : Nat) :
    ReadyRun machine (time bits)
      (fun i => ZeroPadding.pad (![padding,0,0,0] i) (tapes bits sign valid capacity i))
      (fun i => ZeroPadding.pad (![padding,0,0,0] i)
        (tapes (predWord (predWord bits)) (nonzero bits) (decide (value bits≤1))
          (max capacity (2*bits.length+1)) i)) :=
  RecoveryChildSelection.ReadyRun.pad (tag_ready bits sign valid capacity) ![padding,0,0,0]

end NearCubicWires.RepairOrdinary.RecoveryLiteralTag
