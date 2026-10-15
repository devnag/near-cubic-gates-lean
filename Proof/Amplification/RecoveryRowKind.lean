import Proof.Amplification.RecoveryRowFieldsSemantics

namespace NearCubicWires.RepairOrdinary.RecoveryRowKind
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open RecoveryLiteralTag
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (bits : List Bool) (flags : Fin 3→Bool) (capacity : Nat) : Fin 5→List Bool :=
  ![frame bits,[flags 0],[flags 1],[flags 2],List.replicate capacity false]
def predSlots (i : Fin 3) : Fin 3→Fin 5 := ![0,⟨i.val+1,by omega⟩,4]
theorem predSlots_injective (i : Fin 3) : Function.Injective (predSlots i) := by fin_cases i <;> decide
noncomputable def predMachine (i : Fin 3) := RecoveryFocus.machine (predSlots i) RecoveryListPredecessor.machine

theorem pred_ready (bits : List Bool) (flags : Fin 3→Bool) (capacity : Nat) (i : Fin 3) :
    ReadyRun (predMachine i) (4*bits.length+4) (tapes bits flags capacity)
      (tapes (predWord bits) (Function.update flags i (nonzero bits)) (max capacity (2*bits.length+1))) := by
  have h := (RecoveryListPredecessor.predecessor_ready bits (flags i) capacity).focus
    (predSlots i) (predSlots_injective i) (tapes bits flags capacity) (by
      intro j; fin_cases i <;> fin_cases j <;> rfl)
  have he : install (predSlots i) (tapes bits flags capacity)
      ![frame (predWord bits),[nonzero bits],List.replicate (max capacity (2*bits.length+1)) false]=
      tapes (predWord bits) (Function.update flags i (nonzero bits)) (max capacity (2*bits.length+1)) := by
    funext k
    by_cases hk : ∃ j,predSlots i j=k
    · obtain ⟨j,rfl⟩ := hk
      rw [install_slot (predSlots i) (predSlots_injective i)]
      fin_cases i <;> fin_cases j <;> simp [tapes,predSlots]
    · rw [install_other (predSlots i) _ _ _ (by intro j hj; exact hk ⟨j,hj⟩)]
      have h0 : predSlots i 0≠k := by intro h0; exact hk ⟨0,h0⟩
      have h1 : predSlots i 1≠k := by intro h1; exact hk ⟨1,h1⟩
      have h2 : predSlots i 2≠k := by intro h2; exact hk ⟨2,h2⟩
      fin_cases i <;> fin_cases k <;> first
        | exact False.elim (h0 rfl)
        | exact False.elim (h1 rfl)
        | exact False.elim (h2 rfl)
        | simp [tapes]
  rw [←he]
  exact h

def selected (a b c : Bool) : Fin 3→Bool := ![!a,a && !b,a && b && !c]
def flagsFor (bits : List Bool) : Fin 3→Bool :=
  selected (nonzero bits) (nonzero (predWord bits)) (nonzero (predWord (predWord bits)))

theorem flagsFor_eq (bits : List Bool) (i : Fin 3) :
    flagsFor bits i=decide (value bits=i.val) := by
  have h0 : nonzero bits=false ↔ value bits=0 := by simp [nonzero]
  by_cases hz : value bits=0
  · have hn := h0.mpr hz
    fin_cases i <;> simp [flagsFor,selected,hn,hz]
  · have hp := RecoveryListPredecessor.predecessor_value bits hz
    change value (predWord bits)=value bits-1 at hp
    have hn : nonzero bits=true := by simp [nonzero,hz]
    by_cases ho : value bits=1
    · have hp0 : nonzero (predWord bits)=false := by simp [nonzero,hp,ho]
      fin_cases i <;> simp [flagsFor,selected,hn,hp0,ho]
    · have hpz : value (predWord bits)≠0 := by omega
      have hp2 := RecoveryListPredecessor.predecessor_value (predWord bits) hpz
      change value (predWord (predWord bits))=value (predWord bits)-1 at hp2
      have hpn : nonzero (predWord bits)=true := by simp [nonzero,hpz]
      fin_cases i
      · simp [flagsFor,selected,hn,hz]
      · simp [flagsFor,selected,hn,hpn,ho]
      · change (nonzero bits && nonzero (predWord bits) && !nonzero (predWord (predWord bits)))=decide (value bits=2)
        rw [hn,hpn]
        apply Bool.eq_iff_iff.mpr
        simp [nonzero,hp2,hp]
        omega

def gate : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    ![none,some (!(scanned 1)),some (scanned 1 && !(scanned 2)),
      some (scanned 1 && scanned 2 && !(scanned 3)),none],fun _=>.stay⟩ else none

theorem gate_ready (bits : List Bool) (flags : Fin 3→Bool) (capacity : Nat) :
    ReadyRun gate 1 (tapes bits flags capacity)
      (tapes bits (selected (flags 0) (flags 1) (flags 2)) capacity) := by
  let final : Configuration 5 2 := ⟨1,fun _=>0,tapes bits (selected (flags 0) (flags 1) (flags 2)) capacity⟩
  have hs : step gate (initialConfiguration gate (tapes bits flags capacity))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

def sizes : Fin 4→Nat := ![7,7,7,2]
noncomputable def programs : (j : Fin 4)→Machine 5 (sizes j)
  | ⟨0,_⟩=>predMachine 0
  | ⟨1,_⟩=>predMachine 1
  | ⟨2,_⟩=>predMachine 2
  | ⟨3,_⟩=>gate
  | ⟨n+4,h⟩=>False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 5→Bool) : Option (Fin 4) :=
  ![some 1,some 2,some 3,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def after (bits : List Bool) := predWord (predWord (predWord bits))
def time (bits : List Bool) := ((4*bits.length+4+1)+(4*bits.length+4+1))+(4*bits.length+4+1)+(1+1)

theorem kind_ready (bits : List Bool) (flags : Fin 3→Bool) (capacity : Nat) :
    ReadyRun machine (time bits) (tapes bits flags capacity)
      (tapes (after bits) (fun i=>decide (value bits=i.val)) (max capacity (2*bits.length+1))) := by
  let f0 := Function.update flags 0 (nonzero bits)
  let f1 := Function.update f0 1 (nonzero (predWord bits))
  let f2 := Function.update f1 2 (nonzero (predWord (predWord bits)))
  let cap := max capacity (2*bits.length+1)
  have h0 := (pred_ready bits flags capacity 0).call sizes programs 0 next 0 1 (by intro q; rfl)
  have p1 := pred_ready (predWord bits) f0 cap 1
  simp only [predWord,RecoveryListPredecessor.result_length,cap,max_self,max_assoc] at p1
  have h1 := p1.call sizes programs 0 next 1 2 (by intro q; rfl)
  have p2 := pred_ready (predWord (predWord bits)) f1 cap 2
  simp only [predWord,RecoveryListPredecessor.result_length,cap,max_self,max_assoc] at p2
  have h2 := p2.call sizes programs 0 next 2 3 (by intro q; rfl)
  have h3 := (gate_ready (after bits) f2 cap).stop sizes programs 0 next 3 (by intro q; rfl)
  have h := ((h0.trans h1).trans h2).trans h3
  obtain ⟨r,hr,hf,ht⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨r,hr,?_,by intro i; simp [hf,RecoveryCalls.stopped],ht⟩
  rw [hf]
  change tapes (after bits) (selected (f2 0) (f2 1) (f2 2)) cap=_
  have he : selected (f2 0) (f2 1) (f2 2)=fun i=>decide (value bits=i.val) := by
    funext i
    simpa only [flagsFor,f2,f1,f0,Function.update_self,Function.update_of_ne (by decide : (0 : Fin 3)≠2),
      Function.update_of_ne (by decide : (1 : Fin 3)≠2),Function.update_of_ne (by decide : (0 : Fin 3)≠1)]
      using flagsFor_eq bits i
  rw [he]

end NearCubicWires.RepairOrdinary.RecoveryRowKind
