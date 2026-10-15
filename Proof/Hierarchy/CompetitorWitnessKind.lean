import Proof.Hierarchy.CompetitorWitnessKindRows
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessKind
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics RecoveryLiteralTag
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
def gate : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    ![none,none,none,none,none,some (scanned 1 || (!(scanned 2) && !(scanned 3) && !(scanned 5)))],fun _=>.stay⟩ else none

theorem gate_generic (bits : List Bool) (fs : Fin 4 → Bool) (cap : ℕ) : ReadyRun gate 1
    (tapes bits fs cap) (tapes bits (Function.update fs 3 (choose fs)) cap) := by
  let final : Configuration 6 2 := ⟨1,fun _=>0,tapes bits (Function.update fs 3 (choose fs)) cap⟩
  have h : step gate (initialConfiguration gate (tapes bits fs cap))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs⟩

theorem gate_ready (bits : List Bool) : ReadyRun gate 1
    (tapes (after bits) (predFlags bits) (2*bits.length+1))
    (tapes (after bits) (flags bits) (2*bits.length+1)) := by
  have h := gate_generic (after bits) (predFlags bits) (2*bits.length+1)
  have he : Function.update (predFlags bits) 3 (choose (predFlags bits))=flags bits := by
    funext i;fin_cases i
    · rfl
    · rfl
    · rfl
    · exact choose_eq bits
  rw [he] at h
  exact h

def sizes : Fin 4 → ℕ := ![2,Fintype.card (RecoveryCalls.Control RecoveryRowKind.sizes),7,2]
noncomputable def programs : (j : Fin 4) → Machine 6 (sizes j)
  | ⟨0,_⟩=>initMachine
  | ⟨1,_⟩=>row
  | ⟨2,_⟩=>predecessor
  | ⟨3,_⟩=>gate
  | ⟨n+4,h⟩=>False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 6 → Bool) : Option (Fin 4) := ![some 1,some 2,some 3,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem kind_ready (bits : List Bool) : ReadyRun machine (16*bits.length+27) (input bits)
    (tapes (after bits) (flags bits) (2*bits.length+1)) := by
  have h0 := (initMachine_ready bits).call sizes programs 0 next 0 1 (by intro q;rfl)
  have h1 := (row_ready bits).call sizes programs 0 next 1 2 (by intro q;rfl)
  have h2 := (predecessor_ready bits).call sizes programs 0 next 2 3 (by intro q;rfl)
  have h3 := (gate_ready bits).stop sizes programs 0 next 3 (by intro q;rfl)
  have h := ((h0.trans h1).trans h2).trans h3
  have he : ((1+1+(RecoveryRowKind.time bits+1))+(4*bits.length+4+1))+(1+1)=16*bits.length+27 := by
    unfold RecoveryRowKind.time
    omega
  rw [he] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i;simp [hf,RecoveryCalls.stopped],hs⟩

end NearCubicWires.RepairOrdinary.CompetitorWitnessKind
