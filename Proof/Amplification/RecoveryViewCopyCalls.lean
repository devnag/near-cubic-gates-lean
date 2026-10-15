import Proof.Amplification.RecoveryViewAssembly

/-! Literal copy-call interfaces for the cold raw-view bank. Each call
changes its destination and shared reset log, preserving the stream head. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_at {t : Nat} (slot : Fin 4→Fin t) (hi : Function.Injective slot)
    (heads : Fin t→Nat) (ambient : Fin t→List Bool) (bits : List Bool) (width reset : Nat)
    (hw : bits.length=width)
    (hin : ∀ j,ambient (slot j)=![frame bits,[],CompareMachine.word width,List.replicate reset false] j)
    (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot RecoveryColdPaddedCopy.machine) (4*width+8) heads ambient
      (Function.update (Function.update ambient (slot 1) (frame bits)) (slot 3)
        (List.replicate (max reset (2*width+3)) false)) := by
  have hd : RecoveryColdPaddedCopy.data bits width=bits := by
    rw [RecoveryColdPaddedCopy.data_eq_pad bits width hw.le,hw,Nat.sub_self]
    exact List.append_nil bits
  have h := AtRun.focus (padded_ready bits width reset) slot hi heads ambient hin hh
  rw [hd] at h
  rw [RecoveryColdHeader.install_pair slot hi ambient
    ![frame bits,frame bits,CompareMachine.word width,List.replicate (max reset (2*width+3)) false]
    (hin 0).symm (hin 2).symm] at h
  exact h

theorem double_at {t : Nat} (slot : Fin 3→Fin t) (hi : Function.Injective slot)
    (heads : Fin t→Nat) (ambient : Fin t→List Bool) (n reset : Nat)
    (hin : ∀ j,ambient (slot j)=![CompareMachine.word n,[],List.replicate reset false] j)
    (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot doubleMachine) (4*n+6) heads ambient
      (Function.update (Function.update ambient (slot 1) (CompareMachine.word (2*n))) (slot 2)
        (List.replicate (max reset (2*n+2)) false)) := by
  have h := AtRun.focus (double_ready n reset) slot hi heads ambient hin hh
  rw [install_outputs slot hi 1 2 (by decide) _ _ (by
    intro j h1 h2
    fin_cases j
    · exact (hin 0).symm
    · exact False.elim (h1 rfl)
    · exact False.elim (h2 rfl))] at h
  exact h

theorem unary_at {t : Nat} (slot : Fin 3→Fin t) (hi : Function.Injective slot)
    (heads : Fin t→Nat) (ambient : Fin t→List Bool) (n reset : Nat)
    (hin : ∀ j,ambient (slot j)=![CompareMachine.word n,[],List.replicate reset false] j)
    (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot unaryMachine) (2*n+6) heads ambient
      (Function.update (Function.update ambient (slot 1) (CompareMachine.word n)) (slot 2)
        (List.replicate (max reset (n+2)) false)) := by
  have h := AtRun.focus (unary_ready n reset) slot hi heads ambient hin hh
  rw [install_outputs slot hi 1 2 (by decide) _ _ (by
    intro j h1 h2
    fin_cases j
    · exact (hin 0).symm
    · exact False.elim (h1 rfl)
    · exact False.elim (h2 rfl))] at h
  exact h

theorem erase_at {t : Nat} (slot : Fin 4→Fin t) (hi : Function.Injective slot)
    (heads : Fin t→Nat) (ambient : Fin t→List Bool) (n reset : Nat)
    (hin : ∀ j,ambient (slot j)=![List.replicate n true,[],[],List.replicate reset false] j)
    (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot ClockUnarySum.machine) (2*n+6) heads ambient
      (Function.update (Function.update ambient (slot 2) (List.replicate n true)) (slot 3)
        (List.replicate (max reset (n+2)) false)) := by
  have h := AtRun.focus (erase_copy_ready n reset) slot hi heads ambient hin hh
  rw [install_outputs slot hi 2 3 (by decide) _ _ (by
    intro j h2 h3
    fin_cases j
    · exact (hin 0).symm
    · exact (hin 1).symm
    · exact False.elim (h2 rfl)
    · exact False.elim (h3 rfl))] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryColdView
