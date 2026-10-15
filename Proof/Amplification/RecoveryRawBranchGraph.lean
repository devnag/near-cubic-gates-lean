import Proof.Amplification.RecoveryRawBranchSemantics

/-! Actual raw/default control flow. Syntax failure rejects. A certified
invalid Boolean tag takes the accepted-empty default; otherwise the index
bound gates the SAT replay using the same physically produced count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectMachine : Machine 136 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=93 then some false else none,fun _=>.stay⟩ else none

theorem reject_run (heads : Fin 136→Nat) (tapes : Fin 136→List Bool) (old : Bool)
    (hh : heads 93=0) (ht : tapes 93=[old]) :
    ∃ r,runFrom rejectMachine 1 ⟨0,heads,tapes⟩=some r ∧ r.steps=1 ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update tapes 93 [false] := by
  have h : step rejectMachine ⟨0,heads,tapes⟩=
      some (⟨1,heads,Function.update tapes 93 [false]⟩ : Configuration 136 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=93
      · subst i
        change writeTapeBit (tapes 93) (heads 93) false=[false]
        rw [hh,ht]
        rfl
      · simp only [applyAction,if_neg hi,Function.update_of_ne hi]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,hs,by rw [hf],by rw [hf]⟩

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable def sizes : Fin 4→Nat := ![stateCount viewMachine,stateCount evalMachine,2,2]
noncomputable def programs : (j : Fin 4)→Machine 136 (sizes j)
  | ⟨0,_⟩=>viewMachine
  | ⟨1,_⟩=>evalMachine
  | ⟨2,_⟩=>RecoveryBankPair.flagMachine 93 28
  | ⟨3,_⟩=>rejectMachine
  | ⟨n+4,h⟩=>False.elim (by omega)
noncomputable def next (j : Fin 4) (_ : Fin (sizes j)) (bits : Fin 136→Bool) : Option (Fin 4) :=
  ![some (if bits 28 then if bits 33 then if bits 34 then 1 else 3 else 2 else 3),none,none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (width : Nat) := 1073741824*(width+1)^4

theorem tags_bit (x : State) (n : Nat) {s : Nat} (q : Fin s) :
    (cfg x n q).scanned 33=x.view.inner.tags := by
  change readTapeBit [x.view.inner.tags] 0=x.view.inner.tags
  rfl
theorem bounded_bit (x : State) (n : Nat) {s : Nat} (q : Fin s) :
    (cfg x n q).scanned 34=x.view.inner.bounded := by
  change readTapeBit [x.view.inner.bounded] 0=x.view.inner.bounded
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
