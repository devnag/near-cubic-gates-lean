import Proof.Amplification.RecoveryViewCopies

/-! Sequential cold-bank copies preserve the retained certificate cursor.
The physical composition transition is included in every joined budget. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def AtRun {t s : Nat} (p : Machine t s) (n : Nat) (heads : Fin t→Nat)
    (input output : Fin t→List Bool) : Prop :=
  ∃ r,runFrom p n ⟨p.start,heads,input⟩=some r ∧
    r.final.heads=heads ∧ r.final.tapes=output ∧ r.steps=n

theorem AtRun.focus {t u s n : Nat} {p : Machine t s}
    {input output : Fin t→List Bool} (h : ReadyRun p n input output)
    (slot : Fin t→Fin u) (hi : Function.Injective slot)
    (heads : Fin u→Nat) (ambient : Fin u→List Bool)
    (hin : ∀ j,ambient (slot j)=input j) (hh : ∀ j,heads (slot j)=0) :
    AtRun (RecoveryFocus.machine slot p) n heads ambient (install slot ambient output) :=
  h.focus_at slot hi heads ambient hin hh

theorem AtRun.seq {t s v n m : Nat} {p : Machine t s} {q : Machine t v}
    {heads : Fin t→Nat} {input middle output : Fin t→List Bool}
    (h : AtRun p n heads input middle) (k : AtRun q m heads middle output) :
    AtRun (Composition.machine p q) (n+1+m) heads input output := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := h
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := k
  have hi : Composition.restart first.final q.start=
      (⟨q.start,heads,middle⟩ : Configuration t v) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hi] at hlast
  have h := Composition.run_join p q n m _ first last hfirst hlast
  refine ⟨Composition.joinedReceipt first last,h,hlh,hlt,?_⟩
  change first.steps+1+last.steps=n+1+m
  rw [hfs,hls]

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem install_outputs {t u : Nat} (slots : Fin t→Fin u) (hi : Function.Injective slots)
    (a b : Fin t) (hab : a≠b) (ambient : Fin u→List Bool) (replacement : Fin t→List Bool)
    (hr : ∀ j,j≠a → j≠b → replacement j=ambient (slots j)) :
    install slots ambient replacement=
      Function.update (Function.update ambient (slots a) (replacement a)) (slots b) (replacement b) := by
  classical
  apply install_eq slots hi
  · intro j
    by_cases hja : j=a
    · subst j
      simp [Function.update,hi.eq_iff,hab]
    · by_cases hjb : j=b
      · subst j
        simp [Function.update]
      · simp [Function.update,hi.eq_iff,hja,hjb,hr j hja hjb]
  · intro i hout
    simp only [Function.update_of_ne (Ne.symm (hout b)),Function.update_of_ne (Ne.symm (hout a))]

end NearCubicWires.RepairOrdinary.RecoveryColdView
