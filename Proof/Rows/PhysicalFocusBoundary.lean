import Proof.MachineModel.Runs

/-! A concrete focused-run adapter. Every selected local head/word must match
the global boundary, and every unselected global tape is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace FixedLivePackets.PhysicalFocusBoundary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def dock {t u : Nat} {α : Type} (slots : Fin t → Fin u)
    (ambient : Fin u → α) (localData : Fin t → α) (i : Fin u) : α :=
  match RecoveryFocus.pick slots i with | some j => localData j | none => ambient i

theorem dock_eq {t u : Nat} {α : Type} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (ambient target : Fin u → α) (localData : Fin t → α)
    (hs : ∀ j, localData j=target (slots j))
    (ho : ∀ i, (∀ j, slots j≠i) → ambient i=target i) :
    dock slots ambient localData=target := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none =>
    simp only [dock,hp]
    apply ho i
    intro j hj
    subst i
    rw [RecoveryFocus.pick_slot slots hi j] at hp
    contradiction
  | some j =>
    simp only [dock,hp]
    exact (hs j).trans (congrArg target (RecoveryFocus.slot_of_pick slots hp))

theorem focus {t u s fuel : Nat} {p : Machine t s}
    {h0 h1 : Fin t → Nat} {a0 a1 : Fin t → List Bool}
    (run : Step p fuel h0 a0 h1 a1) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H0 H1 : Fin u → Nat) (A0 A1 : Fin u → List Bool)
    (hin : ∀ j,h0 j=H0 (slots j)) (ain : ∀ j,a0 j=A0 (slots j))
    (hout : ∀ j,h1 j=H1 (slots j)) (aout : ∀ j,a1 j=A1 (slots j))
    (outside : ∀ i,(∀ j,slots j≠i) → H0 i=H1 i ∧ A0 i=A1 i) :
    Step (RecoveryFocus.machine slots p) fuel H0 A0 H1 A1 := by
  obtain ⟨r,hr,hh,ht,hs⟩ := run
  obtain ⟨actual,ha,hf,hsteps⟩ := RecoveryFocus.run_config slots hi p H0 A0 fuel
    ⟨p.start,h0,a0⟩ r hr
  have hhi : dock slots H0 h0=H0 := dock_eq slots hi H0 H0 h0 hin (by intros; rfl)
  have hai : dock slots A0 a0=A0 := dock_eq slots hi A0 A0 a0 ain (by intros; rfl)
  have hho : dock slots H0 h1=H1 := dock_eq slots hi H0 H1 h1 hout (by intro i h; exact (outside i h).1)
  have hao : dock slots A0 a1=A1 := dock_eq slots hi A0 A1 a1 aout (by intro i h; exact (outside i h).2)
  have entry : RecoveryFocus.config slots H0 A0 (⟨p.start,h0,a0⟩ : Configuration t s)=
      ⟨(RecoveryFocus.machine slots p).start,H0,A0⟩ := by
    apply configuration_ext
    · rfl
    · exact hhi
    · exact hai
  rw [entry] at ha
  refine ⟨actual,ha,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    change dock slots H0 r.final.heads=H1
    rwa [hh]
  · rw [hf]
    change dock slots A0 r.final.tapes=A1
    rwa [ht]

theorem seq {t sp sq np nq : Nat} {p : Machine t sp} {q : Machine t sq}
    {h0 h1 h2 : Fin t → Nat} {a0 a1 a2 : Fin t → List Bool}
    (hp : Step p np h0 a0 h1 a1) (hq : Step q nq h1 a1 h2 a2) :
    Step (Composition.machine p q) (np+1+nq) h0 a0 h2 a2 := by
  obtain ⟨r,hr,hrh,hrt,hrs⟩ := hp
  obtain ⟨s,hs,hsh,hst,hss⟩ := hq
  have restart : Composition.restart r.final q.start=(⟨q.start,h1,a1⟩ : Configuration t sq) := by
    apply configuration_ext
    · rfl
    · exact hrh
    · exact hrt
  rw [← restart] at hs
  have joined := Composition.run_join p q np nq _ r s hr hs
  exact ⟨Composition.joinedReceipt r s,joined,hsh,hst,by
    change r.steps+1+s.steps≤np+1+nq
    omega⟩

end FixedLivePackets.PhysicalFocusBoundary
