import Proof.PCP.PCPPRequestTaggedBounds

/-! The canonical Boolean-node caller uses the same tagged cons directly at
its retained natural-code fields, including their actual allocated padding. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCons
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_eq (a b : ℕ) (j : Fin 76) :
    PCPPRequestTaggedCons.input a b j=
      if j=2 then frame a.bits else if j=3 then frame b.bits else [] := by
  by_cases hj : j.val<38
  · simp [PCPPRequestTaggedCons.input,hj,PCPPRequestPair.input,PCPPairCanonical.input,Fin.ext_iff]
  · have h2 : j≠2 := by intro he; subst j; contradiction
    have h3 : j≠3 := by intro he; subst j; contradiction
    simp [PCPPRequestTaggedCons.input,hj,h2,h3]

theorem cons_at {u z : ℕ} (slots : Fin 76 → Fin u) (hinj : Function.Injective slots)
    (ambient : Configuration u z) (a b pa pb : ℕ)
    (ht : ∀ j,ambient.tapes (slots j)=
      if j=2 then frame a.bits++List.replicate pa false
      else if j=3 then frame b.bits++List.replicate pb false else [])
    (hh : ∀ j,ambient.heads (slots j)=0) :
    ∃ r,runFrom (RecoveryFocus.machine slots PCPPRequestTaggedCons.machine)
      (PCPPRequestTaggedCons.budget a b)
      (Composition.restart ambient (RecoveryFocus.machine slots PCPPRequestTaggedCons.machine).start)=some r ∧
      r.steps≤PCPPRequestTaggedCons.budget a b ∧ r.final.heads=ambient.heads ∧
      (∃ padding,r.final.tapes (slots 64)=
        frame (Nat.pair 1 (Nat.pair a b)).bits++List.replicate padding false) ∧
      r.final.tapes (slots 74)=(Nat.pair 1 (Nat.pair a b)).bits ∧
      (∀ i,(∀ j,slots j≠i) → r.final.tapes i=ambient.tapes i) := by
  obtain ⟨output,hout,⟨padding,hfield⟩,hraw⟩ := PCPPRequestTaggedCons.cons_run a b
  let caps : Fin 76 → ℕ := fun j => if j=2 then (frame a.bits).length+pa
    else if j=3 then (frame b.bits).length+pb else 0
  have padded := PCPPairReusable.padded_ready _ _ _ hout caps
  have hin (j : Fin 76) : ambient.tapes (slots j)=
      ZeroPadding.pad (caps j) (PCPPRequestTaggedCons.input a b j) := by
    rw [ht,input_eq]
    by_cases h2 : j=2
    · subst j; simp [caps,ZeroPadding.pad]
    by_cases h3 : j=3
    · subst j; simp [caps,ZeroPadding.pad]
    simp [caps,h2,h3,ZeroPadding.pad]
  obtain ⟨r,hr,rh,rt,rs⟩ := padded.focus_at slots hinj ambient.heads ambient.tapes hin hh
  refine ⟨r,hr,rs,rh,?_,?_,?_⟩
  · have h := install_slot slots hinj ambient.tapes (fun j => ZeroPadding.pad (caps j) (output j)) 64
    rw [←rt,hfield] at h
    simp only [caps,show (64 : Fin 76)≠2 by decide,show (64 : Fin 76)≠3 by decide,
      ite_false,ZeroPadding.pad_zero] at h
    exact ⟨padding,h⟩
  · rw [rt]
    have h := install_slot slots hinj ambient.tapes (fun j => ZeroPadding.pad (caps j) (output j)) 74
    rw [hraw] at h
    simpa only [caps,show (74 : Fin 76)≠2 by decide,show (74 : Fin 76)≠3 by decide,
      ite_false,ZeroPadding.pad_zero] using h
  · intro i hi
    rw [rt]
    exact install_other slots _ _ i hi

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCons
