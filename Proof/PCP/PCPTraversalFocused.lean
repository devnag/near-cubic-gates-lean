import Proof.PCP.PCPTripleNative

/-! The existing cold serializer consumes physical fields/count inside an
ambient caller, preserving every unselected tape and head. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focused_run {u : ℕ} (slot : Fin 128 → Fin u) (hinj : Function.Injective slot)
    (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (h : Fin u → ℕ) (t : Fin u → List Bool)
    (hh : ∀ j,h (slot j)=heads pre.length j)
    (ht : ∀ j,t (slot j)=input (pre++FieldList.stream fields++suffix) fields.length j) :
    ∃ r,runFrom (RecoveryFocus.machine slot machine) (budget (mass fields))
      ⟨machine.start,h,t⟩=some r ∧
      r.final.tapes (slot 77)=ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (code fields).bits) ∧
      r.final.tapes (slot 78)=(code fields).bits ∧
      r.final.tapes (slot 0)=pre++FieldList.stream fields++suffix ∧
      r.final.tapes (slot 2)=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      (∀ j,r.final.heads (slot j)=coldHeads (pre.length+(FieldList.stream fields).length) j) ∧
      (∀ i,(∀ j,slot j≠i) → r.final.tapes i=t i ∧ r.final.heads i=h i) ∧
      r.steps ≤ budget (mass fields) := by
  obtain ⟨base,hb,b77,b78,b0,b2,bh,_bw,bs⟩ := cold_run pre fields suffix
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slot hinj machine h t _ _ base hb
  have he : RecoveryFocus.config slot h t
      (entry (pre++FieldList.stream fields++suffix) pre.length fields.length)=
      (⟨machine.start,h,t⟩ : Configuration u _) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp only [RecoveryFocus.config,hp]
      | some j =>
        have hij := RecoveryFocus.slot_of_pick slot hp
        simpa only [RecoveryFocus.config,hp,entry] using
          (hh j).symm.trans (congrArg h hij)
    · exact RecoveryRootRound.install_existing slot t _ ht
  rw [he] at hr
  have st (j : Fin 128) : r.final.tapes (slot j)=base.final.tapes j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hinj]
  have sh (j : Fin 128) : r.final.heads (slot j)=base.final.heads j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hinj]
  refine ⟨r,hr,(st 77).trans b77,(st 78).trans b78,(st 0).trans b0,(st 2).trans b2,?_,?_,?_⟩
  · intro j
    rw [sh,bh]
  · intro i hi
    have hp : RecoveryFocus.pick slot i=none := by
      classical
      simp [RecoveryFocus.pick,show ¬∃ j,slot j=i by simpa using hi]
    simp only [rf,RecoveryFocus.config,hp]
    exact ⟨True.intro,True.intro⟩
  · omega

end NearCubicWires.RepairOrdinary.PCPTraversal
