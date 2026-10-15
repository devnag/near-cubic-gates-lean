import Proof.PCP.VerifierDecodingField
import Proof.Amplification.RecoveryReadyCalls

/-! The same-bucket grouping scan extracts a fixed number of framed payload
bits directly from the sorted source. Its physical width driver is retained;
only the source cursor advances. Padding and old target bytes are explicit. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 6) (source : List Bool) (pos width cap : ℕ) (backing : List Bool) :
    Configuration 3 6 :=
  ⟨q,![pos,0,1],![source,ZeroPadding.pad cap backing,CompareMachine.word width]⟩

theorem padded_run (pre bits suffix backing : List Bool) (cap : ℕ)
    (hb : backing.length ≤ 2*bits.length+1) :
    ∃ r,runFrom FieldMachine.machine (4*bits.length+2)
      (cfg 0 (pre++Streaming.marks bits++suffix) pre.length bits.length cap backing)=some r ∧
      r.final=cfg 4 (pre++Streaming.marks bits++suffix) (pre.length+2*bits.length)
        bits.length cap (frame bits) ∧ r.steps=4*bits.length+2 := by
  obtain ⟨base,hr,hf,hs,_⟩ := FieldMachine.field_run pre bits suffix backing hb
  let caps : Fin 3 → ℕ := ![0,cap,0]
  obtain ⟨r,ha,hfinal,hsteps,_⟩ := ZeroPadding.run_config FieldMachine.machine caps _ _ base hr
  have hi : ZeroPadding.config caps
      (FieldMachine.scan 0 (pre++Streaming.marks bits++suffix) pre.length bits.length 0 [] backing)=
      cfg 0 (pre++Streaming.marks bits++suffix) pre.length bits.length cap backing := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,caps,FieldMachine.scan,cfg,StablePartition.Workspace.overlay]
  rw [hi] at ha
  refine ⟨r,ha,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,FieldMachine.finished,cfg]

def slots {t : ℕ} (source target driver : Fin t) : Fin 3 → Fin t := ![source,target,driver]
noncomputable def program {t : ℕ} (source target driver : Fin t) :=
  RecoveryFocus.machine (slots source target driver) FieldMachine.machine

theorem focused_heads {t : ℕ} (source target driver : Fin t)
    (hi : Function.Injective (slots source target driver)) (q : Fin 6)
    (word backing : List Bool) (pos width cap : ℕ) (heads : Fin t → ℕ)
    (ambient : Fin t → List Bool) (ht : heads target=0) (hd : heads driver=1) :
    (RecoveryFocus.config (slots source target driver) heads ambient
      (cfg q word pos width cap backing)).heads=Function.update heads source pos := by
  have hts : target≠source := fun h => (by decide : (1 : Fin 3)≠0) (hi h)
  have hds : driver≠source := fun h => (by decide : (2 : Fin 3)≠0) (hi h)
  funext i
  cases hp : RecoveryFocus.pick (slots source target driver) i with
  | none =>
    have hn : i≠source := by
      intro h
      subst i
      have hp' : RecoveryFocus.pick (slots source target driver) source=some 0 :=
        RecoveryFocus.pick_slot _ hi 0
      rw [hp'] at hp
      contradiction
    simp [RecoveryFocus.config,hp,Function.update_of_ne hn]
  | some j =>
    have he := RecoveryFocus.slot_of_pick (slots source target driver) hp
    subst i
    simp only [RecoveryFocus.config,hp]
    fin_cases j
    · simp [slots,cfg]
    · change 0=Function.update heads source pos target
      rw [Function.update_of_ne hts]
      exact ht.symm
    · change 1=Function.update heads source pos driver
      rw [Function.update_of_ne hds]
      exact hd.symm

theorem field_run {t : ℕ} (source target driver : Fin t)
    (hi : Function.Injective (slots source target driver))
    (pre bits suffix backing : List Bool) (cap : ℕ) (heads : Fin t → ℕ)
    (ambient : Fin t → List Bool) (hb : backing.length ≤ 2*bits.length+1)
    (hs : heads source=pre.length) (ht : heads target=0) (hd : heads driver=1)
    (hsource : ambient source=pre++Streaming.marks bits++suffix)
    (htarget : ambient target=ZeroPadding.pad cap backing)
    (hdriver : ambient driver=CompareMachine.word bits.length) :
    ∃ r,runFrom (program source target driver) (4*bits.length+2)
      (RecoveryCalls.restarted (program source target driver) heads ambient)=some r ∧
      r.final.heads=Function.update heads source (pre.length+2*bits.length) ∧
      r.final.tapes=Function.update ambient target (ZeroPadding.pad cap (frame bits)) ∧
      r.steps=4*bits.length+2 := by
  obtain ⟨base,hbase,hbf,hbs⟩ := padded_run pre bits suffix backing cap hb
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config (slots source target driver) hi
    FieldMachine.machine heads ambient _ _ base hbase
  have hin : RecoveryFocus.config (slots source target driver) heads ambient
      (cfg 0 (pre++Streaming.marks bits++suffix) pre.length bits.length cap backing)=
      RecoveryCalls.restarted (program source target driver) heads ambient := by
    apply configuration_ext
    · rfl
    · rw [focused_heads source target driver hi _ _ _ _ _ _ _ _ ht hd]
      change Function.update heads source pre.length=heads
      rw [←hs,Function.update_eq_self]
    · apply install_existing
      intro j
      fin_cases j
      · exact hsource
      · exact htarget
      · exact hdriver
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hbs⟩
  · rw [hf,hbf]
    exact focused_heads source target driver hi _ _ _ _ _ _ _ _ ht hd
  · rw [hf,hbf]
    let localTapes := (cfg 4 (pre++Streaming.marks bits++suffix)
      (pre.length+2*bits.length) bits.length cap (frame bits)).tapes
    change install (slots source target driver) ambient localTapes=
      Function.update ambient target (ZeroPadding.pad cap (frame bits))
    funext i
    by_cases hit : i=target
    · subst i
      rw [Function.update_self]
      exact install_slot _ hi _ _ 1
    · rw [Function.update_of_ne hit]
      cases hp : RecoveryFocus.pick (slots source target driver) i with
      | none => simp [install,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick (slots source target driver) hp
        have hj : localTapes j=ambient (slots source target driver j) := by
          fin_cases j
          · exact hsource.symm
          · exact False.elim (hit he.symm)
          · exact hdriver.symm
        simp only [install,hp]
        exact hj.trans (congrArg ambient he)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupFields
