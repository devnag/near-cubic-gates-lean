import Proof.MachineModel.OrdinarySourceSATLiftLayoutFull

/-! Paid request movement. Outer and unary extraction use the streaming
copier, while two framed field calls advance the parser cursor honestly. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open private install_first from Proof.MachineModel.OrdinaryOracleComposeHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_copy {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (heads : Fin t → ℕ) (ambient : Fin t → List Bool) (bits : List Bool)
    (hh : ∀ i,heads (slot i)=0) (hin : ambient (slot 0)=frame bits)
    (hout : ambient (slot 1)=[]) (hlog : ambient (slot 2)=[]) :
    ∃ r,runFrom (RecoveryFocus.machine slot Streaming.machine) (4*bits.length+2)
      ⟨Streaming.machine.start,heads,ambient⟩=some r ∧ r.final.heads=heads ∧
      r.final.tapes=Function.update (Function.update ambient (slot 1) bits)
        (slot 2) (List.replicate bits.length false) ∧ r.steps ≤ 4*bits.length+2 := by
  have hbase := CanonicalPositiveOutput.copy_padded bits 0
  obtain ⟨r,hr,rh,rt,rs⟩ := hbase.focus_at slot hi heads ambient (by
    intro i
    fin_cases i <;> simpa using (by assumption)) hh
  have he : ![frame bits++List.replicate 0 false,bits,List.replicate bits.length false]=
      ![ambient (slot 0),bits,List.replicate bits.length false] := by simp [hin]
  rw [he,install_first slot hi] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem field_advance {t : ℕ} (slot : Fin 3 → Fin t) (hi : Function.Injective slot)
    (heads : Fin t → ℕ) (ambient : Fin t → List Bool) (pre bits suffix : List Bool) (logCap : ℕ)
    (hhead : heads (slot 0)=pre.length) (houthead : heads (slot 1)=0) (hloghead : heads (slot 2)=0)
    (hin : ambient (slot 0)=pre++frame bits++suffix) (hout : ambient (slot 1)=[])
    (hlog : ambient (slot 2)=List.replicate logCap false) :
    ∃ r,runFrom (RecoveryFocus.machine slot PCPFieldMoves.advanceMachine) (4*bits.length+4)
      ⟨PCPFieldMoves.advanceMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=Function.update heads (slot 0) (pre.length+2*bits.length+1) ∧
      r.final.tapes=Function.update (Function.update ambient (slot 1) (frame bits))
        (slot 2) (List.replicate (max logCap (2*bits.length+1)) false) ∧ r.steps=4*bits.length+4 := by
  classical
  obtain ⟨base,hbase,hbt,hbh,hbs⟩ := PCPFieldMoves.advance_run pre bits suffix 0 logCap
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config slot hi PCPFieldMoves.advanceMachine
    heads ambient _ _ base hbase
  have entryHeads : (PCPFieldMoves.entry pre bits suffix 0 logCap).heads=![pre.length,0,0] := by
    funext j
    fin_cases j <;> rfl
  have entryTapes : (PCPFieldMoves.entry pre bits suffix 0 logCap).tapes=
      ![pre++frame bits++suffix,[],List.replicate logCap false] := by
    funext j
    fin_cases j
    · change ZeroPadding.pad 0 (pre++frame bits++suffix)=_
      simp
    · change ZeroPadding.pad 0 ([] : List Bool)=_
      simp
    · change ZeroPadding.pad logCap ([] : List Bool)=_
      simp [ZeroPadding.pad]
  have hinit : RecoveryFocus.config slot heads ambient (PCPFieldMoves.entry pre bits suffix 0 logCap)=
      (⟨PCPFieldMoves.advanceMachine.start,heads,ambient⟩ : Configuration t 5) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        subst i
        simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slot hi,entryHeads]
        fin_cases j <;> simp [hhead,houthead,hloghead]
    · apply install_existing
      intro j
      rw [entryTapes]
      fin_cases j
      · simpa [List.append_assoc] using hin
      · exact hout
      · exact hlog
  rw [hinit] at hr
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none =>
      have hne : i≠slot 0 := by
        intro he
        subst i
        rw [RecoveryFocus.pick_slot slot hi] at hp
        contradiction
      simp [RecoveryFocus.config,hp,Function.update,hne]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slot hi,hbh]
      have h10 : slot 1≠slot 0 := fun h => (by decide : (1 : Fin 3)≠0) (hi h)
      have h20 : slot 2≠slot 0 := fun h => (by decide : (2 : Fin 3)≠0) (hi h)
      fin_cases j <;> simp [Function.update,h10,h20,houthead,hloghead]
  · rw [hf]
    change install slot ambient base.final.tapes=_
    rw [hbt]
    have he : PCPFieldMoves.output pre bits suffix 0 logCap=
        ![ambient (slot 0),frame bits,List.replicate (max logCap (2*bits.length+1)) false] := by
      funext j
      fin_cases j <;> simp [PCPFieldMoves.output,hin]
    rw [he,install_first slot hi]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
