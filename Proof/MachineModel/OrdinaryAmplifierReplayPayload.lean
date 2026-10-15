import Proof.MachineModel.OrdinaryAmplifierReplayPrepare

/-! One fixed cold physical amplifier-schema framer. Its only live datum is
the complete raw payload; every unary driver is constructed internally. -/
namespace NearCubicWires.RepairOrdinary.AmplifierReplay.Payload
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 3→Fin 28 := ![0,26,27]
def framer := RecoveryFocus.machine slots Frame.machine
def machine := Composition.machine Prepare.machine framer
def budget (n : ℕ) (table : List Bool) := Prepare.budget n+1+(2*(frame n.bits++table).length+1)

theorem payload_run (n : ℕ) (table : List Bool) (hlen : table.length=2^n) :
    ∃ r,run machine (budget n table) (Prepare.input (frame n.bits++table))=some r ∧
      r.final.tapes 27=frame (frame n.bits++table) ∧ r.steps ≤ budget n table := by
  obtain ⟨base,hb,h0,hh0,h26,hh26,h27,hh27,hsteps⟩ := Prepare.prepare_run n table
  obtain ⟨localRun,hl,hout,hs⟩ := Frame.frame_run n.bits table
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes
      (Frame.cfg 0 (frame n.bits++table) 0 [] table.length 0)=
      Composition.restart base.final framer.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · exact hh0
      · exact hh26
      · exact hh27
    · intro i; fin_cases i
      · exact h0
      · change base.final.tapes 26=UnaryTemplate.tape table.length
        rw [hlen]
        exact h26
      · exact h27
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) Frame.machine
    base.final.heads base.final.tapes _ _ localRun hl
  rw [hi] at hf
  have hj := Composition.run_join Prepare.machine framer _ _ _ base focused hb hf
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_⟩
  · change focused.final.tapes (slots 2)=_
    rw [hff]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)] using hout
  · change base.steps+1+focused.steps ≤ _
    rw [hfs,hs]
    unfold budget
    omega

/-- A focused actual cold run preserves every physical slot outside its bank. -/
theorem focused_run {t : ℕ} (slot : Fin 28→Fin t) (hinj : Function.Injective slot)
    (heads : Fin t→ℕ) (tapes : Fin t→List Bool) (n : ℕ) (table : List Bool)
    (hlen : table.length=2^n) (hh : ∀ i,heads (slot i)=0)
    (ht : ∀ i,tapes (slot i)=Prepare.input (frame n.bits++table) i) :
    ∃ r,runFrom (RecoveryFocus.machine slot machine) (budget n table)
      ⟨machine.start,heads,tapes⟩=some r ∧
      r.final.tapes (slot 27)=frame (frame n.bits++table) ∧ r.steps ≤ budget n table := by
  obtain ⟨base,hb,hout,hs⟩ := payload_run n table hlen
  obtain ⟨r,hr,hf,hn⟩ := RecoveryFocus.run_config slot hinj machine heads tapes _ _ base hb
  have hi : RecoveryFocus.config slot heads tapes
      (initialConfiguration machine (Prepare.input (frame n.bits++table)))=
      (⟨machine.start,heads,tapes⟩ : Configuration t _) := by
    exact WilliamsSourceCrop.focus_same slot
      (⟨machine.start,heads,tapes⟩ : Configuration t _)
      (initialConfiguration machine (Prepare.input (frame n.bits++table))) hh ht
  rw [hi] at hr
  refine ⟨r,hr,?_,by rw [hn]; exact hs⟩
  rw [hf]
  simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slot hinj] using hout

end
end NearCubicWires.RepairOrdinary.AmplifierReplay.Payload
