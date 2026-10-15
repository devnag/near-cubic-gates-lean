import Proof.Hierarchy.CompetitorPlanePacketLoad

/-! The complete packet loader docks into the actual reusable plane tapes.
Its source32 remains streaming. Packet buffers29/0/18 and scratch1 are
physically cleared with retained driver30/reset31 before every packet. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 34 → ℕ := fun i => if i=32 then pos else 0
def cfg {s : ℕ} (q : Fin s) (pos : ℕ) (ambient : Fin 34 → List Bool) : Configuration 34 s := ⟨q,heads pos,ambient⟩
def targets : Fin 4 → Fin 34 := ![29,0,18,1]
def eraseSlots : Fin 6 → Fin 34 := ![29,0,18,1,30,31]
def loadSlots : Fin 6 → Fin 34 := ![32,29,0,18,33,1]
def eraseInput (D : ℕ) (backing : Fin 4 → List Bool) := CompetitorPlaneWorkspace.eraseInput D backing
noncomputable def clearProgram := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 4)
noncomputable def loadProgram := RecoveryFocus.machine loadSlots CompetitorPlanePacketLoad.machine
noncomputable def machine := Composition.machine clearProgram loadProgram
noncomputable def cleared (D : ℕ) (ambient : Fin 34 → List Bool) :=
  install eraseSlots ambient (eraseInput D (fun _ : Fin 4 => List.replicate D false))
def budget (D : ℕ) (bits counts : List Bool) := 2*D+5+CompetitorPlanePacketLoad.budget bits counts

theorem clear_run (D pos : ℕ) (ambient : Fin 34 → List Bool)
    (hd : ambient 30=List.replicate D true) (hr : ambient 31=List.replicate (D+1) false)
    (hb : ∀ j,(ambient (targets j)).length≤D) :
    ∃ r,runFrom clearProgram (2*D+4) (cfg clearProgram.start pos ambient)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=cleared D ambient ∧ r.steps=2*D+4 := by
  have child : ReadyRun (RecoveryScratchErase.resetMachine 4) (2*D+4)
      (eraseInput D (fun j => ambient (targets j))) (eraseInput D (fun _ => List.replicate D false)) := by
    simpa only [eraseInput,CompetitorPlaneWorkspace.eraseInput,max_self] using
      RecoveryScratchErase.erase_ready D (D+1) (fun j => ambient (targets j)) hb
  have hh : ∀ j,heads pos (eraseSlots j)=0 := by intro j; fin_cases j <;> simp [heads,eraseSlots]
  have ht : ∀ j,ambient (eraseSlots j)=eraseInput D (fun a => ambient (targets a)) j := by
    intro j
    fin_cases j
    all_goals first | exact hd | exact hr | rfl
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := HierarchyBinary.focused_run eraseSlots (by decide)
    _ _ _ child (heads pos) ambient hh ht
  exact ⟨r,hrun,hheads,htapes,hsteps⟩

theorem clear_target (D : ℕ) (ambient : Fin 34 → List Bool) (j : Fin 4) :
    cleared D ambient (targets j)=List.replicate D false := by
  have he := install_slot eraseSlots (by decide) ambient
    (eraseInput D (fun _ : Fin 4 => List.replicate D false)) (j.castAdd 2)
  fin_cases j <;> exact he

theorem clear_keep (D : ℕ) (ambient : Fin 34 → List Bool)
    (hd : ambient 30=List.replicate D true) (hr : ambient 31=List.replicate (D+1) false)
    (i : Fin 34) (h0 : i≠0) (h1 : i≠1) (h18 : i≠18) (h29 : i≠29) :
    cleared D ambient i=ambient i := by
  by_cases h30 : i=30
  · subst i
    exact (install_slot eraseSlots (by decide) _ _ 4).trans hd.symm
  · by_cases h31 : i=31
    · subst i
      exact (install_slot eraseSlots (by decide) _ _ 5).trans hr.symm
    · apply install_other
      intro j hj
      fin_cases j
      all_goals first | exact h29 hj.symm | exact h0 hj.symm | exact h18 hj.symm | exact h1 hj.symm | exact h30 hj.symm | exact h31 hj.symm

theorem load_heads (old pos : ℕ) (ambient : Fin 34 → List Bool) {s : ℕ} (part : Configuration 6 s)
    (hh : part.heads=CompetitorPlanePacketFields.heads pos) :
    (RecoveryFocus.config loadSlots (heads old) ambient part).heads=heads pos := by
  funext i
  by_cases hz : i=32
  · subst i
    have hp : RecoveryFocus.pick loadSlots 32=some 0 := RecoveryFocus.pick_slot loadSlots (by decide) 0
    simp [RecoveryFocus.config,hp,hh,CompetitorPlanePacketFields.heads,heads]
  · cases hj : RecoveryFocus.pick loadSlots i with
    | none => simp [RecoveryFocus.config,hj,heads,hz]
    | some j =>
      have he := RecoveryFocus.slot_of_pick loadSlots hj
      have hne : j≠0 := by intro h; subst j; exact hz he.symm
      simp [RecoveryFocus.config,hj,hh,CompetitorPlanePacketFields.heads,hne,heads,hz]

theorem dock_run (pre suffix bits counts : List Bool) (sign : Bool) (D : ℕ)
    (ambient : Fin 34 → List Bool)
    (hsource : ambient 32=pre++CompetitorPlanePacketLoad.packet sign bits counts++suffix)
    (hcount : ambient 33=List.replicate counts.length true)
    (hd : ambient 30=List.replicate D true) (hr : ambient 31=List.replicate (D+1) false)
    (hwork : ∀ j,(ambient (targets j)).length≤D)
    (hb : 2*bits.length+1≤D) (hc : counts.length≤D) :
    ∃ r,runFrom machine (budget D bits counts) (cfg machine.start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+(CompetitorPlanePacketLoad.packet sign bits counts).length) ∧
      r.final.tapes 29=ZeroPadding.pad D [sign] ∧ r.final.tapes 0=ZeroPadding.pad D (frame bits) ∧
      r.final.tapes 18=ZeroPadding.pad D counts ∧ r.final.tapes 1=List.replicate D false ∧
      (∀ i,i≠0 → i≠1 → i≠18 → i≠29 → r.final.tapes i=ambient i) ∧
      r.steps=budget D bits counts := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run D pre.length ambient hd hr hwork
  obtain ⟨base,hbase,hbh,hbt,hbs⟩ := CompetitorPlanePacketLoad.packet_run pre suffix bits counts sign D hb hc
  let source := pre++CompetitorPlanePacketLoad.packet sign bits counts++suffix
  let startTapes := CompetitorPlanePacketFields.contents source (List.replicate D false)
    (List.replicate D false) (List.replicate D false) D counts.length
  have hlocal : ∀ j,cleared D ambient (loadSlots j)=startTapes j := by
    intro j
    fin_cases j
    · exact (clear_keep D ambient hd hr 32 (by decide) (by decide) (by decide) (by decide)).trans hsource
    · exact clear_target D ambient 0
    · exact clear_target D ambient 1
    · exact clear_target D ambient 2
    · exact (clear_keep D ambient hd hr 33 (by decide) (by decide) (by decide) (by decide)).trans hcount
    · exact clear_target D ambient 3
  obtain ⟨second,hsecond,hsf,hss⟩ := RecoveryFocus.run_config loadSlots (by decide)
    CompetitorPlanePacketLoad.machine (heads pre.length) (cleared D ambient) _ _ base hbase
  have hin : RecoveryFocus.config loadSlots (heads pre.length) (cleared D ambient)
      (CompetitorPlanePacketFields.cfg CompetitorPlanePacketLoad.machine.start pre.length startTapes)=
      Composition.restart first.final loadProgram.start := by
    apply configuration_ext
    · rfl
    · rw [load_heads _ _ _ _ rfl]
      exact hfh.symm
    · change install loadSlots (cleared D ambient) startTapes=first.final.tapes
      rw [hft]
      exact install_existing loadSlots (cleared D ambient) startTapes hlocal
  rw [hin] at hsecond
  have joined := Composition.run_join clearProgram loadProgram _ _ _ first second hfirst hsecond
  have htime : (2*D+4)+1+CompetitorPlanePacketLoad.budget bits counts=budget D bits counts := by unfold budget; omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt first second,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact joined
  · change second.final.heads=_
    rw [hsf]
    exact load_heads _ _ _ _ hbh
  · change second.final.tapes 29=_
    rw [hsf]
    change install loadSlots (cleared D ambient) base.final.tapes 29=_
    rw [hbt]
    exact install_slot loadSlots (by decide) _ _ 1
  · change second.final.tapes 0=_
    rw [hsf]
    change install loadSlots (cleared D ambient) base.final.tapes 0=_
    rw [hbt]
    exact install_slot loadSlots (by decide) _ _ 2
  · change second.final.tapes 18=_
    rw [hsf]
    change install loadSlots (cleared D ambient) base.final.tapes 18=_
    rw [hbt]
    exact install_slot loadSlots (by decide) _ _ 3
  · change second.final.tapes 1=_
    rw [hsf]
    change install loadSlots (cleared D ambient) base.final.tapes 1=_
    rw [hbt]
    exact install_slot loadSlots (by decide) _ _ 5
  · intro i h0 h1 h18 h29
    change second.final.tapes i=_
    rw [hsf]
    change install loadSlots (cleared D ambient) base.final.tapes i=_
    rw [hbt]
    by_cases h32 : i=32
    · subst i
      exact (install_slot loadSlots (by decide) _ _ 0).trans hsource.symm
    · by_cases h33 : i=33
      · subst i
        exact (install_slot loadSlots (by decide) _ _ 4).trans hcount.symm
      · have he : install loadSlots (cleared D ambient)
            (CompetitorPlanePacketFields.contents source (ZeroPadding.pad D [sign])
              (ZeroPadding.pad D (frame bits)) (ZeroPadding.pad D counts) D counts.length) i=cleared D ambient i := by
          apply install_other
          intro j hj
          fin_cases j
          all_goals first | exact h32 hj.symm | exact h29 hj.symm | exact h0 hj.symm | exact h18 hj.symm | exact h33 hj.symm | exact h1 hj.symm
        exact he.trans (clear_keep D ambient hd hr i h0 h1 h18 h29)
  · change first.steps+1+second.steps=_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketDock
