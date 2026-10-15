import Proof.Hierarchy.CompetitorPlanePacketRawLoad

/-! The physical framed factor and raw count fields of one P3 packet are
loaded in order, retaining the packet cursor between the two calls. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 6 → ℕ := fun i => if i=0 then pos else 0
def cfg {s : ℕ} (q : Fin s) (pos : ℕ) (tapes : Fin 6 → List Bool) : Configuration 6 s := ⟨q,heads pos,tapes⟩
def contents (source sign factor counts : List Bool) (D n : ℕ) : Fin 6 → List Bool :=
  ![source,sign,factor,counts,List.replicate n true,List.replicate D false]
def factorSlots : Fin 3 → Fin 6 := ![0,2,5]
def countSlots : Fin 4 → Fin 6 := ![0,4,3,5]
noncomputable def factorProgram := RecoveryFocus.machine factorSlots FrameLoad.machine
noncomputable def countProgram := RecoveryFocus.machine countSlots CompetitorPlanePacketRawLoad.machine
noncomputable def machine := Composition.machine factorProgram countProgram

theorem focus_heads {k s : ℕ} (slots : Fin (k+1) → Fin 6) (hi : Function.Injective slots)
    (h0 : slots 0=0) (old pos : ℕ) (ambient : Fin 6 → List Bool) (part : Configuration (k+1) s)
    (hp : ∀ j,part.heads j=if j=0 then pos else 0) :
    (RecoveryFocus.config slots (heads old) ambient part).heads=heads pos := by
  funext i
  by_cases hz : i=0
  · subst i
    have hpick := RecoveryFocus.pick_slot slots hi 0
    rw [h0] at hpick
    simp [RecoveryFocus.config,hpick,hp,heads]
  · cases hj : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config,hj,heads,hz]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hj
      have hne : j≠0 := by intro h; subst j; rw [h0] at he; exact hz he.symm
      simp [RecoveryFocus.config,hj,hp,hne,heads,hz]

theorem factor_run (pre bits suffix sign counts : List Bool) (D n : ℕ) (hc : 2*bits.length+1≤D) :
    ∃ r,runFrom factorProgram (4*bits.length+3)
      (cfg factorProgram.start pre.length (contents (pre++frame bits++suffix) sign (List.replicate D false) counts D n))=some r ∧
      r.final=cfg 3 (pre.length+2*bits.length+1)
        (contents (pre++frame bits++suffix) sign (ZeroPadding.pad D (frame bits)) counts D n) ∧
      r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := padded_load_run pre bits suffix D hc
  let ambient := contents (pre++frame bits++suffix) sign (List.replicate D false) counts D n
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config factorSlots (by decide) FrameLoad.machine
    (heads pre.length) ambient _ _ base hr
  have hin : RecoveryFocus.config factorSlots (heads pre.length) ambient
      (loadCfg 0 (pre++frame bits++suffix) pre.length D (List.replicate D false))=
      cfg factorProgram.start pre.length ambient := by
    apply configuration_ext
    · rfl
    · exact focus_heads factorSlots (by decide) rfl _ _ _ _ (by intro j; fin_cases j <;> simp [loadCfg])
    · apply install_existing
      intro j; fin_cases j <;> rfl
  rw [hin] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · exact focus_heads factorSlots (by decide) rfl _ _ _ _ (by intro j; fin_cases j <;> simp [loadCfg])
  · change install factorSlots ambient (loadCfg 3 (pre++frame bits++suffix)
      (pre.length+2*bits.length+1) D (ZeroPadding.pad D (frame bits))).tapes=
        contents (pre++frame bits++suffix) sign (ZeroPadding.pad D (frame bits)) counts D n
    funext i
    fin_cases i
    · exact install_slot factorSlots (by decide) _ _ 0
    · exact install_other factorSlots _ _ 1 (by decide)
    · exact install_slot factorSlots (by decide) _ _ 1
    · exact install_other factorSlots _ _ 3 (by decide)
    · exact install_other factorSlots _ _ 4 (by decide)
    · exact install_slot factorSlots (by decide) _ _ 2

theorem count_run (pre bits suffix sign factor : List Bool) (D : ℕ) (hc : bits.length≤D) :
    ∃ r,runFrom countProgram (2*bits.length+2)
      (cfg countProgram.start pre.length (contents (pre++bits++suffix) sign factor (List.replicate D false) D bits.length))=some r ∧
      r.final=cfg 2 (pre.length+bits.length)
        (contents (pre++bits++suffix) sign factor (ZeroPadding.pad D bits) D bits.length) ∧
      r.steps=2*bits.length+2 := by
  obtain ⟨base,hr,hf,hs⟩ := CompetitorPlanePacketRawLoad.raw_load_run pre bits suffix D hc
  let ambient := contents (pre++bits++suffix) sign factor (List.replicate D false) D bits.length
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config countSlots (by decide)
    CompetitorPlanePacketRawLoad.machine (heads pre.length) ambient _ _ base hr
  have hin : RecoveryFocus.config countSlots (heads pre.length) ambient
      (CompetitorPlanePacketRawLoad.input pre bits suffix D)=cfg countProgram.start pre.length ambient := by
    apply configuration_ext
    · rfl
    · exact focus_heads countSlots (by decide) rfl _ _ _ _
        (by intro j; fin_cases j <;> simp [CompetitorPlanePacketRawLoad.input])
    · apply install_existing
      intro j; fin_cases j <;> rfl
  rw [hin] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · exact focus_heads countSlots (by decide) rfl _ _ _ _
      (by intro j; fin_cases j <;> simp [CompetitorPlanePacketRawLoad.output])
  · change install countSlots ambient (CompetitorPlanePacketRawLoad.output pre bits suffix D).tapes=
      contents (pre++bits++suffix) sign factor (ZeroPadding.pad D bits) D bits.length
    funext i
    fin_cases i
    · exact install_slot countSlots (by decide) _ _ 0
    · exact install_other countSlots _ _ 1 (by decide)
    · exact install_other countSlots _ _ 2 (by decide)
    · exact install_slot countSlots (by decide) _ _ 2
    · exact install_slot countSlots (by decide) _ _ 1
    · exact install_slot countSlots (by decide) _ _ 3

theorem fields_run (pre bits counts suffix sign : List Bool) (D : ℕ)
    (hb : 2*bits.length+1≤D) (hc : counts.length≤D) :
    ∃ r,runFrom machine (4*bits.length+2*counts.length+6)
      (cfg machine.start pre.length (contents (pre++frame bits++counts++suffix) sign
        (List.replicate D false) (List.replicate D false) D counts.length))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1+counts.length) ∧
      r.final.tapes=contents (pre++frame bits++counts++suffix) sign (ZeroPadding.pad D (frame bits))
        (ZeroPadding.pad D counts) D counts.length ∧ r.steps=4*bits.length+2*counts.length+6 := by
  obtain ⟨first,hfirst,hff,hfs⟩ := factor_run pre bits (counts++suffix) sign (List.replicate D false) D counts.length hb
  obtain ⟨second,hsecond,hsf,hss⟩ := count_run (pre++frame bits) counts suffix sign (ZeroPadding.pad D (frame bits)) D hc
  have hmid : Composition.restart first.final countProgram.start=
      cfg countProgram.start (pre++frame bits).length
        (contents ((pre++frame bits)++counts++suffix) sign (ZeroPadding.pad D (frame bits)) (List.replicate D false) D counts.length) := by
    rw [hff]
    simp [Composition.restart,cfg,frame_length,List.length_append,List.append_assoc,Nat.add_assoc]
  have hsecond' : runFrom countProgram (2*counts.length+2)
      (Composition.restart first.final countProgram.start)=some second := by rw [hmid]; exact hsecond
  have joined := Composition.run_join factorProgram countProgram _ _ _ first second hfirst hsecond'
  have htime : (4*bits.length+3)+1+(2*counts.length+2)=4*bits.length+2*counts.length+6 := by omega
  rw [htime] at joined
  refine ⟨Composition.joinedReceipt first second,?_,?_,?_,?_⟩
  · simpa only [machine,Composition.machine,Composition.leftConfig,cfg,List.append_assoc] using joined
  · change second.final.heads=_
    rw [hsf]
    simp [cfg,frame_length,List.length_append,Nat.add_assoc]
  · change second.final.tapes=_
    rw [hsf]
    rfl
  · change first.steps+1+second.steps=_
    omega

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketFields
