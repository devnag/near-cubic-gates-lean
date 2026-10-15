import Proof.Hierarchy.CompetitorSameBucketCoefficientLoad

/-! The two gate-stream loaders share the same paid bounded local clear.
The global source cursor is retained by the clear and advanced by the
already checked packet or coefficient copier. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketStreamLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (cap pos : ℕ) (source target log : List Bool) : Configuration 5 s :=
  ⟨q,![pos,0,0,0,0],![source,target,log,List.replicate cap true,List.replicate (cap+1) false]⟩
def eraseSlots : Fin 4 → Fin 5 := ![1,2,3,4]
theorem erase_injective : Function.Injective eraseSlots := by decide
noncomputable def clear := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def machine {s : ℕ} (p : Machine 3 s) := Composition.machine clear (TapeEmbedding.machine 2 p)

theorem clear_run (cap pos : ℕ) (source target log : List Bool)
    (ht : target.length≤cap) (hl : log.length≤cap) :
    ∃ actual,runFrom clear (2*cap+4) (cfg clear.start cap pos source target log)=some actual ∧
      actual.final.heads=![pos,0,0,0,0] ∧
      actual.final.tapes=(cfg clear.start cap pos source (List.replicate cap false) (List.replicate cap false)).tapes ∧
      actual.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine 2) (2*cap+4)
      (CompetitorPlaneWorkspace.eraseInput cap (![target,log] : Fin 2 → List Bool))
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 2 => List.replicate cap false)) := by
    simpa only [CompetitorPlaneWorkspace.eraseInput,max_self] using
      RecoveryScratchErase.erase_ready cap (cap+1) (![target,log] : Fin 2 → List Bool)
        (by intro i; fin_cases i; exact ht; exact hl)
  obtain ⟨base,hb,bt,bh,bs⟩ := ready
  let entry := cfg clear.start cap pos source target log
  have hi : RecoveryFocus.config eraseSlots entry.heads entry.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 2)
        (CompetitorPlaneWorkspace.eraseInput cap (![target,log] : Fin 2 → List Bool)))=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config eraseSlots erase_injective (RecoveryScratchErase.resetMachine 2)
    entry.heads entry.tapes _ _ base hb
  rw [hi] at ha
  have pick0 : RecoveryFocus.pick eraseSlots 0=none := by
    unfold RecoveryFocus.pick
    apply dif_neg
    rintro ⟨i,hi⟩
    fin_cases i <;> simp_all [eraseSlots]
  have pick1 := RecoveryFocus.pick_slot eraseSlots erase_injective 0
  have pick2 := RecoveryFocus.pick_slot eraseSlots erase_injective 1
  have pick3 := RecoveryFocus.pick_slot eraseSlots erase_injective 2
  have pick4 := RecoveryFocus.pick_slot eraseSlots erase_injective 3
  change RecoveryFocus.pick eraseSlots 1=some 0 at pick1
  change RecoveryFocus.pick eraseSlots 2=some 1 at pick2
  change RecoveryFocus.pick eraseSlots 3=some 2 at pick3
  change RecoveryFocus.pick eraseSlots 4=some 3 at pick4
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick0,pick1,pick2,pick3,pick4,bh,entry,cfg]
  · rw [hf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick0,pick1,pick2,pick3,pick4,bt,entry,cfg,CompetitorPlaneWorkspace.eraseInput,Fin.addCases]

theorem load_run {s : ℕ} (p : Machine 3 s) (cap pos endPos b : ℕ) (source target log result : List Bool)
    (ht : target.length≤cap) (hl : log.length≤cap)
    (load : ∃ base,runFrom p b ⟨p.start,![pos,0,0],![source,List.replicate cap false,List.replicate cap false]⟩=some base ∧
      base.final.heads=![endPos,0,0] ∧ base.final.tapes=![source,result,List.replicate cap false] ∧ base.steps≤b) :
    ∃ actual,runFrom (machine p) (2*cap+b+5) (cfg (machine p).start cap pos source target log)=some actual ∧
      actual.final.heads=![endPos,0,0,0,0] ∧
      actual.final.tapes=(cfg p.start cap endPos source result (List.replicate cap false)).tapes ∧
      actual.steps≤2*cap+b+5 := by
  obtain ⟨erase,he,eh,et,es⟩ := clear_run cap pos source target log ht hl
  obtain ⟨base,hb,bh,bt,bs⟩ := load
  let ehds : Fin 2 → ℕ := ![0,0]
  let etps : Fin 2 → List Bool := ![List.replicate cap true,List.replicate (cap+1) false]
  have hlift := TapeEmbedding.run_embed p ehds etps _ _ base hb
  have hi : Composition.restart erase.final (TapeEmbedding.machine 2 p).start=
      TapeEmbedding.config ehds etps ⟨p.start,![pos,0,0],![source,List.replicate cap false,List.replicate cap false]⟩ := by
    apply configuration_ext
    · rfl
    · change erase.final.heads=_
      rw [eh]; funext i; fin_cases i <;> rfl
    · change erase.final.tapes=_
      rw [et]; funext i; fin_cases i <;> rfl
  rw [←hi] at hlift
  have hall := Composition.run_join clear (TapeEmbedding.machine 2 p) _ _ _ erase
    (TapeEmbedding.receipt ehds etps base) he hlift
  have hbudget : (2*cap+4)+1+b=2*cap+b+5 := by omega
  rw [hbudget] at hall
  refine ⟨Composition.joinedReceipt erase (TapeEmbedding.receipt ehds etps base),hall,?_,?_,?_⟩
  · change (TapeEmbedding.config ehds etps base.final).heads=_
    funext i
    fin_cases i <;> simp [TapeEmbedding.config,bh,ehds,Fin.addCases]
  · change (TapeEmbedding.config ehds etps base.final).tapes=_
    funext i
    fin_cases i <;> simp [TapeEmbedding.config,bt,etps,cfg,Fin.addCases]
  · change erase.steps+1+base.steps≤_
    omega

noncomputable def packet := machine MatrixRankPacketLoad.machine
noncomputable def coefficient := machine CompetitorSameBucketCoefficientLoad.machine

theorem packet_run (cap : ℕ) (words : List (List Bool)) (pre suffix target log : List Bool)
    (ht : target.length≤cap) (hl : log.length≤cap) (hn : ∀ w∈words,w≠[])
    (hc : MatrixBatchRankAppend.packetBudget words≤cap) :
    ∃ actual,runFrom packet (2*cap+MatrixRankPacketLoad.budget words+5)
        (cfg packet.start cap pre.length (pre++MatrixBatchRankAppend.stream words++suffix) target log)=some actual ∧
      actual.final.heads=![pre.length+(MatrixBatchRankAppend.stream words).length,0,0,0,0] ∧
      actual.final.tapes=(cfg packet.start cap 0 (pre++MatrixBatchRankAppend.stream words++suffix)
        (ZeroPadding.pad cap (MatrixBatchRankAppend.stream words)) (List.replicate cap false)).tapes ∧
      actual.steps≤2*cap+MatrixRankPacketLoad.budget words+5 := by
  apply load_run _ cap _ _ _ _ target log _ ht hl
  obtain ⟨base,hb,bh,bt,bs⟩ := MatrixRankPacketLoad.padded_run cap words pre suffix hn hc
  have hi : MatrixRankPacketLoad.paddedInput cap words pre suffix=
      ⟨MatrixRankPacketLoad.machine.start,![pre.length,0,0],
        ![pre++MatrixBatchRankAppend.stream words++suffix,List.replicate cap false,List.replicate cap false]⟩ :=
    configuration_ext rfl (MatrixRankPacketLoad.padded_heads ..) (MatrixRankPacketLoad.padded_tapes ..)
  rw [hi] at hb
  exact ⟨base,hb,bh,bt,bs.le⟩

theorem coefficient_run (cap : ℕ) (bits pre suffix target log : List Bool)
    (ht : target.length≤cap) (hl : log.length≤cap) (hc : 2*bits.length+1≤cap) :
    ∃ actual,runFrom coefficient (2*cap+CompetitorSameBucketCoefficientLoad.budget bits+5)
        (cfg coefficient.start cap pre.length (pre++frame bits++suffix) target log)=some actual ∧
      actual.final.heads=![pre.length+(frame bits).length,0,0,0,0] ∧
      actual.final.tapes=(cfg coefficient.start cap 0 (pre++frame bits++suffix)
        (ZeroPadding.pad cap (frame bits)) (List.replicate cap false)).tapes ∧
      actual.steps≤2*cap+CompetitorSameBucketCoefficientLoad.budget bits+5 := by
  apply load_run _ cap _ _ _ _ target log _ ht hl
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketCoefficientLoad.padded_run cap bits pre suffix hc
  have hi : CompetitorSameBucketCoefficientLoad.paddedInput cap bits pre suffix=
      ⟨CompetitorSameBucketCoefficientLoad.machine.start,![pre.length,0,0],
        ![pre++frame bits++suffix,List.replicate cap false,List.replicate cap false]⟩ :=
    configuration_ext rfl (CompetitorSameBucketCoefficientLoad.padded_heads ..) (CompetitorSameBucketCoefficientLoad.padded_tapes ..)
  rw [hi] at hb
  exact ⟨base,hb,bh,bt,bs.le⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketStreamLoad
