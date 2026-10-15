import Proof.Hierarchy.CompetitorSameBucketBlockDrivers

/-! Load one complete padded B-record bucket into a reusable local bank,
then physically return the original packet cursor by B fixed ranked fields.
Only this bucket is traversed; no global rank-bank rewind occurs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBlockLoad
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (h b cap pos : ℕ) (target : List Bool) : Configuration 6 s :=
  ⟨q,![1,pos,0,0,0,1],![UnaryTemplate.tape ((4*h+1)*b),source,target,List.replicate cap false,
    UnaryTemplate.tape h,UnaryTemplate.tape b]⟩
def first := TapeEmbedding.machine 2 CompetitorSameBucketRecordCopy.machine
def reverseSlots : Fin 3 → Fin 6 := ![1,4,5]
theorem reverse_injective : Function.Injective reverseSlots := by decide
noncomputable def last := RecoveryFocus.machine reverseSlots MatrixRankRowReverse.machine
noncomputable def machine := Composition.machine first last

def budget (h b : ℕ) := CompetitorSameBucketRecordCopy.budget ((4*h+1)*b)+1+MatrixRankRowReverse.budget h b

theorem copy_run (h b cap : ℕ) (pre bits suffix : List Bool) (hlen : bits.length=(4*h+1)*b)
    (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom first (CompetitorSameBucketRecordCopy.budget bits.length)
        (cfg first.start (pre++bits++suffix) h b cap pre.length (List.replicate cap false))=some r ∧
      r.final=cfg r.final.control (pre++bits++suffix) h b cap (pre.length+bits.length) (ZeroPadding.pad cap bits) ∧
      r.steps=CompetitorSameBucketRecordCopy.budget bits.length := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketRecordCopy.padded_run cap pre bits suffix hc
  have hr := TapeEmbedding.run_embed CompetitorSameBucketRecordCopy.machine (![0,1] : Fin 2 → ℕ)
    ![UnaryTemplate.tape h,UnaryTemplate.tape b] _ _ base hb
  have hi : TapeEmbedding.config (![0,1] : Fin 2 → ℕ) ![UnaryTemplate.tape h,UnaryTemplate.tape b]
      (CompetitorSameBucketRecordCopy.paddedInput cap pre bits suffix)=
      cfg first.start (pre++bits++suffix) h b cap pre.length (List.replicate cap false) := by
    apply configuration_ext
    · rfl
    · simp only [TapeEmbedding.config,CompetitorSameBucketRecordCopy.padded_heads]
      funext i; fin_cases i <;> rfl
    · simp only [TapeEmbedding.config,CompetitorSameBucketRecordCopy.padded_tapes]
      funext i; fin_cases i <;> simp [cfg,hlen,Fin.addCases]
  rw [hi] at hr
  refine ⟨TapeEmbedding.receipt (![0,1] : Fin 2 → ℕ) ![UnaryTemplate.tape h,UnaryTemplate.tape b] base,hr,?_,bs⟩
  change TapeEmbedding.config _ _ base.final=_
  apply configuration_ext
  · rfl
  · simp only [TapeEmbedding.config,bh]
    funext i; fin_cases i <;> rfl
  · simp only [TapeEmbedding.config,bt]
    funext i; fin_cases i <;> simp [cfg,hlen,Fin.addCases]

theorem reverse_pick (i : Fin 6) : RecoveryFocus.pick reverseSlots i=
    (![none,some 0,none,none,some 1,some 2] : Fin 6 → Option (Fin 3)) i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot reverseSlots reverse_injective 0
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · unfold RecoveryFocus.pick; apply dif_neg; decide
  · exact RecoveryFocus.pick_slot reverseSlots reverse_injective 1
  · exact RecoveryFocus.pick_slot reverseSlots reverse_injective 2

theorem reverse_run (h b cap pos : ℕ) (source target : List Bool) :
    ∃ r,runFrom last (MatrixRankRowReverse.budget h b) (cfg last.start source h b cap pos target)=some r ∧
      r.final.heads=(cfg last.start source h b cap (pos-(4*h+1)*b) target).heads ∧
      r.final.tapes=(cfg last.start source h b cap (pos-(4*h+1)*b) target).tapes ∧
      r.steps≤MatrixRankRowReverse.budget h b := by
  obtain ⟨base,hb,bs,bf⟩ := MatrixRankRowReverse.row_run source h b pos
  let entry := cfg last.start source h b cap pos target
  have hi : RecoveryFocus.config reverseSlots entry.heads entry.tapes (MatrixRankRowReverse.cfg 0 source h b pos)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [MatrixRankRowReverse.cfg_heads]
      fin_cases i <;> rfl
    · intro i
      rw [MatrixRankRowReverse.cfg_tapes]
      fin_cases i <;> rfl
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config reverseSlots reverse_injective MatrixRankRowReverse.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,hs.trans_le bs⟩
  · rw [hf,bf]
    simp only [RecoveryFocus.config,MatrixRankRowReverse.cfg_heads,reverse_pick]
    funext i
    fin_cases i <;> simp [entry,cfg,MatrixRankFieldReverse.distance,Nat.mul_comm]
  · rw [hf,bf]
    simp only [RecoveryFocus.config,MatrixRankRowReverse.cfg_tapes,reverse_pick]
    funext i
    fin_cases i <;> simp [entry,cfg]

theorem block_run (h b cap : ℕ) (pre bits suffix : List Bool) (hlen : bits.length=(4*h+1)*b)
    (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom machine (budget h b)
        (cfg machine.start (pre++bits++suffix) h b cap pre.length (List.replicate cap false))=some r ∧
      r.final.heads=(cfg machine.start (pre++bits++suffix) h b cap pre.length (ZeroPadding.pad cap bits)).heads ∧
      r.final.tapes=(cfg machine.start (pre++bits++suffix) h b cap pre.length (ZeroPadding.pad cap bits)).tapes ∧
      r.steps≤budget h b := by
  obtain ⟨r0,h0,hf0,hs0⟩ := copy_run h b cap pre bits suffix hlen hc
  obtain ⟨r1,h1,hh1,ht1,hs1⟩ := reverse_run h b cap (pre.length+bits.length) (pre++bits++suffix) (ZeroPadding.pad cap bits)
  have hi : Composition.restart r0.final last.start=
      cfg last.start (pre++bits++suffix) h b cap (pre.length+bits.length) (ZeroPadding.pad cap bits) := by rw [hf0]; rfl
  rw [←hi] at h1
  have hall := Composition.run_join first last _ _ _ r0 r1 h0 h1
  have pos : pre.length+bits.length-(4*h+1)*b=pre.length := by omega
  rw [pos] at hh1 ht1
  have time : CompetitorSameBucketRecordCopy.budget bits.length+1+MatrixRankRowReverse.budget h b=budget h b := by rw [hlen]; rfl
  rw [time] at hall
  refine ⟨Composition.joinedReceipt r0 r1,hall,hh1,ht1,?_⟩
  change r0.steps+1+r1.steps≤_
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBlockLoad
