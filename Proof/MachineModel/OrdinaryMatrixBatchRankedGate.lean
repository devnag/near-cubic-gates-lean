import Proof.MachineModel.OrdinaryMatrixBatchRankAppend

namespace NearCubicWires.RepairOrdinary.MatrixBatchRankedGate
open LocalBitMultitape SignedSortKey MatrixScoreBatch MatrixScoreReusableRanks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rankWords (r : Request) (gate : Fin r.Gates) :=
  (MatrixScoreRawRanks.entries r gate).map
    (fun e => KeyLoop.word r.S r.M e++binary (r.M+r.S+1) e.2.2)
theorem word_length (r : Request) (gate : Fin r.Gates) (w : List Bool) (hw : w∈rankWords r gate) :
    w.length=2*(r.M+r.S+1) := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hw
  simp only [List.length_append,KeyLoop.word_length,binary_length]
  omega
theorem words_nonempty (r : Request) (gate : Fin r.Gates) : ∀ w∈rankWords r gate,w≠[] := by
  intro w hw he
  have hl := word_length r gate w hw
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega
theorem words_length (r : Request) (gate : Fin r.Gates) : (rankWords r gate).length=r.U+r.U := by
  have hh := (DominanceSort.sorted_semantics r.S r.M (leftScore r) (rightScore r) gate
    (MatrixScoreRawRanks.size_fit r) (score_lo r gate) (score_hi r gate)).1.length_eq
  simpa [rankWords,MatrixScoreRawRanks.entries,KeyLoop.dominanceEntries,DominanceSort.copies] using hh
theorem stream_eq (r : Request) (gate : Fin r.Gates) :
    MatrixBatchRankAppend.stream (rankWords r gate)=MatrixScoreRawRanks.output r gate := by
  simp [MatrixBatchRankAppend.stream,MatrixBatchRankAppend.fields,rankWords,MatrixScoreRawRanks.output,
    KeyLoop.stream,KeyLoop.fields,List.flatMap_map]
theorem packet_budget (r : Request) (gate : Fin r.Gates) :
    MatrixBatchRankAppend.packetBudget (rankWords r gate)=(r.U+r.U)*(4*(r.M+r.S+1)+3)+3 := by
  have hl : (MatrixBatchRankAppend.fields (rankWords r gate)).length=
      (rankWords r gate).length*(4*(r.M+r.S+1)+1) := by
    unfold MatrixBatchRankAppend.fields
    rw [List.length_flatMap]
    have he : ((rankWords r gate).map (fun a => (frame a).length))=
        List.replicate (rankWords r gate).length (4*(r.M+r.S+1)+1) := by
      apply List.eq_replicate_iff.mpr
      constructor
      · simp
      · intro n hn
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hn
        rw [frame_length,word_length r gate w hw]
        omega
    rw [he,List.sum_replicate]
    rfl
  unfold MatrixBatchRankAppend.packetBudget
  rw [hl,words_length]
  ring
theorem packet_fits (r : Request) (gate : Fin r.Gates) :
    MatrixBatchRankAppend.packetBudget (rankWords r gate)≤D r := by
  have hd := MatrixScoreRawRanksBounds.header_width r
  have hw : r.M+r.S+1≤8*(r.d+r.p+1) := by omega
  have hm := Nat.mul_le_mul_left (r.U+r.U) hw
  have hq : 1≤r.d+r.p+1 := by omega
  have hsq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hu := Nat.mul_le_mul_left r.U hsq
  have hcap := capacity_gap r
  rw [packet_budget]
  unfold MatrixScoreRawRanksBounds.capacity at hcap
  nlinarith

def padCaps (r : Request) : Fin 3 → ℕ := ![D r,0,D r]
noncomputable def appendInput (r : Request) (gate : Fin r.Gates) (out : List Bool) :=
  ZeroPadding.config (padCaps r) (MatrixBatchRankAppend.input (rankWords r gate) out)
theorem append_input_heads (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (appendInput r gate out).heads= ![0,out.length,0] := by
  funext i
  fin_cases i <;> rfl
theorem append_input_tapes (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (appendInput r gate out).tapes= ![ZeroPadding.pad (D r) (MatrixScoreRawRanks.output r gate),
      out,List.replicate (D r) false] := by
  funext i
  fin_cases i
  · change ZeroPadding.pad (D r) (MatrixBatchRankAppend.stream (rankWords r gate))=_
    rw [stream_eq]
    rfl
  · change ZeroPadding.pad 0 out=out
    simp
  · rfl
theorem append_run (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    ∃ actual,runFrom MatrixBatchRankAppend.machine (MatrixBatchRankAppend.budget (rankWords r gate))
      (appendInput r gate out)=some actual ∧
      actual.final.heads= ![0,(out++MatrixScoreRawRanks.output r gate).length,0] ∧
      actual.final.tapes= ![ZeroPadding.pad (D r) (MatrixScoreRawRanks.output r gate),
        out++MatrixScoreRawRanks.output r gate,List.replicate (D r) false] ∧
      actual.steps=MatrixBatchRankAppend.budget (rankWords r gate) := by
  obtain ⟨base,hb,bh,bt,bs⟩ := MatrixBatchRankAppend.append_run (rankWords r gate) out (words_nonempty r gate)
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config MatrixBatchRankAppend.machine (padCaps r) _ _ base hb
  refine ⟨actual,ha,?_,?_,has.trans bs⟩
  · rw [haf]
    simp only [ZeroPadding.config]
    rw [bh,stream_eq]
  · rw [haf]
    simp only [ZeroPadding.config]
    rw [bt,stream_eq]
    funext i
    fin_cases i
    · rfl
    · simp [padCaps]
    · change ZeroPadding.pad (D r) (List.replicate (MatrixBatchRankAppend.packetBudget (rankWords r gate)) false)=_
      simp [ZeroPadding.pad,Nat.add_sub_of_le (packet_fits r gate)]

def slots : Fin 3 → Fin 44 := ![37,42,43]
theorem slots_injective : Function.Injective slots := by decide
theorem pick_other (i : Fin 42) (hi : i≠37) : RecoveryFocus.pick slots (i.castAdd 2)=none := by
  fin_cases i <;> first | contradiction | decide
noncomputable def first := TapeEmbedding.machine 2 MatrixScoreRetainedRanks.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBatchRankAppend.machine
noncomputable def machine := Composition.machine first last
noncomputable def input (r : Request) (gate : Fin r.Gates) (out : List Bool) :=
  Composition.leftConfig 9 (TapeEmbedding.config ![out.length,0] ![out,List.replicate (D r) false]
    (MatrixScoreReusableRanks.input r gate))
noncomputable def budget (r : Request) (gate : Fin r.Gates) := MatrixScoreRetainedRanks.budget r gate+1+
  MatrixBatchRankAppend.budget (rankWords r gate)

theorem gate_run (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    ∃ final : MatrixScoreLeftLoop.State r,∃ actual,
      runFrom machine (budget r gate) (input r gate out)=some actual ∧
      actual.final.tapes 42=out++MatrixScoreRawRanks.output r gate ∧
      actual.final.heads 42=(out++MatrixScoreRawRanks.output r gate).length ∧
      actual.final.tapes 43=List.replicate (D r) false ∧ actual.final.heads 43=0 ∧
      (∀ i : Fin 30,i≠24 → actual.final.tapes (i.castAdd 14)=
        ZeroPadding.pad (capacities r (i.castAdd 12)) (MatrixScoreRetainedRanks.finalFields r gate final i)) ∧
      (∀ i : Fin 42,actual.final.heads (i.castAdd 2)=MatrixScoreRetainedRanks.retainedHeads i) ∧
      (∀ i : Fin 42,(actual.final.tapes (i.castAdd 2)).length≤D r) ∧ actual.steps≤budget r gate := by
  obtain ⟨final,base,hb,b37,bt,bh,bfit,bs⟩ := MatrixScoreReusableRanks.gate_run r gate
  have he := TapeEmbedding.run_embed MatrixScoreRetainedRanks.machine ![out.length,0]
    ![out,List.replicate (D r) false] _ _ base hb
  let prepared := TapeEmbedding.receipt ![out.length,0] ![out,List.replicate (D r) false] base
  obtain ⟨body,ha,ah,atapes,as⟩ := append_run r gate out
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes (appendInput r gate out)=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [append_input_heads]
      fin_cases i
      · change base.final.heads 37=0
        rw [bh]
        rfl
      all_goals rfl
    · intro i
      rw [append_input_tapes]
      fin_cases i
      · exact b37
      all_goals rfl
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixBatchRankAppend.machine
    prepared.final.heads prepared.final.tapes _ _ body ha
  rw [hi] at hf
  have joined := Composition.run_join first last _ _ _ prepared focused he hf
  have localT (i : Fin 3) : focused.final.tapes (slots i)=body.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (i : Fin 3) : focused.final.heads (slots i)=body.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  refine ⟨final,Composition.joinedReceipt prepared focused,joined,
    (localT 1).trans (congrFun atapes 1),(localH 1).trans (congrFun ah 1),
    (localT 2).trans (congrFun atapes 2),(localH 2).trans (congrFun ah 2),?_,?_,?_,?_⟩
  · intro i hn
    change focused.final.tapes (i.castAdd 14)=_
    rw [hff]
    have hnone : RecoveryFocus.pick slots (i.castAdd 14)=none := by
      exact pick_other (i.castAdd 12) (by
        intro heq
        have hv:=congrArg (fun a : Fin 42 => a.val) heq
        change i.val=37 at hv
        omega)
    simp only [RecoveryFocus.config,hnone]
    rw [←show (i.castAdd 12).castAdd 2=i.castAdd 14 by rfl]
    simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config] using bt i hn
  · intro i
    change focused.final.heads (i.castAdd 2)=_
    by_cases hi : i=37
    · subst i
      exact (localH 0).trans (congrFun ah 0)
    rw [hff]
    simp only [RecoveryFocus.config,pick_other i hi]
    simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config] using congrFun bh i
  · intro i
    change (focused.final.tapes (i.castAdd 2)).length≤_
    by_cases hi : i=37
    · subst i
      have heq := (localT 0).trans (congrFun atapes 0)
      change focused.final.tapes 37=ZeroPadding.pad (D r) (MatrixScoreRawRanks.output r gate) at heq
      change (focused.final.tapes 37).length≤D r
      rw [heq]
      have hbase := bfit 37
      rw [b37] at hbase
      exact hbase
    rw [hff]
    simp only [RecoveryFocus.config,pick_other i hi]
    simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config] using bfit i
  · change prepared.steps+1+focused.steps≤_
    rw [hfs,as]
    change base.steps+1+_≤budget r gate
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchRankedGate
