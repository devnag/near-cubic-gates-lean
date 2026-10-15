import Proof.Hierarchy.CompetitorSameBucketGroupRead

/-! Whole sign/magnitude/two-ID read from the original sorted key bytes.
The enclosing controller receives the actual extracted fields, not supplied
record projections or a free change of the source cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (sign : Bool) (magnitude ids : List Bool) : List Bool :=
  [true,true,true,sign]++Streaming.marks magnitude++Streaming.marks ids++[false]

theorem word_length (sign : Bool) (magnitude ids : List Bool) :
    (word sign magnitude ids).length=2*magnitude.length+2*ids.length+5 := by
  simp only [word,List.length_append,Streaming.marks_length,List.length_cons,List.length_nil]
  omega

theorem word_frame (sign : Bool) (magnitude ids : List Bool) :
    word sign magnitude ids=frame (true::sign::(magnitude++ids)) := by
  have h := Streaming.frame_append ids []
  simp only [List.append_nil,frame] at h
  simp only [word,frame,Streaming.frame_append,List.cons_append,List.nil_append,List.append_assoc,h]

theorem read_run (pre suffix magnitude ids oldMagnitude oldIDs oldFlag : List Bool) (cap : ℕ) (sign : Bool)
    (hm : oldMagnitude.length≤2*magnitude.length+1) (hi : oldIDs.length≤2*ids.length+1)
    (hf : oldFlag.length≤1) :
    ∃ r,runFrom machine (budget magnitude.length ids.length)
      (cfg machine.start (pre++word sign magnitude ids++suffix) oldMagnitude oldIDs oldFlag
        pre.length magnitude.length ids.length cap)=some r ∧
      r.final.heads=heads (pre.length+(word sign magnitude ids).length) ∧
      r.final.tapes=data (pre++word sign magnitude ids++suffix) (frame magnitude) (frame ids) [sign]
        magnitude.length ids.length cap ∧ r.steps=budget magnitude.length ids.length := by
  let source := pre++word sign magnitude ids++suffix
  let pm := pre++[true,true,true,sign]
  let pi := pm++Streaming.marks magnitude
  let endpoint := pre.length+2*magnitude.length+2*ids.length+4
  have hmword : pm++Streaming.marks magnitude++(Streaming.marks ids++[false]++suffix)=source := by
    simp only [pm,source,word,List.append_assoc]
  have hiword : pi++Streaming.marks ids++([false]++suffix)=source := by
    simp only [pi,pm,source,word,List.append_assoc]
  obtain ⟨first,hfirst,hff,hfs⟩ := sign_run pre (Streaming.marks magnitude++Streaming.marks ids++[false]++suffix)
    oldMagnitude oldIDs oldFlag magnitude.length ids.length cap sign hf
  have hsword : pre++[true,true,true,sign]++(Streaming.marks magnitude++Streaming.marks ids++[false]++suffix)=source := by
    simp only [source,word,List.append_assoc]
  rw [hsword] at hfirst hff
  obtain ⟨native,hn,hnh,hnt,hns⟩ := native_run pm magnitude (Streaming.marks ids++[false]++suffix)
    oldMagnitude oldIDs [sign] ids.length cap hm
  rw [hmword] at hn hnt
  obtain ⟨indices,hj,hjh,hjt,hjs⟩ := id_run pi ids ([false]++suffix)
    (frame magnitude) oldIDs [sign] magnitude.length cap hi
  rw [hiword] at hj hjt
  obtain ⟨last,hl,hlf,hls⟩ := delimiter_run source (frame magnitude) (frame ids) [sign]
    endpoint magnitude.length ids.length cap
  have hlenm : pm.length=pre.length+4 := by simp [pm]
  have hleni : pi.length=pre.length+4+2*magnitude.length := by
    simp [pi,pm,Streaming.marks_length]
    omega
  have hdock : Composition.restart indices.final delimiter.start=
      cfg 0 source (frame magnitude) (frame ids) [sign] endpoint magnitude.length ids.length cap := by
    apply configuration_ext
    · rfl
    · change indices.final.heads=heads endpoint
      rw [hjh,hleni]
      congr 1
      dsimp [endpoint]
      omega
    · exact hjt
  have hl' : runFrom delimiter 1 (Composition.restart indices.final delimiter.start)=some last := by
    rw [hdock]
    exact hl
  have htail := Composition.run_join idProgram delimiter _ _ _ indices last hj hl'
  have hndock : Composition.restart native.final tail.start=
      Composition.leftConfig 2 (cfg idProgram.start source (frame magnitude) oldIDs [sign]
        pi.length magnitude.length ids.length cap) := by
    apply configuration_ext
    · rfl
    · change native.final.heads=heads pi.length
      rw [hnh,hlenm,hleni]
    · exact hnt
  have htail' : runFrom tail ((4*ids.length+2)+1+1)
      (Composition.restart native.final tail.start)=some (Composition.joinedReceipt indices last) := by
    rw [hndock]
    exact htail
  have hfields := Composition.run_join nativeProgram tail _ _ _ native
    (Composition.joinedReceipt indices last) hn htail'
  have hsdock : Composition.restart first.final fields.start=
      Composition.leftConfig 8 (cfg nativeProgram.start source oldMagnitude oldIDs [sign]
        pm.length magnitude.length ids.length cap) := by
    rw [hff]
    apply configuration_ext
    · rfl
    · rw [hlenm]
      rfl
    · rfl
  have hfields' : runFrom fields ((4*magnitude.length+2)+1+((4*ids.length+2)+1+1))
      (Composition.restart first.final fields.start)=some
        (Composition.joinedReceipt native (Composition.joinedReceipt indices last)) := by
    rw [hsdock]
    exact hfields
  have hall := Composition.run_join signMachine fields _ _ _ first
    (Composition.joinedReceipt native (Composition.joinedReceipt indices last)) hfirst hfields'
  have hbudget : 4+1+((4*magnitude.length+2)+1+((4*ids.length+2)+1+1))=
      budget magnitude.length ids.length := by unfold budget; omega
  rw [hbudget] at hall
  refine ⟨Composition.joinedReceipt first
    (Composition.joinedReceipt native (Composition.joinedReceipt indices last)),hall,?_,?_,?_⟩
  · change last.final.heads=_
    rw [hlf]
    change heads (endpoint+1)=_
    rw [word_length]
    congr 1
    dsimp [endpoint]
    omega
  · change last.final.tapes=_
    rw [hlf]
    rfl
  · change first.steps+1+(native.steps+1+(indices.steps+1+last.steps))=_
    rw [hfs,hns,hjs,hls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupRead
