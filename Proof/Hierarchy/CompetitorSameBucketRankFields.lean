import Proof.Hierarchy.CompetitorSameBucketRecordCopy

/-! Decode the ID and rank of one actually loaded, present rank record.
The existing midpoint extractor and prefix copier are composed literally;
all scalar heads return to zero. Uniform padding is bounded local backing,
not a supplied decoded field or a machine instruction. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRankFields
open LocalBitMultitape SignedSortKey Streaming RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source (s k : ℕ) (score : ℤ) (id rank : ℕ) :=
  frame (KeyLoop.word s k (score,id,rank)++binary (k+s+1) rank)
def idInput (s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 7 → List Bool :=
  ![source s k score id rank,frame (binary k 0),[],[false],[],List.replicate (2*k) false,List.replicate (4*k+7) false]
def idOutput (s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 7 → List Bool :=
  ![source s k score id rank,frame (binary k 0),[],[false],frame (binary k id),
    List.replicate (2*k) false,List.replicate (4*k+7) false]
def idMachine := Rewind.machine KeyPair.machine

theorem id_ready (s k : ℕ) (score : ℤ) (id rank : ℕ) :
    ClockJoin.ReadyRun idMachine (8*k+16) (idInput s k score id rank) (idOutput s k score id rank) := by
  let suffix := frame (binary (s+1) (shifted s score)++binary (k+s+1) rank)
  have hsource : marks (binary k id)++suffix=source s k score id rank := by
    simp only [source,KeyLoop.word,encode_word,List.append_assoc,frame_append,suffix]
  obtain ⟨base,hb,bf,bs,_⟩ := KeyPair.pair_run (binary k id) suffix (binary k 0)
    [] [] [] [] (2*k) (by simp) rfl (by simp) (by simp)
  simp only [binary_length,List.length_nil,Nat.add_zero,List.append_nil,List.nil_append,hsource] at hb bf bs
  have hi : KeyPair.config 0 (source s k score id rank) (frame (binary k 0))
      (marks []) (frame []) [] (2*k)=initialConfiguration KeyPair.machine
      (![source s k score id rank,frame (binary k 0),[],[false],[],List.replicate (2*k) false] : Fin 6 → List Bool) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  change runFrom KeyPair.machine (4*k+7) _=some base at hb
  rw [hi] at hb
  obtain ⟨actual,ha,atapes,ac,ah,as,_⟩ := Rewind.Workspace.reset_workspace KeyPair.machine _ _ base hb (4*k+7)
  have hbound : 2*base.steps+2≤8*k+16 := by omega
  have he := run_moreFuel idMachine _ (8*k+16-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbound] at he
  have hinput : Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
      ![source s k score id rank,frame (binary k 0),[],[false],[],List.replicate (2*k) false]
      (fun _ => List.replicate (4*k+7) false)=idInput s k score id rank := by
    funext i; fin_cases i <;> rfl
  rw [hinput] at he
  refine ⟨actual,he,?_,ah,as.trans_le hbound⟩
  funext i
  fin_cases i
  · exact (atapes 0).trans (by rw [bf]; rfl)
  · exact (atapes 1).trans (by rw [bf]; rfl)
  · exact (atapes 2).trans (by rw [bf]; rfl)
  · exact (atapes 3).trans (by rw [bf]; rfl)
  · exact (atapes 4).trans (by rw [bf]; rfl)
  · exact (atapes 5).trans (by rw [bf]; rfl)
  · have index : (0 : Fin 1).natAdd 6=(6 : Fin 7) := by decide
    change actual.final.tapes 6=List.replicate (4*k+7) false
    simpa only [index,max_eq_left bs] using ac

def rankSlots (i : Fin 7) : Fin 13 := i.castAdd 6
def idSlots : Fin 7 → Fin 13 := ![0,7,8,9,10,11,12]
noncomputable def first := RecoveryFocus.machine rankSlots RecordExtractReset.machine
noncomputable def last := RecoveryFocus.machine idSlots idMachine
noncomputable def machine := Composition.machine first last

def input (s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 13 → List Bool :=
  Fin.addCases (m := 7) (n := 6) (motive := fun _ => List Bool)
    (RecordExtractReset.input (KeyLoop.word s k (score,id,rank)) (binary (k+s+1) rank) [] [])
    ![frame (binary k 0),[],[false],[],List.replicate (2*k) false,List.replicate (4*k+7) false]
def output (s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 13 → List Bool :=
  ![source s k score id rank,source s k score id rank,List.replicate (4*(k+s+1)+1) false,
    List.replicate (8*(k+s+1)+3) false,frame (binary (k+s+1) rank),
    List.replicate (2*(k+s+1)+1) false,List.replicate (24*(k+s+1)+14) false,
    frame (binary k 0),[],[false],frame (binary k id),List.replicate (2*k) false,List.replicate (4*k+7) false]
def budget (s k : ℕ) := 48*(k+s+1)+8*k+47

theorem fields_ready (s k : ℕ) (score : ℤ) (id rank : ℕ) :
    ClockJoin.ReadyRun machine (budget s k) (input s k score id rank) (output s k score id rank) := by
  let word := KeyLoop.word s k (score,id,rank)
  let ranked := binary (k+s+1) rank
  have hw : word.length=k+s+1 := KeyLoop.word_length s k _
  obtain ⟨base,hb,_,bt,bh,bs,_⟩ := RecordExtractReset.reset_run word ranked [] []
    (by simp [ranked,hw]) (by simp) (by simp)
  rw [hw] at hb bs
  have ready : ClockJoin.ReadyRun RecordExtractReset.machine (48*(k+s+1)+30)
      (RecordExtractReset.input word ranked [] []) (RecordExtractReset.output word ranked) :=
    ⟨base,hb,bt,bh,bs.le⟩
  let middle := install rankSlots (input s k score id rank) (RecordExtractReset.output word ranked)
  have hfirst := CompetitorRationalProducts.bounded_focus rankSlots (by decide) _ _ _ ready
    (input s k score id rank) (by intro i; fin_cases i <;> rfl)
  have hid : ∀ i,middle (idSlots i)=idInput s k score id rank i := by
    intro i
    fin_cases i
    · exact install_slot rankSlots (by decide) _ _ 0
    all_goals first
      | exact install_other rankSlots _ _ 7 (by decide)
      | exact install_other rankSlots _ _ 8 (by decide)
      | exact install_other rankSlots _ _ 9 (by decide)
      | exact install_other rankSlots _ _ 10 (by decide)
      | exact install_other rankSlots _ _ 11 (by decide)
      | exact install_other rankSlots _ _ 12 (by decide)
  have hlast := CompetitorRationalProducts.bounded_focus idSlots (by decide) _ _ _
    (id_ready s k score id rank) middle hid
  have hall := ClockJoin.join first last _ _ _ _ _ hfirst hlast
  have ht : (48*(k+s+1)+30)+1+(8*k+16)=budget s k := by unfold budget; omega
  rw [ht] at hall
  have hout : install idSlots middle (idOutput s k score id rank)=output s k score id rank := by
    funext i
    fin_cases i
    · exact install_slot idSlots (by decide) _ _ 0
    · exact (install_other idSlots _ _ 1 (by decide)).trans (install_slot rankSlots (by decide) _ _ 1)
    · apply (install_other idSlots _ _ 2 (by decide)).trans
      apply (install_slot rankSlots (by decide) _ _ 2).trans
      simp [RecordExtractReset.output,RecordExtract.finished,word,ranked,KeyLoop.word_length,Fin.addCases]
      congr 1
      omega
    · apply (install_other idSlots _ _ 3 (by decide)).trans
      apply (install_slot rankSlots (by decide) _ _ 3).trans
      simp [RecordExtractReset.output,RecordExtract.finished,word,ranked,KeyLoop.word_length,Fin.addCases]
      congr 1
      omega
    · exact (install_other idSlots _ _ 4 (by decide)).trans (install_slot rankSlots (by decide) _ _ 4)
    · apply (install_other idSlots _ _ 5 (by decide)).trans
      apply (install_slot rankSlots (by decide) _ _ 5).trans
      simp [RecordExtractReset.output,RecordExtract.finished,word,KeyLoop.word_length,Fin.addCases]
      rfl
    · apply (install_other idSlots _ _ 6 (by decide)).trans
      apply (install_slot rankSlots (by decide) _ _ 6).trans
      simp [RecordExtractReset.output,word,KeyLoop.word_length,Fin.addCases]
      rfl
    · exact install_slot idSlots (by decide) _ _ 1
    · exact install_slot idSlots (by decide) _ _ 2
    · exact install_slot idSlots (by decide) _ _ 3
    · exact install_slot idSlots (by decide) _ _ 4
    · exact install_slot idSlots (by decide) _ _ 5
    · exact install_slot idSlots (by decide) _ _ 6
  rw [hout] at hall
  exact hall

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRankFields
