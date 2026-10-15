import Proof.MachineModel.OrdinaryMatrixScoreCapacity

/-! The capacity printer retains frame(2^W). This paid two-cell skip and
framed copy turns it into the W-bit offset 2^(W−1), then rewinds all heads. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreTopBit
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skip : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if h : q.val<2 then some ⟨⟨q.val+1,by omega⟩,fun _ => none,
    fun i => if i=0 then .right else .stay⟩ else none
def skipCfg (q : Fin 3) (source : List Bool) : Configuration 3 3 :=
  ⟨q,![q.val,0,0],![source,[],[]]⟩

theorem skip_run (source : List Bool) :
    ∃ actual,run skip 2 ![source,[],[]]=some actual ∧ actual.final=skipCfg 2 source ∧ actual.steps=2 := by
  have step0 : step skip (skipCfg 0 source)=some (skipCfg 1 source) := by
    simp [step,skip,skipCfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have step1 : step skip (skipCfg 1 source)=some (skipCfg 2 source) := by
    simp [step,skip,skipCfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨actual,hr,hf,hs⟩ := ((Timed.single (by rfl) step0).trans (Timed.single (by rfl) step1)).run (by rfl)
  have hi : skipCfg 0 source=initialConfiguration skip ![source,[],[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨actual,hr,hf,hs⟩

def raw : Machine 3 7 := Composition.machine skip FrameLoad.machine
def machine : Machine 4 9 := Rewind.machine raw

theorem raw_run (s : ℕ) :
    ∃ actual,run raw (4*(s+1)+6) ![frame (List.replicate (s+1) false++[true]),[],[]]=some actual ∧
      actual.final.tapes=![frame (List.replicate (s+1) false++[true]),frame (List.replicate s false++[true]),
        List.replicate (2*(s+1)+1) false] ∧ actual.steps=4*(s+1)+6 := by
  let source := frame (List.replicate (s+1) false++[true])
  obtain ⟨first,hf,hff,hfs⟩ := skip_run source
  obtain ⟨last,hl,hlf,hls,_⟩ := FrameLoad.load_run [true,false] (List.replicate s false++[true]) [] [] (by simp)
  have hsource : [true,false]++frame (List.replicate s false++[true])++[]=source := by
    simp [source,List.replicate_succ,frame]
  rw [hsource] at hl hlf
  have hlen : (List.replicate s false++[true]).length=s+1 := by simp
  rw [hlen] at hl hls
  have hi : Composition.restart first.final FrameLoad.machine.start=FrameLoad.scan 0 source 2 [] [] := by
    rw [hff]
    rfl
  have hl' : runFrom FrameLoad.machine (4*(s+1)+3) (Composition.restart first.final FrameLoad.machine.start)=some last := by
    rw [hi]
    exact hl
  have hj := Composition.run_join skip FrameLoad.machine 2 (4*(s+1)+3) _ first last hf hl'
  have htime : 2+1+(4*(s+1)+3)=4*(s+1)+6 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change last.final.tapes=_
    rw [hlf]
    funext i; fin_cases i <;> simp [FrameLoad.reset,source]
  · change first.steps+1+last.steps=_
    omega

theorem top_bit_run (s : ℕ) :
    ∃ actual,run machine (8*(s+1)+14)
        ![frame (List.replicate (s+1) false++[true]),[],[],[]]=some actual ∧
      actual.final.tapes 0=frame (List.replicate (s+1) false++[true]) ∧
      actual.final.tapes 1=frame (binary (s+1) (2^s)) ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps=8*(s+1)+14 := by
  obtain ⟨base,hb,ht,hs⟩ := raw_run s
  obtain ⟨actual,hr,hout,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have htime : 2*base.steps+2=8*(s+1)+14 := by omega
  rw [htime] at hr
  have hi : (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
      ![frame (List.replicate (s+1) false++[true]),[],[]] (fun _ => []))=
      ![frame (List.replicate (s+1) false++[true]),[],[],[]] := by funext i; fin_cases i <;> rfl
  change run machine (8*(s+1)+14) (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
    ![frame (List.replicate (s+1) false++[true]),[],[]] (fun _ => []))=some actual at hr
  rw [hi] at hr
  have hv : RadixSemantics.value (List.replicate s false++[true])=2^s := by
    simp [RadixSemantics.value_append,RadixSemantics.value]
  have he := BoundedCounter.binary_of_value (List.replicate s false++[true])
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,hv] at he
  refine ⟨actual,hr,(hout 0).trans (congrFun ht 0),?_,hh,hsteps.trans htime⟩
  have ho := (hout 1).trans (congrFun ht 1)
  change actual.final.tapes 1=frame (List.replicate s false++[true]) at ho
  rw [he]
  exact ho

end NearCubicWires.RepairOrdinary.MatrixScoreTopBit
