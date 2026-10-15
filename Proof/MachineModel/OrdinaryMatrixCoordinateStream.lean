import Proof.MachineModel.OrdinaryMatrixCoordinateCell

/-! Traverse a complete coordinate stream with paid entry, return and stop
transitions. Bounded scratch is reused, and both global cursors advance. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming RecoveryExecution SignedSortKey
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Record := Bool × ℕ × ℕ
def word (w : ℕ) (r : Record) := frame (r.1::(binary w r.2.1++binary w r.2.2))
def stream (w : ℕ) (rs : List Record) := rs.flatMap (word w)
def output (w : ℕ) (rs : List Record) :=
  rs.flatMap (fun r => frame (r.1::(binary w r.2.2++binary w r.2.1)))
noncomputable def streamMachine : Machine 12 36 := StreamController.machine machine 7

@[simp] theorem word_length (w : ℕ) (r : Record) : (word w r).length=4*w+3 := by
  simp [word]
  omega

theorem iteration (w cap : ℕ) (source record clone rank out : List Bool) (pos fuel : ℕ)
    (r : ExecutionReceipt 12 34)
    (hr : runFrom machine fuel (cfg machine.start w cap source pos record clone rank out)=some r)
    (hread : readTapeBit source pos=true) :
    Timed streamMachine (r.steps+2)
      (cfg (test 34) w cap source pos record clone rank out)
      (controlConfig (fun _ => test 34) r.final) := by
  let c := cfg machine.start w cap source pos record clone rank out
  have he := StreamController.enter_step machine 7 c hread
  have hb := StreamController.body_prefix machine 7 fuel c r hr
  have hx := StreamController.return_step machine 7 r.final hb.2
  have first : Timed streamMachine 1 (cfg (test 34) w cap source pos record clone rank out)
      (controlConfig code c) := by
    exact Timed.single (StreamController.test_halted machine 7) he
  have middle : Timed streamMachine r.steps (controlConfig code c) (controlConfig code r.final) := ⟨_,hb.1⟩
  have last : Timed streamMachine 1 (controlConfig code r.final) (controlConfig (fun _ => test 34) r.final) :=
    Timed.single (StreamController.body_halted machine 7 _) hx
  have h := first.trans (middle.trans last)
  convert h using 1
  omega

theorem stream_run (w cap : ℕ) (rs : List Record) (pre record clone rank out : List Bool)
    (hcap : 2*w ≤ cap) (hr : record.length ≤ 4*w+1)
    (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ finalRecord finalClone finalRank,
      finalRecord.length ≤ 4*w+1 ∧ finalClone.length ≤ 4*w+1 ∧ finalRank.length ≤ 2*w+1 ∧
      ∃ actual : ExecutionReceipt 12 36,
        runFrom streamMachine (rs.length*(64*w+47)+1)
          (cfg (test 34) w cap (pre++stream w rs) pre.length record clone rank out)=some actual ∧
        actual.final=cfg (stop 34) w cap (pre++stream w rs) (pre.length+(stream w rs).length)
          finalRecord finalClone finalRank (out++output w rs) ∧
        actual.steps ≤ rs.length*(64*w+47)+1 := by
  induction rs generalizing pre record clone rank out with
  | nil =>
    let c := cfg machine.start w cap pre pre.length record clone rank out
    have hread : c.scanned 7=false := by
      change readTapeBit pre pre.length=false
      simp [readTapeBit,List.getD]
    have hs := Timed.single (StreamController.test_halted machine 7)
      (StreamController.stop_step machine 7 c hread)
    obtain ⟨r,hrun,hf,hsteps⟩ := hs.run (StreamController.stop_halted machine 7)
    refine ⟨record,clone,rank,hr,hc,hk,r,?_,?_,?_⟩
    · simpa [stream,streamMachine,c,controlConfig,cfg] using hrun
    · simpa [stream,output,c,controlConfig,cfg] using hf
    · simpa using hsteps.le
  | cons entry rs ih =>
    let a := binary w entry.2.1
    let b := binary w entry.2.2
    let stored := frame (a++b)
    let source := pre++stream w (entry::rs)
    let next := pre.length+4*w+3
    let appended := out++frame (entry.1::(b++a))
    have hstored : stored.length=4*w+1 := by simp [stored,a,b]; omega
    have hb : (frame b).length=2*w+1 := by simp [b]
    obtain ⟨body,hbody,hbf,hbs⟩ := cell_run w cap a b pre (stream w rs) record clone rank out entry.1
      (binary_length _ _) (binary_length _ _) hcap hr hc hk
    have hsource : pre++frame (entry.1::(a++b))++stream w rs=source := by
      simp [source,stream,word,a,b,List.append_assoc]
    rw [hsource] at hbody hbf
    obtain ⟨finalRecord,finalClone,finalRank,hfr,hfc,hfk,tail,htail,htf,hts⟩ :=
      ih (pre++word w entry) stored stored (frame b) appended hstored.le hstored.le hb.le
    have hsource' : (pre++word w entry)++stream w rs=source := by
      simp [source,stream,List.append_assoc]
    have hpos : (pre++word w entry).length=next := by simp [next,Nat.add_assoc]
    rw [hsource',hpos] at htail htf
    have hread : readTapeBit source pre.length=true := by
      change readTapeBit (pre++stream w (entry::rs)) pre.length=true
      simpa [stream,word,frame,List.append_assoc] using
        read_append pre (entry.1::frame (a++b)++stream w rs) true
    have hp := iteration w cap source record clone rank out pre.length (64*w+45) body hbody hread
    rw [hbf] at hp
    rcases hp with ⟨space,hp⟩
    obtain ⟨actual,haRun,hf,hs,_⟩ := hp.followedBy tail htail
    have hbound : body.steps+2+(rs.length*(64*w+47)+1) ≤ (entry::rs).length*(64*w+47)+1 := by
      simp only [List.length_cons]
      nlinarith only [hbs]
    have hm := runFrom_moreFuel streamMachine _
      ((entry::rs).length*(64*w+47)+1-(body.steps+2+(rs.length*(64*w+47)+1))) _ actual haRun
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨finalRecord,finalClone,finalRank,hfr,hfc,hfk,actual,hm,?_,?_⟩
    · rw [hf,htf]
      have hpEnd : next+(stream w rs).length=pre.length+(stream w (entry::rs)).length := by
        simp [next,stream]
        omega
      have hoEnd : appended++output w rs=out++output w (entry::rs) := by
        simp [appended,output,a,b,List.append_assoc]
      rw [hpEnd,hoEnd]
    · rw [hs]
      simp only [List.length_cons]
      nlinarith only [hbs,hts]

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
