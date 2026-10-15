import Proof.CaseAnalysis.RowsGateSupportMeaning

/-! The retained top's arity is physically counted from its same support
bitmap. This short scan supplies a unary count; it does not count integer
magnitudes, inspect a source child, or traverse the circuit again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportCount
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ones : List Bool→ℕ
  | []=>0
  | b::bs=>b.toNat+ones bs
def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q.val=0 then
      if bs 0 then some ⟨1,fun _=>none,![.right,.stay]⟩
      else some ⟨2,fun _=>none,fun _=>.stay⟩
    else if q.val=1 then some ⟨0,![none,if bs 0 then some true else none],
      ![.right,if bs 0 then .right else .stay]⟩
    else none
def cfg (q : Fin 3) (source : List Bool) (pos count : ℕ) : Configuration 2 3:=
  ⟨q,![pos,count],![source,List.replicate count true]⟩

theorem bit_steps (pre tail : List Bool) (bit : Bool) (count : ℕ) :
    Timed machine 2 (cfg 0 (pre++true::bit::tail) pre.length count)
      (cfg 0 (pre++true::bit::tail) (pre.length+2) (count+bit.toNat)):=by
  let source:=pre++true::bit::tail
  have h0:step machine (cfg 0 source pre.length count)=some (cfg 1 source (pre.length+1) count):=by
    simp [step,machine,cfg,source,Configuration.scanned,read_append]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  have hb:readTapeBit source (pre.length+1)=bit:=by
    simpa [source,List.append_assoc] using read_append (pre++[true]) tail bit
  have h1:step machine (cfg 1 source (pre.length+1) count)=
      some (cfg 0 source (pre.length+2) (count+bit.toNat)):=by
    simp [step,machine,cfg,Configuration.scanned,hb]
    apply configuration_ext
    · rfl
    · funext i;cases bit <;> fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;cases bit <;> fin_cases i <;>
        simp [applyAction,List.replicate_add]
  exact (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)

theorem stop_step (pre tail : List Bool) (count : ℕ) :
    step machine (cfg 0 (pre++false::tail) pre.length count)=
      some (cfg 2 (pre++false::tail) pre.length count):=by
  simp [step,machine,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_timed (pre bits tail : List Bool) (count : ℕ) :
    Timed machine (2*bits.length+1) (cfg 0 (pre++frame bits++tail) pre.length count)
      (cfg 2 (pre++frame bits++tail) (pre.length+2*bits.length) (count+ones bits)):=by
  induction bits generalizing pre count with
  | nil=>simpa [frame,ones] using Timed.single (by rfl) (stop_step pre tail count)
  | cons bit bits ih=>
    have hs:=bit_steps pre (frame bits++tail) bit count
    have ht:=ih (pre++[true,bit]) (count+bit.toNat)
    have hall:=hs.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append,
      List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using ht)
    have htime:2+(2*bits.length+1)=2*(bit::bits).length+1:=by simp;omega
    rw [htime] at hall
    simpa [frame,ones,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using hall

def input (bits : List Bool) : Fin 2→List Bool:=![frame bits,[]]
def readyMachine:=Rewind.machine machine
def readyInput (bits : List Bool) : Fin 3→List Bool:=![frame bits,[],[]]

theorem count_ready (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun readyMachine (4*bits.length+4) (readyInput bits) output ∧
      output 0=frame bits ∧ output 1=List.replicate (ones bits) true:=by
  obtain ⟨a,ha,af,as⟩:=(scan_timed [] bits [] 0).run (by rfl)
  have hi:cfg 0 (frame bits) 0 0=initialConfiguration machine (input bits):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  have ha':run machine (2*bits.length+1) (input bits)=some a:=by
    rw [LocalBitMultitape.run,←hi]
    simpa only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] using ha
  obtain ⟨r,hr,rt,_,rh,rs,_⟩:=Rewind.Workspace.reset_workspace machine _ _ a ha' 0
  have he:2*a.steps+2=4*bits.length+4:=by rw [as];omega
  rw [he] at hr rs
  refine ⟨r.final.tapes,⟨r,?_,rfl,rh,rs.le⟩,?_,?_⟩
  · convert hr using 2
    all_goals first | rfl | (funext i;fin_cases i <;> rfl)
  · exact (rt 0).trans (by rw [af];simp [cfg])
  · exact (rt 1).trans (by rw [af];simp [cfg])

theorem ones_filter (bits : List Bool) : ones bits=(bits.filter id).length:=by
  induction bits with
  | nil=>rfl
  | cons b bits ih=>cases b <;> simp [ones,ih,Nat.add_comm]

theorem support_card {n : ℕ} (s : Finset (Fin n)) :
    ones (CloseoutRowsGateSupport.gateMembers s)=s.card:=by
  rw [ones_filter,CloseoutRowsGateSupport.gateMembers,List.ofFn_eq_map,List.filter_map]
  simp only [Function.comp_def,id_eq]
  rw [List.length_map,CloseoutRowsGateSupport.sorted_members,Finset.length_sort]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportCount
