import Proof.CaseAnalysis.RowsGateSupportCount

/-! One physical support scan computes the remaining nonsupport count
and both candidate-touch flags. The flag bits live on owned tapes, so the
scanner has only the existing marker/payload/halt control pattern. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Cell:=Bool×Bool×Bool×Bool
def kept (e : Cell):Bool:=e.2.2.2 && !e.1
def touched (e : Cell):Bool:=e.1 && e.2.1
def current (e : Cell):Bool:=e.1 && e.2.2.1
def masks (xs : List Cell) : Fin 3→List Bool:=![xs.map (fun e=>e.2.1),xs.map (fun e=>e.2.2.1),xs.map (fun e=>e.2.2.2)]
def machine : Machine 7 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q.val=0 then
      some ⟨if bs 0 then 1 else 2,fun _=>none,![.right,.stay,.stay,.stay,.stay,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨0,![none,none,none,none,if bs 3 && !bs 0 then some true else none,
        some (bs 5 || (bs 0 && bs 1)),some (bs 6 || (bs 0 && bs 2))],
        ![.right,.right,.right,.right,if bs 3 && !bs 0 then .right else .stay,.stay,.stay]⟩
    else none

def cfg (state : Fin 3) (source : List Bool) (pos : ℕ) (mask : Fin 3→List Bool)
    (index count : ℕ) (hit cur : Bool):Configuration 7 3:=
  ⟨state,![pos,index,index,index,count,0,0],
    ![source,mask 0,mask 1,mask 2,List.replicate count true,[hit],[cur]]⟩

def prefixedCfg (lead : List Bool) (state : Fin 3) (source : List Bool) (pos : ℕ) (mask : Fin 3→List Bool)
    (index count : ℕ) (hit cur : Bool):Configuration 7 3:=
  ⟨state,![pos,index,index,index,lead.length+count,0,0],
    ![source,mask 0,mask 1,mask 2,lead++List.replicate count true,[hit],[cur]]⟩

theorem write_counter (lead : List Bool) (n : ℕ):
    writeTapeBit (lead++List.replicate n true) (lead.length+n) true=lead++List.replicate (n+1) true:=by
  simpa only [List.length_append,List.length_replicate,List.replicate_add,List.replicate_one,List.append_assoc]
    using write_append (lead++List.replicate n true) true

theorem prefixed_bit_steps (lead : List Bool) (pre tail : List Bool) (e : Cell) (mask : Fin 3→List Bool) (j count : ℕ) (hit cur : Bool)
    (hs:readTapeBit (mask 0) j=e.2.1) (hc:readTapeBit (mask 1) j=e.2.2.1)
    (hr:readTapeBit (mask 2) j=e.2.2.2):
    Timed machine 2 (prefixedCfg lead 0 (pre++true::e.1::tail) pre.length mask j count hit cur)
      (prefixedCfg lead 0 (pre++true::e.1::tail) (pre.length+2) mask (j+1) (count+(kept e).toNat)
        (hit||touched e) (cur||current e)):=by
  let source:=pre++true::e.1::tail
  have h0:step machine (prefixedCfg lead 0 source pre.length mask j count hit cur)=
      some (prefixedCfg lead 1 source (pre.length+1) mask j count hit cur):=by
    simp [step,machine,prefixedCfg,source,Configuration.scanned,read_append]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  have hb:readTapeBit source (pre.length+1)=e.1:=by
    simpa [source,List.append_assoc] using read_append (pre++[true]) tail e.1
  have h1:step machine (prefixedCfg lead 1 source (pre.length+1) mask j count hit cur)=
      some (prefixedCfg lead 0 source (pre.length+2) mask (j+1) (count+(kept e).toNat)
        (hit||touched e) (cur||current e)):=by
    simp [step,machine,prefixedCfg,Configuration.scanned,hb,hs,hc,hr,kept,touched,current]
    apply configuration_ext
    · rfl
    · funext i;rcases e with ⟨b,s,c,r⟩;cases b <;> cases r <;> fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
    · funext i;rcases e with ⟨b,s,c,r⟩;cases b <;> cases r <;> fin_cases i <;>
        simp [applyAction,write_counter,readTapeBit,writeTapeBit]
  exact (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)

theorem prefixed_stop_step (lead : List Bool) (pre tail : List Bool) (mask : Fin 3→List Bool) (j count : ℕ) (hit cur : Bool):
    step machine (prefixedCfg lead 0 (pre++false::tail) pre.length mask j count hit cur)=
      some (prefixedCfg lead 2 (pre++false::tail) (pre.length+1) mask j count hit cur):=by
  simp [step,machine,prefixedCfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem bit_steps (pre tail : List Bool) (e : Cell) (mask : Fin 3→List Bool) (j count : ℕ) (hit cur : Bool)
    (hs:readTapeBit (mask 0) j=e.2.1) (hc:readTapeBit (mask 1) j=e.2.2.1)
    (hr:readTapeBit (mask 2) j=e.2.2.2):
    Timed machine 2 (cfg 0 (pre++true::e.1::tail) pre.length mask j count hit cur)
      (cfg 0 (pre++true::e.1::tail) (pre.length+2) mask (j+1) (count+(kept e).toNat)
        (hit||touched e) (cur||current e)):=by
  simpa only [prefixedCfg,cfg,List.length_nil,List.nil_append,Nat.zero_add] using
    prefixed_bit_steps [] pre tail e mask j count hit cur hs hc hr

theorem stop_step (pre tail : List Bool) (mask : Fin 3→List Bool) (j count : ℕ) (hit cur : Bool):
    step machine (cfg 0 (pre++false::tail) pre.length mask j count hit cur)=
      some (cfg 2 (pre++false::tail) (pre.length+1) mask j count hit cur):=by
  simpa only [prefixedCfg,cfg,List.length_nil,List.nil_append,Nat.zero_add] using
    prefixed_stop_step [] pre tail mask j count hit cur

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
