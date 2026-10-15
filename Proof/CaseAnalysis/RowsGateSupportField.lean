import Proof.CaseAnalysis.RowsGateFieldsBudget
import Proof.PCP.PCPPQueryField

/-! The actual retained support bit controls one native signed-weight copy.
The same payload scan checks zero outside support. Scratch is reused by
overwriting its unary bit-length prefix; integer magnitude is never unary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RecoveryExecution Streaming StablePartition.Workspace
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def keep (compressed member : Bool):=!compressed || member
def selected (compressed member : Bool) (bits : List Bool):=
  PCPPQueryField.selected (keep compressed member) bits
def checked (member flag : Bool) (bits : List Bool):=
  bits.foldl (fun ok bit=>ok && (member || !bit)) flag

def machine (compressed : Bool) : Machine 5 5 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==4
  rule:=fun q bs=>if q.val=0 then
      some ⟨1,![none,some false,none,none,none],![.stay,.right,.stay,.right,.stay]⟩
    else if q.val=1 then
      some ⟨2,![none,none,if keep compressed (bs 3) then some (bs 0) else none,none,none],
        ![.right,.stay,if keep compressed (bs 3) then .right else .stay,.stay,.stay]⟩
    else if q.val=2 then
      some ⟨if bs 0 then 2 else 3,
        ![none,some (bs 0),if keep compressed (bs 3) then some (bs 0) else none,none,none],
        ![.right,if bs 0 then .right else .left,if keep compressed (bs 3) then .right else .stay,.stay,.stay]⟩
    else if q.val=3 then
      if bs 1 then some ⟨3,
        ![none,none,if keep compressed (bs 3) then some (bs 0) else none,none,
          some (bs 4 && (bs 3 || !bs 0))],
        ![.right,.left,if keep compressed (bs 3) then .right else .stay,.stay,.stay]⟩
      else some ⟨4,fun _=>none,![.stay,.stay,.stay,.right,.stay]⟩
    else none

def cfg (q : Fin 5) (source : List Bool) (pos : ℕ) (backing : List Bool) (head : ℕ)
    (out membership : List Bool) (mp : ℕ) (flag : Bool) : Configuration 5 5:=
  ⟨q,![pos,head,out.length,mp,0],![source,backing,out,membership,[flag]]⟩
def scan (source : List Bool) (pos width : ℕ) (backing out membership : List Bool)
    (mp : ℕ) (flag : Bool):=
  cfg 2 source pos (overlay (false::List.replicate width true) backing) (width+1) out membership mp flag
def payload (q : Fin 5) (source : List Bool) (pos width head : ℕ)
    (backing out membership : List Bool) (mp : ℕ) (flag : Bool):=
  cfg q source pos (overlay (UnaryTemplate.tape width) backing) head out membership mp flag

theorem start_step (compressed : Bool) (source backing out membership : List Bool) (pos mp : ℕ) (flag : Bool) :
    step (machine compressed) (cfg 0 source pos backing 0 out membership mp flag)=
      some (cfg 1 source pos (overlay [false] backing) 1 out membership (mp+1) flag):=by
  have hw:writeTapeBit backing 0 false=overlay [false] backing:=by
    simpa [overlay] using overlay_write [] backing false
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,hw]

theorem sign_step (compressed sign member : Bool) (pre tail backing out membership : List Bool)
    (mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) :
    step (machine compressed) (cfg 1 (pre++sign::tail) pre.length
      (overlay [false] backing) 1 out membership mp flag)=
      some (scan (pre++sign::tail) (pre.length+1) 0 backing
        (out++selected compressed member [sign]) membership mp flag):=by
  simp [step,machine,cfg,Configuration.scanned,read_append,hm]
  apply configuration_ext
  · rfl
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,HeadMove.apply,scan,cfg,selected,keep,PCPPQueryField.selected]
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,scan,cfg,selected,keep,PCPPQueryField.selected,write_append]

theorem mark_step (compressed member : Bool) (pre tail backing out membership : List Bool)
    (width mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) :
    step (machine compressed) (scan (pre++true::tail) pre.length width backing out membership mp flag)=
      some (scan (pre++true::tail) (pre.length+1) (width+1) backing
        (out++selected compressed member [true]) membership mp flag):=by
  have hw:=overlay_write (false::List.replicate width true) backing true
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,cfg,Configuration.scanned,read_append,hm]
  apply configuration_ext
  · rfl
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,HeadMove.apply,selected,keep,PCPPQueryField.selected]
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,selected,keep,PCPPQueryField.selected,hw,List.replicate_add,write_append]

theorem delimiter_step (compressed member : Bool) (pre tail backing out membership : List Bool)
    (width mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) :
    step (machine compressed) (scan (pre++false::tail) pre.length width backing out membership mp flag)=
      some (payload 3 (pre++false::tail) (pre.length+1) width width backing
        (out++selected compressed member [false]) membership mp flag):=by
  have hw:=overlay_write (false::List.replicate width true) backing false
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,cfg,Configuration.scanned,read_append,hm]
  apply configuration_ext
  · rfl
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,HeadMove.apply,payload,cfg,selected,keep,PCPPQueryField.selected]
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,payload,cfg,selected,keep,PCPPQueryField.selected,hw,UnaryTemplate.tape,write_append]

theorem bit_step (compressed member bit : Bool) (pre tail backing out membership : List Bool)
    (width k mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) (hk : k<width) :
    step (machine compressed) (payload 3 (pre++bit::tail) pre.length width (k+1) backing out membership mp flag)=
      some (payload 3 (pre++bit::tail) (pre.length+1) width k backing
        (out++selected compressed member [bit]) membership mp (flag && (member || !bit))):=by
  have hmagnitude:readTapeBit (overlay (UnaryTemplate.tape width) backing) (k+1)=true:=by
    rw [PCPPQueryField.overlay_read _ _ _ (by simp;omega),UnaryTemplate.tape_mark width k hk]
  have hf:readTapeBit [flag] 0=flag:=rfl
  simp [step,machine,payload,cfg,Configuration.scanned,hmagnitude,read_append,hm,hf]
  apply configuration_ext
  · rfl
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,HeadMove.apply,selected,keep,PCPPQueryField.selected]
  · funext i;cases compressed <;> cases member <;> fin_cases i <;>
      simp [applyAction,selected,keep,PCPPQueryField.selected,write_append,writeTapeBit]

theorem stop_step (compressed : Bool) (source backing out membership : List Bool)
    (pos width mp : ℕ) (flag : Bool) :
    step (machine compressed) (payload 3 source pos width 0 backing out membership mp flag)=
      some (payload 4 source pos width 0 backing out membership (mp+1) flag):=by
  have hz:readTapeBit (overlay (UnaryTemplate.tape width) backing) 0=false:=by
    rw [PCPPQueryField.overlay_read _ _ _ (by simp),UnaryTemplate.tape_zero]
  simp [step,machine,payload,cfg,Configuration.scanned,hz]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
