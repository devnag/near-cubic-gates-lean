import Proof.CaseAnalysis.RowsGateSupportField

/-! One complete native signed-weight pass copies exactly the selected
field and folds exactly its zero-outside-support condition. Its two source
cursors remain live, and its reusable scratch head returns to zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RecoveryExecution Streaming StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_timed (compressed member : Bool) (pre tail backing out membership : List Bool)
    (width remaining mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) :
    Timed (machine compressed) (remaining+1)
      (scan (pre++List.replicate remaining true++false::tail) pre.length width backing out membership mp flag)
      (payload 3 (pre++List.replicate remaining true++false::tail)
        (pre.length+remaining+1) (width+remaining) (width+remaining) backing
        (out++selected compressed member (List.replicate remaining true++[false])) membership mp flag):=by
  induction remaining generalizing pre width out with
  | zero => simpa [selected,PCPPQueryField.selected] using
      Timed.single (by rfl) (delimiter_step compressed member pre tail backing out membership width mp flag hm)
  | succ remaining ih =>
    have ht:=ih (pre++[true]) (out++selected compressed member [true]) (width+1)
    have hs:=Timed.single (by rfl)
      (mark_step compressed member pre (List.replicate remaining true++false::tail) backing out membership width mp flag hm)
    have hall:=hs.trans (by simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc] using ht)
    cases compressed <;> cases member <;>
      simpa [selected,keep,PCPPQueryField.selected,List.replicate_succ,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem payload_timed (compressed member : Bool) (pre bits tail backing out membership : List Bool)
    (width mp : ℕ) (flag : Bool) (hm : readTapeBit membership mp=member) (hw : bits.length≤width) :
    Timed (machine compressed) (bits.length+1)
      (payload 3 (pre++bits++tail) pre.length width bits.length backing out membership mp flag)
      (payload 4 (pre++bits++tail) (pre.length+bits.length) width 0 backing
        (out++selected compressed member bits) membership (mp+1) (checked member flag bits)):=by
  induction bits generalizing pre out flag with
  | nil => simpa [selected,PCPPQueryField.selected,checked] using
      Timed.single (by rfl) (stop_step compressed (pre++tail) backing out membership pre.length width mp flag)
  | cons bit bits ih =>
    have ht:=ih (pre++[bit]) (out++selected compressed member [bit]) (flag && (member || !bit))
      (by simp only [List.length_cons] at hw;omega)
    have hs:=Timed.single (by rfl)
      (bit_step compressed member bit pre (bits++tail) backing out membership width bits.length mp flag hm
        (by simp only [List.length_cons] at hw;omega))
    have hall:=hs.trans (by simpa [List.append_assoc,Nat.add_assoc] using ht)
    cases compressed <;> cases member <;>
      simpa [selected,keep,PCPPQueryField.selected,checked,List.append_assoc,Nat.add_assoc,Nat.add_comm] using hall

def weightWord (sign : Bool) (bits : List Bool):=sign::(List.replicate bits.length true++false::bits)

theorem field_run (compressed sign member : Bool) (pre bits tail backing out membership : List Bool)
    (mp : ℕ) (flag : Bool) (hm : readTapeBit membership (mp+1)=member) :
    ∃ actual,runFrom (machine compressed) (2*bits.length+4)
      (cfg 0 (pre++weightWord sign bits++tail) pre.length backing 0 out membership mp flag)=some actual ∧
      actual.final=payload 4 (pre++weightWord sign bits++tail)
        (pre.length+(weightWord sign bits).length) bits.length 0 backing
        (out++selected compressed member (weightWord sign bits)) membership (mp+2) (checked member flag bits) ∧
      actual.steps=2*bits.length+4:=by
  let source:=pre++weightWord sign bits++tail
  let preSign:=pre++[sign]
  let preHeader:=preSign++List.replicate bits.length true++[false]
  have hsource:preSign++List.replicate bits.length true++false::(bits++tail)=source:=by
    simp [preSign,source,weightWord,List.append_assoc]
  have hheader:preHeader++bits++tail=source:=by
    simp [preHeader,preSign,source,weightWord,List.append_assoc]
  have h0:=Timed.single (by rfl) (start_step compressed source backing out membership pre.length mp flag)
  have h1:=Timed.single (by rfl) (sign_step compressed sign member pre
    (List.replicate bits.length true++false::(bits++tail)) backing out membership (mp+1) flag hm)
  have hsigned:pre++sign::(List.replicate bits.length true++false::(bits++tail))=source:=by
    simp [source,weightWord,List.append_assoc]
  rw [hsigned] at h1
  have h2:=header_timed compressed member preSign (bits++tail) backing
    (out++selected compressed member [sign]) membership 0 bits.length (mp+1) flag hm
  rw [hsource] at h2
  have h3:=payload_timed compressed member preHeader bits tail backing
    ((out++selected compressed member [sign])++selected compressed member (List.replicate bits.length true++[false]))
    membership bits.length (mp+1) flag hm (by rfl)
  rw [hheader] at h3
  have hfirst:=h0.trans h1
  have hsecond:=hfirst.trans (by simpa [preSign,List.length_append] using h2)
  have hhead:preHeader.length=pre.length+1+bits.length+1:=by
    simp only [preHeader,preSign,List.length_append,List.length_replicate,List.length_singleton]
  rw [←hhead] at hsecond
  have hall:=hsecond.trans (by simpa only [List.append_assoc] using h3)
  have htime:1+1+(bits.length+1)+(bits.length+1)=2*bits.length+4:=by omega
  rw [htime] at hall
  have hpos:preHeader.length+bits.length=pre.length+(weightWord sign bits).length:=by
    simp [preHeader,preSign,weightWord]
    omega
  rw [hpos] at hall
  have hout:((out++selected compressed member [sign])++
      selected compressed member (List.replicate bits.length true++[false]))++selected compressed member bits=
        out++selected compressed member (weightWord sign bits):=by
    cases compressed <;> cases member <;>
      simp [selected,keep,PCPPQueryField.selected,weightWord,List.append_assoc]
  simp only [List.append_assoc] at hout
  rw [hout,show mp+1+1=mp+2 by omega] at hall
  exact hall.run (by rfl)

theorem checked_iff (member flag : Bool) (bits : List Bool) :
    checked member flag bits=true ↔ flag=true ∧ (member=false → RadixSemantics.value bits=0):=by
  induction bits generalizing flag with
  | nil => simp [checked,RadixSemantics.value]
  | cons bit bits ih =>
    change checked member (flag && (member || !bit)) bits=true ↔_
    rw [ih]
    cases member <;> cases bit <;> simp [RadixSemantics.value]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
