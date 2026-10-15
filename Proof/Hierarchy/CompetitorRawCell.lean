import Proof.Hierarchy.CompetitorThresholdDecision

/-! Paid widening of a raw Williams count cell into a framed scalar. The
source cursor advances only over native bits. High zero bits, the delimiter
and all local cursor resets are actual transitions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawCell
open LocalBitMultitape RecoveryExecution Streaming
open StablePartition.Workspace (overlay overlay_write)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 4) (source native width target counter : HeadMove)
    (out scratch : Option Bool) : Action 5 4 :=
  ⟨q,![none,none,none,out,scratch],![source,native,width,target,counter]⟩
def machine : Machine 5 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
      if bits 2 then some (action 1 .stay .stay .stay .right .right (some true) (some true))
      else some (action 2 .stay .stay .stay .right .stay (some false) (some true))
    else if q.val=1 then
      some (action 0 (if bits 1 then .right else .stay) (if bits 1 then .right else .stay)
        .right .right .right (some (bits 1 && bits 0)) (some true))
    else if q.val=2 then
      if bits 4 then some (action 2 .stay .left .left .left .left none (some false))
      else some (action 3 .stay .stay .stay .stay .stay none none)
    else none

def scan (q : Fin 4) (source : List Bool) (pos nativeSize widthSize nativeHead widthHead : ℕ)
    (out backing : List Bool) : Configuration 5 4 :=
  ⟨q,![pos,nativeHead,widthHead,out.length,out.length],
    ![source,List.replicate nativeSize true,List.replicate widthSize true,
      overlay out backing,List.replicate out.length true]⟩
def reset (q : Fin 4) (source : List Bool) (pos nativeSize widthSize nativeHead widthHead : ℕ)
    (out : List Bool) (remaining erased : ℕ) : Configuration 5 4 :=
  ⟨q,![pos,nativeHead,widthHead,remaining,remaining-1],
    ![source,List.replicate nativeSize true,List.replicate widthSize true,out,
      List.replicate remaining true++List.replicate erased false]⟩

theorem marker_step (source out backing : List Bool) (pos b w i j : ℕ) (hj : j<w) :
    step machine (scan 0 source pos b w i j out backing)=
      some (scan 1 source pos b w i j (out++[true]) backing) := by
  have hw : readTapeBit (List.replicate w true) j=true := by
    simp [readTapeBit,hj]
  simp [step,machine,scan,Configuration.scanned,hw]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action,overlay_write,List.replicate_add]

theorem raw_step (pre tail out backing : List Bool) (bit : Bool) (b w i j : ℕ) (hi : i<b) :
    step machine (scan 1 (pre++bit::tail) pre.length b w i j out backing)=
      some (scan 0 (pre++bit::tail) (pre.length+1) b w (i+1) (j+1) (out++[bit]) backing) := by
  have hn : readTapeBit (List.replicate b true) i=true := by
    simp [readTapeBit,hi]
  simp [step,machine,scan,Configuration.scanned,hn,read_append]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action,overlay_write,List.replicate_add]

theorem zero_step (source out backing : List Bool) (pos b w j : ℕ) :
    step machine (scan 1 source pos b w b j out backing)=
      some (scan 0 source pos b w b (j+1) (out++[false]) backing) := by
  have hn : readTapeBit (List.replicate b true) b=false := by simp [readTapeBit]
  simp [step,machine,scan,Configuration.scanned,hn]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action,overlay_write,List.replicate_add]

theorem delimiter_step (source out backing : List Bool) (pos b w i : ℕ) :
    step machine (scan 0 source pos b w i w out backing)=
      some (reset 2 source pos b w i w (overlay (out++[false]) backing) (out.length+1) 0) := by
  have hw : readTapeBit (List.replicate w true) w=false := by simp [readTapeBit]
  simp [step,machine,scan,Configuration.scanned,hw]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply,reset]
  · funext k; fin_cases k <;> simp [applyAction,action,overlay_write,reset,List.replicate_add]

theorem rewind_step (source out : List Bool) (pos b w i j remaining erased : ℕ) :
    step machine (reset 2 source pos b w i j out (remaining+1) erased)=
      some (reset 2 source pos b w (i-1) (j-1) out remaining (erased+1)) := by
  simp [step,machine,reset,Configuration.scanned,read_counter]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action,erase_counter]

theorem stop_step (source out : List Bool) (pos b w erased : ℕ) :
    step machine (reset 2 source pos b w 0 0 out 0 erased)=
      some (reset 3 source pos b w 0 0 out 0 erased) := by
  simp [step,machine,reset,Configuration.scanned,read_zeros]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction,action,HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction,action]

theorem reset_timed (source out : List Bool) (pos b w i j remaining erased : ℕ)
    (hi : i≤remaining) (hj : j≤remaining) :
    Timed machine (remaining+1) (reset 2 source pos b w i j out remaining erased)
      (reset 3 source pos b w 0 0 out 0 (remaining+erased)) := by
  induction remaining generalizing i j erased with
  | zero =>
    have hi0 : i=0 := by omega
    have hj0 : j=0 := by omega
    subst i; subst j
    simpa using Timed.single (by rfl) (stop_step source out pos b w erased)
  | succ remaining ih =>
    have ht := ih (i-1) (j-1) (erased+1) (by omega) (by omega)
    have hs := Timed.single (by rfl) (rewind_step source out pos b w i j remaining erased)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans ht

theorem zeros_timed (source out backing : List Bool) (pos b j pad : ℕ) :
    Timed machine (2*pad+1)
      (scan 0 source pos b (j+pad) b j out backing)
      (reset 2 source pos b (j+pad) b (j+pad)
        (overlay (out++frame (List.replicate pad false)) backing) (out.length+2*pad+1) 0) := by
  induction pad generalizing j out with
  | zero =>
    simpa [frame] using Timed.single (by rfl) (delimiter_step source out backing pos b j b)
  | succ pad ih =>
    have h0 := Timed.single (by rfl) (marker_step source out backing pos b (j+(pad+1)) b j (by omega))
    have h1 := Timed.single (by rfl) (zero_step source (out++[true]) backing pos b (j+(pad+1)) j)
    have ht := ih (out++[true,false]) (j+1)
    have he : j+(pad+1)=(j+1)+pad := by omega
    rw [he] at h0 h1
    have hs := h0.trans (by simpa [List.append_assoc] using h1)
    have hall := hs.trans ht
    convert hall using 1 <;> simp [List.replicate_succ,frame,List.append_assoc,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem raw_timed (pre bits suffix out backing : List Bool) (i j pad : ℕ) :
    Timed machine (2*(bits.length+pad)+1)
      (scan 0 (pre++bits++suffix) pre.length (i+bits.length) (j+bits.length+pad) i j out backing)
      (reset 2 (pre++bits++suffix) (pre.length+bits.length) (i+bits.length) (j+bits.length+pad)
        (i+bits.length) (j+bits.length+pad)
        (overlay (out++frame (bits++List.replicate pad false)) backing) (out.length+2*(bits.length+pad)+1) 0) := by
  induction bits generalizing pre out i j with
  | nil => simpa using zeros_timed (pre++suffix) out backing pre.length i j pad
  | cons bit bits ih =>
    let source := pre++(bit::bits)++suffix
    have hsource : (pre++[bit])++bits++suffix=source := by simp [source,List.append_assoc]
    have hn : i+(bit::bits).length=(i+1)+bits.length := by simp; omega
    have hw : j+(bit::bits).length+pad=(j+1)+bits.length+pad := by simp; omega
    have h0 := Timed.single (by rfl) (marker_step source out backing pre.length
      (i+(bit::bits).length) (j+(bit::bits).length+pad) i j (by simp; omega))
    have h1 := Timed.single (by rfl) (raw_step pre (bits++suffix) (out++[true]) backing bit
      (i+(bit::bits).length) (j+(bit::bits).length+pad) i j (by simp))
    have hs := h0.trans (by simpa [source,List.append_assoc] using h1)
    have ht := ih (pre++[bit]) (out++[true,bit]) (i+1) (j+1)
    rw [hsource] at ht
    rw [hn,hw] at hs
    have hall := hs.trans (by simpa [source,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht)
    convert hall using 1 <;> simp [source,frame,List.append_assoc,Nat.mul_add,
      Nat.add_comm,Nat.add_left_comm]

theorem cell_run (pre bits suffix backing : List Bool) (pad : ℕ)
    (hb : backing.length≤2*(bits.length+pad)+1) :
    ∃ r : ExecutionReceipt 5 4,
      runFrom machine (4*(bits.length+pad)+3)
        (scan 0 (pre++bits++suffix) pre.length bits.length (bits.length+pad) 0 0 [] backing)=some r ∧
      r.final=reset 3 (pre++bits++suffix) (pre.length+bits.length) bits.length (bits.length+pad) 0 0
        (frame (bits++List.replicate pad false)) 0 (2*(bits.length+pad)+1) ∧
      r.steps=4*(bits.length+pad)+3 := by
  have hfirst := raw_timed pre bits suffix [] backing 0 0 pad
  have hover : overlay (frame (bits++List.replicate pad false)) backing=frame (bits++List.replicate pad false) := by
    simp [overlay,List.drop_eq_nil_of_le (by simpa using hb)]
  simp only [List.nil_append,List.length_nil,Nat.zero_add,hover] at hfirst
  have hreset := reset_timed (pre++bits++suffix) (frame (bits++List.replicate pad false))
    (pre.length+bits.length) bits.length (bits.length+pad) bits.length (bits.length+pad)
    (2*(bits.length+pad)+1) 0 (by omega) (by omega)
  have hall := hfirst.trans hreset
  have he : (2*(bits.length+pad)+1)+(2*(bits.length+pad)+1+1)=4*(bits.length+pad)+3 := by omega
  rw [he] at hall
  obtain ⟨r,hr,hf,hs⟩ := hall.run (by rfl)
  exact ⟨r,hr,by simpa using hf,hs⟩

end NearCubicWires.RepairOrdinary.CompetitorRawCell
