import Proof.CaseAnalysis.RecoveryRowRandomReset
import Proof.Amplification.RecoveryPaddedCopyMeaning

/-! Print the exact fixed-width original prototype fields directly from
their raw scalar and the paid raw width. Only the output append head is
retained; the existing masked reset restores both read heads. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketPadded
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>![
    some (if scan 2 then ⟨1,![none,some true,none],![.stay,.right,.stay]⟩
      else ⟨2,![none,some false,none],![.stay,.right,.stay]⟩),
    some ⟨0,![none,some (scan 0),none],fun _=>.right⟩,none] q

def cfg (bits out : List Bool) (width k : ℕ) : Configuration 3 3:=
  ⟨0,![k,out.length+2*k,k],
    ![bits,out++Streaming.marks (RecoveryColdPaddedCopy.data bits k),List.replicate width true]⟩
def mid (bits out : List Bool) (width k : ℕ) : Configuration 3 3:=
  ⟨1,![k,out.length+2*k+1,k],
    ![bits,(out++Streaming.marks (RecoveryColdPaddedCopy.data bits k))++[true],List.replicate width true]⟩
def final (bits out : List Bool) (width : ℕ) : Configuration 3 3:=
  ⟨2,![width,(out++frame (RecoveryColdPaddedCopy.data bits width)).length,width],
    ![bits,out++frame (RecoveryColdPaddedCopy.data bits width),List.replicate width true]⟩

theorem marker_step (bits out : List Bool) (width k : ℕ) (hk : k<width) :
    step raw (cfg bits out width k)=some (mid bits out width k) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [applyAction,mid]
    have h:=Streaming.write_append (out++Streaming.marks (RecoveryColdPaddedCopy.data bits k)) true
    simpa only [List.length_append,Streaming.marks_length,RecoveryColdPaddedCopy.data_length,List.append_assoc] using h

theorem data_step (bits out : List Bool) (width k : ℕ) :
    step raw (mid bits out width k)=some (cfg bits out width (k+1)) := by
  simp [step,raw,mid,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,cfg,HeadMove.apply];omega
  · funext i;fin_cases i <;> simp [applyAction,cfg]
    have h:=Streaming.write_append ((out++Streaming.marks (RecoveryColdPaddedCopy.data bits k))++[true]) (readTapeBit bits k)
    have he : ((out++Streaming.marks (RecoveryColdPaddedCopy.data bits k))++[true]).length=out.length+2*k+1:=by simp [Nat.add_assoc]
    rw [he] at h
    simp only [List.append_assoc] at h
    rw [h,RecoveryColdPaddedCopy.data_succ,Streaming.marks_append]
    rfl

theorem stop_step (bits out : List Bool) (width : ℕ) :
    step raw (cfg bits out width width)=some (final bits out width) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,final,frame_length,HeadMove.apply,Nat.add_assoc]
  · funext i;fin_cases i <;> simp [applyAction,final]
    have h:=Streaming.write_append (out++Streaming.marks (RecoveryColdPaddedCopy.data bits width)) false
    rw [show (out++Streaming.marks (RecoveryColdPaddedCopy.data bits width)).length=out.length+2*width by simp] at h
    rw [h]
    have he : Streaming.marks (RecoveryColdPaddedCopy.data bits width)++[false]=
        frame (RecoveryColdPaddedCopy.data bits width):=by
      simpa only [List.append_nil,frame] using
        (Streaming.frame_append (RecoveryColdPaddedCopy.data bits width) []).symm
    rw [List.append_assoc,he]

theorem trace (bits out : List Bool) (width k remaining : ℕ) (hk : k+remaining=width) :
    Timed raw (2*remaining+1) (cfg bits out width k) (final bits out width) := by
  induction remaining generalizing k with
  | zero=>
    have he : k=width:=by omega
    subst k
    exact Timed.single (by rfl) (stop_step bits out width)
  | succ remaining ih=>
    have h:=((Timed.single (by rfl) (marker_step bits out width k (by omega))).trans
      (Timed.single (by rfl) (data_step bits out width k))).trans (ih (k+1) (by omega))
    have he : 1+1+(2*remaining+1)=2*(remaining+1)+1:=by omega
    rw [he] at h
    exact h

def selected (i : Fin 3):=decide (i≠1)
noncomputable def machine:=MaskedReset.machine raw selected
noncomputable def input (bits out : List Bool) (width B : ℕ):=
  ZeroPadding.config (Rewind.Workspace.capacities 3 B)
    (Rewind.recording (cfg bits out width 0) 0)

theorem append_run (bits out : List Bool) (width B : ℕ) (hB : 2*width+2≤B) :
    ∃ r,runFrom machine (4*width+4) (input bits out width B)=some r ∧
      r.steps≤4*width+4 ∧
      r.final.heads=![0,(out++frame (RecoveryColdPaddedCopy.data bits width)).length,0,0] ∧
      r.final.tapes=![bits,out++frame (RecoveryColdPaddedCopy.data bits width),
        List.replicate width true,List.replicate B false] := by
  obtain ⟨p,pr,pf,ps⟩:=(trace bits out width 0 width (by omega)).run (by rfl)
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run raw selected _ B _ p pr
    (by intro i hi;fin_cases i <;> first | rfl | simp [selected] at hi) (by omega)
  have hb : 2*p.steps+2≤4*width+4:=by omega
  have more:=runFrom_moreFuel machine _ (4*width+4-(2*p.steps+2)) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,by omega,?_,?_⟩
  · rw [rf]
    funext i;fin_cases i
    · rfl
    · change p.final.heads 1=_
      rw [pf]
      rfl
    · rfl
    · rfl
  · rw [rf]
    funext i;fin_cases i
    · change p.final.tapes 0=_
      rw [pf]
      rfl
    · change p.final.tapes 1=_
      rw [pf]
      rfl
    · change p.final.tapes 2=_
      rw [pf]
      rfl
    · rfl

theorem padded_append_run (bits out : List Bool) (width B : ℕ)
    (hw : bits.length≤width) (hB : 2*width+2≤B) :
    ∃ r,runFrom machine (4*width+4) (input bits out width B)=some r ∧
      r.steps≤4*width+4 ∧
      r.final.heads=![0,(out++frame (ZeroPadding.pad width bits)).length,0,0] ∧
      r.final.tapes=![bits,out++frame (ZeroPadding.pad width bits),
        List.replicate width true,List.replicate B false] := by
  have h:=append_run bits out width B hB
  simpa only [RecoveryColdPaddedCopy.data_eq_pad bits width hw,ZeroPadding.pad] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketPadded
