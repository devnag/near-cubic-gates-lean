import Proof.Amplification.RecoveryDimensions

/-! Copy exactly the produced width from a framed binary source, reading
missing data cells as false and physically writing every output marker and
bit. This pads the short binary input bound as well as the original code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (bits : List Bool) (width : Nat) := (List.range width).map (readTapeBit bits)
@[simp] theorem data_length (bits : List Bool) (width : Nat) : (data bits width).length=width := by simp [data]
theorem data_succ (bits : List Bool) (width : Nat) :
    data bits (width+1)=data bits width++[readTapeBit bits width] := by simp [data,List.range_succ]

theorem frame_data (bits : List Bool) (k : Nat) : readTapeBit (frame bits) (2*k+1)=readTapeBit bits k := by
  induction bits generalizing k with
  | nil=>simp [frame,readTapeBit,List.getD]
  | cons bit bits ih=>
    cases k with
    | zero=>rfl
    | succ k=>simpa [frame,readTapeBit,Nat.mul_add,Nat.add_assoc] using ih k

def loop : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=> ![
    some (if scan 2 then ⟨1,![none,some true,none],![.right,.right,.stay]⟩
      else ⟨2,![none,some false,none],fun _=>.stay⟩),
    some ⟨0,![none,some (scan 0),none],fun _=>.right⟩,none] q

def cfg (bits : List Bool) (width k : Nat) : Configuration 3 3 :=
  ⟨0,![2*k,2*k,k+1],![frame bits,Streaming.marks (data bits k),CompareMachine.word width]⟩
def mid (bits : List Bool) (width k : Nat) : Configuration 3 3 :=
  ⟨1,![2*k+1,2*k+1,k+1],![frame bits,Streaming.marks (data bits k)++[true],CompareMachine.word width]⟩
def final (bits : List Bool) (width : Nat) : Configuration 3 3 :=
  ⟨2,![2*width,2*width,width+1],![frame bits,frame (data bits width),CompareMachine.word width]⟩

theorem marker_step (bits : List Bool) (width k : Nat) (hk : k<width) :
    step loop (cfg bits width k)=some (mid bits width k) := by
  simp [step,loop,cfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [applyAction,mid]
    have h := Streaming.write_append (Streaming.marks (data bits k)) true
    simpa only [Streaming.marks_length,data_length] using h

theorem data_step (bits : List Bool) (width k : Nat) :
    step loop (mid bits width k)=some (cfg bits width (k+1)) := by
  simp [step,loop,mid,Configuration.scanned,frame_data]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,cfg,HeadMove.apply] <;> omega
  · funext i
    fin_cases i <;> simp [applyAction,cfg]
    have h := Streaming.write_append (Streaming.marks (data bits k)++[true]) (readTapeBit bits k)
    have he : (Streaming.marks (data bits k)++[true]).length=2*k+1 := by simp
    rw [he] at h
    rw [h,data_succ,Streaming.marks_append]
    exact List.append_assoc _ _ _

theorem stop_step (bits : List Bool) (width : Nat) :
    step loop (cfg bits width width)=some (final bits width) := by
  simp [step,loop,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,final]
    have h := Streaming.write_append (Streaming.marks (data bits width)) false
    rw [show (Streaming.marks (data bits width)).length=2*width by simp] at h
    rw [h]
    simpa only [List.append_nil,frame] using (Streaming.frame_append (data bits width) []).symm

end NearCubicWires.RepairOrdinary.RecoveryColdPaddedCopy
