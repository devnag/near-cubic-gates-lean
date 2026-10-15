import Proof.PCP.VerifierDecodingBitWidth
import Proof.MachineModel.OrdinaryPartitionWorkspace

/-! Read one fixed-width field from the retained code. The output is framed
for the shared binary comparison kernel. Existing output storage is reused
by actual overwrites; width and output cursors are restored after success. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.FieldMachine
open LocalBitMultitape RepairOrdinary StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 6) (sm om wm : HeadMove) (write : Option Bool := none) : Action 3 6 :=
  ⟨next,![none,write,none],![sm,om,wm]⟩
def machine : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => 4 ≤ state.val
  rule := fun state bits =>
    ![some (if bits 2 then
        if bits 0 then action 1 .right .right .stay (some true) else action 5 .stay .stay .stay
      else action 2 .stay .stay .left (some false)),
      some (action 0 .right .right .right (some (bits 0))),
      some (if bits 2 then action 3 .stay .left .left else action 4 .stay .stay .right),
      some (action 2 .stay .left .stay),none,none] state

def scan (state : Fin 6) (source : List Bool) (pos width count : ℕ)
    (out backing : List Bool) : Configuration 3 6 :=
  ⟨state,![pos,out.length,count+1],![source,overlay out backing,CompareMachine.word width]⟩
def reset (state : Fin 6) (source target : List Bool) (pos width remaining : ℕ) : Configuration 3 6 :=
  ⟨state,![pos,2*remaining,remaining],![source,target,CompareMachine.word width]⟩
def finished (source target : List Bool) (pos width : ℕ) : Configuration 3 6 :=
  ⟨4,![pos,0,1],![source,target,CompareMachine.word width]⟩

@[simp] theorem scan_cells (state : Fin 6) (source : List Bool) (pos width count : ℕ)
    (out backing : List Bool) :
    (scan state source pos width count out backing).tapeCells = source.length+max out.length backing.length+width+1 := by
  simp [scan,Configuration.tapeCells,Fin.sum_univ_succ,CompareMachine.word]
  omega
@[simp] theorem reset_cells (state : Fin 6) (source target : List Bool) (pos width remaining : ℕ) :
    (reset state source target pos width remaining).tapeCells = source.length+target.length+width+1 := by
  simp [reset,Configuration.tapeCells,Fin.sum_univ_succ,CompareMachine.word]
  omega
@[simp] theorem finished_cells (source target : List Bool) (pos width : ℕ) :
    (finished source target pos width).tapeCells = source.length+target.length+width+1 := by
  simp [finished,Configuration.tapeCells,Fin.sum_univ_succ,CompareMachine.word]
  omega

theorem marker_step (pre tail out backing : List Bool) (width count : ℕ) (hc : count < width) :
    step machine (scan 0 (pre++true::tail) pre.length width count out backing) =
      some (scan 1 (pre++true::tail) (pre.length+1) width count (out++[true]) backing) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append,hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,overlay_write]

theorem payload_step (pre tail out backing : List Bool) (bit : Bool) (width count : ℕ) :
    step machine (scan 1 (pre++bit::tail) pre.length width count out backing) =
      some (scan 0 (pre++bit::tail) (pre.length+1) width (count+1) (out++[bit]) backing) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action,overlay_write]

theorem missing_step (pre tail out backing : List Bool) (width count : ℕ) (hc : count < width) :
    step machine (scan 0 (pre++false::tail) pre.length width count out backing) =
      some (scan 5 (pre++false::tail) pre.length width count out backing) := by
  simp [step,machine,scan,Configuration.scanned,Streaming.read_append,hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem finish_step (source backing bits : List Bool) (pos : ℕ) :
    step machine (scan 0 source pos bits.length bits.length (Streaming.marks bits) backing) =
      some (reset 2 source (overlay (frame bits) backing) pos bits.length bits.length) := by
  have he : Streaming.marks bits++[false] = frame bits := by
    have h := Streaming.frame_append bits []
    simpa [RepairOrdinary.frame] using h.symm
  have hw := overlay_write (Streaming.marks bits) backing false
  simp only [Streaming.marks_length, he] at hw
  simp [step,machine,scan,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply,reset]
  · funext i; fin_cases i <;> simp [applyAction,action,reset]
    exact hw

theorem copy_prefix (bits pre tail processed backing : List Bool) (width : ℕ)
    (hw : processed.length+bits.length ≤ width) (hb : backing.length ≤ 2*width+1) :
    let source := pre++Streaming.marks bits++tail
    Prefix machine (source.length+3*width+2) (2*bits.length)
      (scan 0 source pre.length width processed.length (Streaming.marks processed) backing)
      (scan 0 source (pre.length+2*bits.length) width (processed.length+bits.length)
        (Streaming.marks (processed++bits)) backing) := by
  induction bits generalizing pre processed with
  | nil =>
    simp only [Streaming.marks,List.append_nil,List.length_nil,Nat.add_zero,Nat.mul_zero]
    exact Prefix.refl _ (by simp; omega)
  | cons bit bits ih =>
    let source := pre++Streaming.marks (bit::bits)++tail
    let space := source.length+3*width+2
    have he : (pre++[true,bit])++Streaming.marks bits++tail = source := by
      simp [source,Streaming.marks,List.append_assoc]
    have hp := ih (pre++[true,bit]) (processed++[bit]) (by simp at hw ⊢; omega)
    dsimp only at hp
    rw [he] at hp
    have htail : Prefix machine space (2*bits.length)
        (scan 0 source (pre.length+2) width (processed.length+1)
          (Streaming.marks processed++[true,bit]) backing)
        (scan 0 source (pre.length+2*(bit::bits).length) width (processed.length+(bit::bits).length)
          (Streaming.marks (processed++bit::bits)) backing) := by
      simpa [space,Streaming.marks_append,Streaming.marks,List.append_assoc,
        Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp
    have h1 := Prefix.step (by
        simp [space,Streaming.marks_length]
        simp only [List.length_cons] at hw
        omega : (scan 1 source (pre.length+1) width processed.length
          (Streaming.marks processed++[true]) backing).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 6) = false)
      (by simpa [source,Streaming.marks,List.append_assoc] using
        (payload_step (pre++[true]) (Streaming.marks bits++tail) (Streaming.marks processed++[true]) backing bit width processed.length))
      htail
    have h0 := Prefix.step (by
        simp [space,Streaming.marks_length]
        simp only [List.length_cons] at hw
        omega : (scan 0 source pre.length width processed.length (Streaming.marks processed) backing).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 6) = false)
      (by simpa [source,Streaming.marks,List.append_assoc] using
        (marker_step pre (bit::Streaming.marks bits++tail) (Streaming.marks processed) backing width processed.length
          (by simp only [List.length_cons] at hw; omega))) h1
    convert h0 using 1
    simp only [List.length_cons]
    omega

end NearCubicWires.RepairSource.VerifierDecoding.FieldMachine
