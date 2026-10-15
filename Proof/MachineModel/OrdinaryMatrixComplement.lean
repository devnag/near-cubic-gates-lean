import Proof.MachineModel.OrdinaryWilliamsCeilRealization

/-! A paid fixed-width Boolean complement supplies the second interval
operand used by the right-plane scan. Source and output heads are reset. -/
namespace NearCubicWires.RepairOrdinary.MatrixComplement
open LocalBitMultitape RecoveryExecution StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scanned => if q.val=0 then
      some ⟨if scanned 0 then 1 else 2,![none,some (scanned 0)],fun _ => .right⟩
    else if q.val=1 then some ⟨0,![none,some (!(scanned 0))],fun _ => .right⟩ else none

def cfg (q : Fin 3) (source : List Bool) (position : ℕ) (out backing : List Bool) : Configuration 2 3 :=
  ⟨q,![position,out.length],![source,overlay out backing]⟩

theorem marker_step (pre tail out backing : List Bool) :
    step machine (cfg 0 (pre++true::tail) pre.length out backing)=
      some (cfg 1 (pre++true::tail) (pre.length+1) (out++[true]) backing) := by
  have hr := Streaming.read_append pre tail true
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,overlay_write]

theorem bit_step (pre tail out backing : List Bool) (bit : Bool) :
    step machine (cfg 1 (pre++bit::tail) pre.length out backing)=
      some (cfg 0 (pre++bit::tail) (pre.length+1) (out++[!bit]) backing) := by
  have hr := Streaming.read_append pre tail bit
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,overlay_write]

theorem end_step (pre tail out backing : List Bool) :
    step machine (cfg 0 (pre++false::tail) pre.length out backing)=
      some (cfg 2 (pre++false::tail) (pre.length+1) (out++[false]) backing) := by
  have hr := Streaming.read_append pre tail false
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,overlay_write]

theorem scan_timed (pre bits suffix out backing : List Bool) :
    Timed machine (2*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out backing)
      (cfg 2 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (out++frame (bits.map Bool.not)) backing) := by
  induction bits generalizing pre out with
  | nil => simpa [frame] using Timed.single (by rfl) (end_step pre suffix out backing)
  | cons bit bits ih =>
    have hm := Timed.single (by rfl) (marker_step pre (bit::frame bits++suffix) out backing)
    have hb := Timed.single (by rfl) (bit_step (pre++[true]) (frame bits++suffix) (out++[true]) backing bit)
    have ht := ih (pre++[true,bit]) (out++[true,!bit])
    have hb' : Timed machine 1
        (cfg 1 (pre++frame (bit::bits)++suffix) (pre.length+1) (out++[true]) backing)
        (cfg 0 (pre++frame (bit::bits)++suffix) (pre.length+2) (out++[true,!bit]) backing) := by
      simpa [frame,List.append_assoc,Nat.add_assoc] using hb
    have ht' : Timed machine (2*bits.length+1)
        (cfg 0 (pre++frame (bit::bits)++suffix) (pre.length+2) (out++[true,!bit]) backing)
        (cfg 2 (pre++frame (bit::bits)++suffix) (pre.length+2*(bit::bits).length+1)
          (out++frame ((bit::bits).map Bool.not)) backing) := by
      convert ht using 1 <;> simp [frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add]
    have hm' : Timed machine 1 (cfg 0 (pre++frame (bit::bits)++suffix) pre.length out backing)
        (cfg 1 (pre++frame (bit::bits)++suffix) (pre.length+1) (out++[true]) backing) := by
      simpa [frame,List.append_assoc] using hm
    have whole := hm'.trans (hb'.trans ht')
    convert whole using 1
    simp
    omega

def input (bits backing : List Bool) : Fin 2 → List Bool := ![frame bits,backing]

theorem copy_run (bits backing : List Bool) (hb : backing.length ≤ 2*bits.length+1) :
    ∃ r : ExecutionReceipt 2 3,run machine (2*bits.length+1) (input bits backing)=some r ∧
      r.final.tapes 0=frame bits ∧ r.final.tapes 1=frame (bits.map Bool.not) ∧ r.steps=2*bits.length+1 := by
  have h := scan_timed [] bits [] [] backing
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  have hi : cfg 0 (frame bits) 0 [] backing=initialConfiguration machine (input bits backing) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [cfg,input,initialConfiguration,overlay]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hf]; rfl
  · rw [hf]
    change overlay (frame (bits.map Bool.not)) backing=_
    simp [overlay,List.drop_eq_nil_of_le (by simpa using hb)]

noncomputable def resetMachine := Rewind.machine machine
def resetInput (bits backing : List Bool) : Fin 3 → List Bool := ![frame bits,backing,[]]

theorem reset_run (bits backing : List Bool) (hb : backing.length ≤ 2*bits.length+1) :
    ∃ r : ExecutionReceipt 3 5,run resetMachine (4*bits.length+4) (resetInput bits backing)=some r ∧
      r.final.tapes 0=frame bits ∧ r.final.tapes 1=frame (bits.map Bool.not) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hbRun,h0,h1,hs⟩ := copy_run bits backing hb
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run machine _ (input bits backing) base hbRun
  have hin : Fin.addCases (motive := fun _ : Fin (2+1) => List Bool) (input bits backing) (fun _ : Fin 1 => [])=resetInput bits backing := by
    funext i; fin_cases i <;> rfl
  rw [hin,hs] at hr
  have htime : 2*(2*bits.length+1)+2=4*bits.length+4 := by omega
  rw [htime] at hr
  exact ⟨r,hr,(ht 0).trans h0,(ht 1).trans h1,hh,by omega⟩

end NearCubicWires.RepairOrdinary.MatrixComplement
