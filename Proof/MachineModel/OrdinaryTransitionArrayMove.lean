import Proof.MachineModel.OrdinaryTransitionArrayLoop

/-! Move the entire short next-head array back to its source buffer. A real
unary width controls raw-bit copying, including zeros and record delimiters;
the source is erased during the same pass, then all four local heads reset. -/
namespace NearCubicWires.RepairOrdinary.TransitionArrayMove
open LocalBitMultitape RecoveryExecution RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then
    if bits 2 then some ⟨0,![some false,some (bits 0),none],fun _ => .right⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩ else none

def cfg (q : Fin 2) (pre rest backing : List Bool) : Configuration 3 2 :=
  ⟨q,fun _ => pre.length,
    ![List.replicate pre.length false++rest,overlay pre backing,List.replicate (pre.length+rest.length) true]⟩

theorem move_step (pre rest backing : List Bool) (bit : Bool) :
    step raw (cfg 0 pre (bit::rest) backing)=some (cfg 0 (pre++[bit]) rest backing) := by
  have hs : readTapeBit (List.replicate pre.length false++bit::rest) pre.length=bit := by
    simpa using Streaming.read_append (List.replicate pre.length false) rest bit
  have hd : readTapeBit (List.replicate (pre.length+(rest.length+1)) true) pre.length=true := by
    simp [readTapeBit,List.getD]
  simp [step,raw,cfg,Configuration.scanned,hs,hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i
    · have hw := BinaryIncrement.write_prefix (List.replicate pre.length false) rest bit false
      simpa [applyAction,List.replicate_add,List.append_assoc] using hw
    · simpa [applyAction] using overlay_write pre backing bit
    · simp [applyAction]
      omega

theorem stop_step (pre backing : List Bool) :
    step raw (cfg 0 pre [] backing)=some (cfg 1 pre [] backing) := by
  simp [step,raw,cfg,Configuration.scanned,readTapeBit,List.getD]
  rfl

theorem move_prefix (pre rest backing : List Bool) :
    Timed raw (rest.length+1) (cfg 0 pre rest backing) (cfg 1 (pre++rest) [] backing) := by
  induction rest generalizing pre with
  | nil => simpa using Timed.single (by rfl : raw.halted (0 : Fin 2)=false) (stop_step pre backing)
  | cons b bs ih =>
    have h := (Timed.single (by rfl : raw.halted (0 : Fin 2)=false) (move_step pre bs backing b)).trans
      (ih (pre++[b]))
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_run (bits backing : List Bool) (hb : backing.length≤bits.length) :
    ∃ r,run raw (bits.length+1) ![bits,backing,List.replicate bits.length true]=some r ∧
      r.final.tapes=![List.replicate bits.length false,bits,List.replicate bits.length true] ∧
      r.steps=bits.length+1 := by
  obtain ⟨r,hr,hf,hs⟩ := (move_prefix [] bits backing).run (by rfl)
  have hi : cfg 0 [] bits backing=initialConfiguration raw ![bits,backing,List.replicate bits.length true] := by
    apply configuration_ext
    · rfl
    · rfl
    · simp [cfg,initialConfiguration,overlay]
  rw [hi] at hr
  refine ⟨r,hr,?_,hs⟩
  rw [hf]
  simp [cfg,overlay,List.drop_eq_nil_of_le hb]

def machine : Machine 4 4 := Rewind.machine raw

theorem move_ready (bits backing : List Bool) (cap : ℕ)
    (hb : backing.length≤bits.length) (hc : bits.length+1≤cap) :
    ReadyRun machine (2*bits.length+4)
      ![bits,backing,List.replicate bits.length true,List.replicate cap false]
      ![List.replicate bits.length false,bits,List.replicate bits.length true,List.replicate cap false] := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run bits backing hb
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb cap
  have htime : 2*base.steps+2=2*bits.length+4 := by rw [hs]; omega
  rw [htime] at hr
  have hin : Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      (![bits,backing,List.replicate bits.length true] : Fin 3 → List Bool)
      (fun _ : Fin 1 => List.replicate cap false)=
      (![bits,backing,List.replicate bits.length true,List.replicate cap false] : Fin 4 → List Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨r,hr,?_,hh,hsteps.trans htime⟩
  funext i; fin_cases i
  · simpa [hf] using ht 0
  · simpa [hf] using ht 1
  · simpa [hf] using ht 2
  · simpa [hs,max_eq_left hc] using hcounter

end NearCubicWires.RepairOrdinary.TransitionArrayMove
