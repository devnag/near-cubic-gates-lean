import Proof.Hierarchy.CompetitorPlaneReusable

/-! Copy the native raw count segment of one packet. Its paid unary length
is read physically. Only local heads return; the packet source stays advanced. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketRawLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
    if bits 1 then some ⟨0,![none,none,some (bits 0),some true],fun _ => .right⟩
    else some ⟨1,fun _ => none,![.stay,.stay,.stay,.left]⟩
    else if q.val=1 then
      if bits 3 then some ⟨1,![none,none,none,some false],![.stay,.left,.left,.left]⟩
      else some ⟨2,fun _ => none,fun _ => .stay⟩
    else none
def scan (source : List Bool) (position total : ℕ) (out : List Bool) : Configuration 4 3 :=
  ⟨0,![position,out.length,out.length,out.length],
    ![source,List.replicate total true,out,List.replicate out.length true]⟩
def reset (state : Fin 3) (source out : List Bool) (position total remaining erased : ℕ) : Configuration 4 3 :=
  ⟨state,![position,remaining,remaining,remaining-1],
    ![source,List.replicate total true,out,List.replicate remaining true++List.replicate erased false]⟩

theorem copy_step (pre tail out : List Bool) (bit : Bool) (total : ℕ) (h : out.length<total) :
    step machine (scan (pre++bit::tail) pre.length total out)=
      some (scan (pre++bit::tail) (pre.length+1) total (out++[bit])) := by
  have hread : readTapeBit (List.replicate total true) out.length=true := by simp [readTapeBit,List.getD,h]
  simp only [step,machine,scan,Configuration.scanned,Matrix.cons_val_zero,Matrix.cons_val_one,
    hread,Streaming.read_append,Fin.val_zero,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append,List.replicate_add]

theorem copy_stop (source out : List Bool) (position : ℕ) :
    step machine (scan source position out.length out)=
      some (reset 1 source out position out.length out.length 0) := by
  simp [step,machine,scan,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,reset,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,reset]

theorem copy_run (pre bits suffix out : List Bool) :
    Timed machine (bits.length+1) (scan (pre++bits++suffix) pre.length (out++bits).length out)
      (reset 1 (pre++bits++suffix) (out++bits) (pre.length+bits.length)
        (out++bits).length (out++bits).length 0) := by
  induction bits generalizing pre out with
  | nil => simpa using Timed.single (by rfl) (copy_stop (pre++suffix) out pre.length)
  | cons bit bits ih =>
    have hs := copy_step pre (bits++suffix) out bit (out++bit::bits).length (by simp)
    have ht := ih (pre++[bit]) (out++[bit])
    have he : (out++[bit])++bits=out++bit::bits := by simp [List.append_assoc]
    rw [he] at ht
    have hc : (pre++[bit])++bits++suffix=pre++(bit::bits)++suffix := by simp [List.append_assoc]
    rw [hc] at ht
    have hp : (pre++[bit]).length=pre.length+1 := by simp
    rw [hp] at ht
    simp only [List.append_assoc,List.cons_append] at hs ht
    have joined := Timed.step (by rfl) hs ht
    have hepos : pre.length+1+bits.length=pre.length+(bits.length+1) := by omega
    rw [hepos] at joined
    simpa [List.length_cons,Nat.add_assoc,List.cons_append] using joined

theorem reset_step (source out : List Bool) (position total remaining erased : ℕ) :
    step machine (reset 1 source out position total (remaining+1) erased)=
      some (reset 1 source out position total remaining (erased+1)) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.erase_counter]

theorem reset_stop (source out : List Bool) (position total erased : ℕ) :
    step machine (reset 1 source out position total 0 erased)=
      some (reset 2 source out position total 0 erased) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_zeros]
  rfl

theorem reset_run (source out : List Bool) (position total remaining erased : ℕ) :
    Timed machine (remaining+1) (reset 1 source out position total remaining erased)
      (reset 2 source out position total 0 (remaining+erased)) := by
  induction remaining generalizing erased with
  | zero => simpa using Timed.single (by rfl) (reset_stop source out position total erased)
  | succ remaining ih =>
    have he : remaining+(erased+1)=remaining+1+erased := by omega
    simpa only [Nat.succ_eq_add_one,he] using
      Timed.step (by rfl) (reset_step source out position total remaining erased) (ih (erased+1))

def input (pre bits suffix : List Bool) (D : ℕ) : Configuration 4 3 :=
  ⟨0,![pre.length,0,0,0],![pre++bits++suffix,List.replicate bits.length true,
    List.replicate D false,List.replicate D false]⟩
def output (pre bits suffix : List Bool) (D : ℕ) : Configuration 4 3 :=
  ⟨2,![pre.length+bits.length,0,0,0],![pre++bits++suffix,List.replicate bits.length true,
    ZeroPadding.pad D bits,List.replicate D false]⟩

theorem raw_load_run (pre bits suffix : List Bool) (D : ℕ) (hD : bits.length≤D) :
    ∃ r,runFrom machine (2*bits.length+2) (input pre bits suffix D)=some r ∧
      r.final=output pre bits suffix D ∧ r.steps=2*bits.length+2 := by
  have first := copy_run pre bits suffix []
  simp only [List.nil_append] at first
  have second := reset_run (pre++bits++suffix) bits (pre.length+bits.length) bits.length bits.length 0
  simp only [Nat.add_zero] at second
  obtain ⟨base,hr,hf,hs⟩ := (first.trans second).run (by rfl)
  have htime : bits.length+1+(bits.length+1)=2*bits.length+2 := by omega
  rw [htime] at hr hs
  let caps : Fin 4 → ℕ := ![0,0,D,D]
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine caps _ _ base hr
  have hin : ZeroPadding.config caps (scan (pre++bits++suffix) pre.length bits.length [])=input pre bits suffix D := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,scan,input,ZeroPadding.pad]
  rw [hin] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,reset,output,CompetitorReusableDecision.pad_zeros,max_eq_left hD]

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketRawLoad
