import Proof.Assembly.AppendOutputLength

namespace NearCubicWires.RepairOrdinary.AppendFrameKernel
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some (if bits 1 then ⟨1,![none,none,some true],![.stay,.stay,.right]⟩
        else ⟨2,![none,none,some false],fun _ => .stay⟩)
    else if q.val=1 then some ⟨0,![none,none,some (bits 0)],![.right,.right,.right]⟩ else none

def cfg (q : Fin 3) (bits : List Bool) (pos : ℕ) (out : List Bool) : Configuration 3 3 :=
  ⟨q,![pos,pos,out.length],![bits,List.replicate bits.length true,out]⟩

theorem marker_step (pre : List Bool) (b : Bool) (bs out : List Bool) :
    step raw (cfg 0 (pre++b::bs) pre.length out)=some (cfg 1 (pre++b::bs) pre.length (out++[true])) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem bit_step (pre : List Bool) (b : Bool) (bs out : List Bool) :
    step raw (cfg 1 (pre++b::bs) pre.length out)=some (cfg 0 (pre++b::bs) (pre.length+1) (out++[b])) := by
  have hr := Streaming.read_append pre bs b
  simp [step,raw,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem loop (pre bits out : List Bool) :
    Timed raw (2*bits.length) (cfg 0 (pre++bits) pre.length out)
      (cfg 0 (pre++bits) (pre.length+bits.length) (out++Streaming.marks bits)) := by
  induction bits generalizing pre out with
  | nil => simpa [Streaming.marks] using Timed.refl raw (cfg 0 pre pre.length out)
  | cons b bs ih =>
    have ht := ih (pre++[b]) (out++[true,b])
    have he : (pre++[b])++bs=pre++b::bs := by simp
    rw [he] at ht
    have hout : out++[true,b]=(out++[true])++[b] := by simp
    rw [hout] at ht
    simp only [List.length_append,List.length_singleton] at ht
    have h := (Timed.single (by rfl : raw.halted (0 : Fin 3)=false) (marker_step pre b bs out)).trans
      ((Timed.single (by rfl : raw.halted (1 : Fin 3)=false) (bit_step pre b bs (out++[true]))).trans ht)
    have htime : 1+(1+2*bs.length)=2*(b::bs).length := by simp; omega
    rw [htime] at h
    simpa [Streaming.marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def final (bits : List Bool) : Configuration 3 3 :=
  ⟨2,![bits.length,bits.length,2*bits.length],![bits,List.replicate bits.length true,frame bits]⟩

theorem raw_run (bits : List Bool) : ∃ r,
    run raw (2*bits.length+1) ![bits,List.replicate bits.length true,[]]=some r ∧
      r.final=final bits ∧ r.steps=2*bits.length+1 := by
  have hp := loop [] bits []
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hp
  have hf : step raw (cfg 0 bits bits.length (Streaming.marks bits))=some (final bits) := by
    simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,final]
    · funext i; fin_cases i
      · rfl
      · rfl
      · have h := Streaming.write_append (Streaming.marks bits) false
        have he : Streaming.marks bits++[false]=frame bits := by
          simpa only [List.append_nil,RepairOrdinary.frame] using (Streaming.frame_append bits []).symm
        simpa [applyAction,final,he] using h
  have h := hp.trans (Timed.single (by rfl : raw.halted (0 : Fin 3)=false) hf)
  obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by rfl)
  have hi : cfg 0 bits 0 []=initialConfiguration raw ![bits,List.replicate bits.length true,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hfinal,hsteps⟩

def machine := Rewind.machine raw
def input (bits : List Bool) : Fin 4 → List Bool := ![bits,List.replicate bits.length true,[],[]]
def output (bits : List Bool) : Fin 4 → List Bool :=
  ![bits,List.replicate bits.length true,frame bits,List.replicate (2*bits.length+1) false]

theorem ready (bits : List Bool) : ClockJoin.ReadyRun machine (4*bits.length+4) (input bits) (output bits) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run bits
  obtain ⟨r,hr,ht,hcount,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![bits,List.replicate bits.length true,[]] (fun _ : Fin 1 => []))=input bits := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![bits,List.replicate bits.length true,[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have he : 2*base.steps+2=4*bits.length+4 := by omega
  rw [he] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i; fin_cases i
  · simpa [output,hf,final] using ht 0
  · simpa [output,hf,final] using ht 1
  · simpa [output,hf,final] using ht 2
  · simpa [output,hs] using hcount

end NearCubicWires.RepairOrdinary.AppendFrameKernel
