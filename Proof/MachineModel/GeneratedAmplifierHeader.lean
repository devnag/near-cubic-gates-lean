import Proof.MachineModel.GeneratedAmplifierSemantics
import Proof.MachineModel.OrdinaryMaskedReset

/-! Isolate the literal framed arity and physically produce its binary-width
driver. Only the two outputs are rewound; the raw payload's table cursor is
retained at the end of the executed header scan. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Header
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
      some ⟨if bits 0 then 1 else 2,![none,some (bits 0),if bits 0 then some true else none],
        ![.right,.right,if bits 0 then .right else .stay]⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0),none],![.right,.right,.stay]⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) (count : ℕ) : Configuration 3 3 :=
  ⟨q,![pos,out.length,count],![source,out,List.replicate count true]⟩

theorem marker_step (b : Bool) (pre tail out : List Bool) (count : ℕ) :
    step raw (cfg 0 (pre++b::tail) pre.length out count)=
      some (cfg (if b then 1 else 2) (pre++b::tail) (pre.length+1) (out++[b]) (count+b.toNat)) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; cases b <;> fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; cases b <;> fin_cases i <;> simp [applyAction,Streaming.write_append,List.replicate_add]

theorem bit_step (b : Bool) (pre tail out : List Bool) (count : ℕ) :
    step raw (cfg 1 (pre++b::tail) pre.length out count)=
      some (cfg 0 (pre++b::tail) (pre.length+1) (out++[b]) count) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem scan_timed (pre bits tail out : List Bool) (count : ℕ) :
    Timed raw (2*bits.length+1)
      (cfg 0 (pre++frame bits++tail) pre.length out count)
      (cfg 2 (pre++frame bits++tail) (pre.length+2*bits.length+1) (out++frame bits) (count+bits.length)) := by
  induction bits generalizing pre out count with
  | nil =>
    simpa only [frame,List.length_nil,Nat.mul_zero,Nat.add_zero,Bool.toNat_false,
      List.append_assoc,List.cons_append,List.nil_append,Bool.false_eq_true,↓reduceIte] using
      Timed.single (by rfl : raw.halted (0 : Fin 3)=false) (marker_step false pre tail out count)
  | cons b bits ih =>
    let source := pre++frame (b::bits)++tail
    have hm : step raw (cfg 0 source pre.length out count)=
        some (cfg 1 source (pre.length+1) (out++[true]) (count+1)) := by
      simpa [source,frame,List.append_assoc] using marker_step true pre (b::frame bits++tail) out count
    have hb : step raw (cfg 1 source (pre.length+1) (out++[true]) (count+1))=
        some (cfg 0 source (pre.length+2) (out++[true,b]) (count+1)) := by
      simpa [source,frame,List.append_assoc] using bit_step b (pre++[true]) (frame bits++tail) (out++[true]) (count+1)
    have he : (pre++[true,b])++frame bits++tail=source := by simp [source,frame,List.append_assoc]
    have ht := ih (pre++[true,b]) (out++[true,b]) (count+1)
    rw [he] at ht
    have hp : (pre++[true,b]).length=pre.length+2 := by simp
    rw [hp] at ht
    have h := (Timed.single (by rfl : raw.halted (0 : Fin 3)=false) hm).trans
      ((Timed.single (by rfl : raw.halted (1 : Fin 3)=false) hb).trans ht)
    have htime : 1+(1+(2*bits.length+1))=2*(b::bits).length+1 := by simp; omega
    have hpos : pre.length+2+2*bits.length+1=pre.length+2*(b::bits).length+1 := by simp; omega
    rw [htime,hpos] at h
    simpa [source,frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def selected (i : Fin 3) : Bool := decide (i≠0)
def machine := MaskedReset.machine raw selected
def entry (source : List Bool) (pos : ℕ) := Rewind.recording (cfg 0 source pos [] 0) 0
def finished (source : List Bool) (pos : ℕ) (bits : List Bool) : Configuration 4 5 :=
  ⟨4,![pos+2*bits.length+1,0,0,0],![source,frame bits,List.replicate bits.length true,
    List.replicate (2*bits.length+1) false]⟩

theorem header_run (pre bits tail : List Bool) :
    ∃ r,runFrom machine (4*bits.length+4) (entry (pre++frame bits++tail) pre.length)=some r ∧
      r.final=finished (pre++frame bits++tail) pre.length bits ∧ r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hf,hs⟩ := (scan_timed pre bits tail [] 0).run (by rfl)
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    rw [hf,hs]
    fin_cases i <;> simp [selected] at hi
    all_goals simp [cfg]
    omega
  obtain ⟨r,hr,hrf,hrs,_⟩ := MaskedReset.reset_run raw selected _ _ base hb hh
  have ht : 2*base.steps+2=4*bits.length+4 := by rw [hs]; omega
  rw [ht] at hr hrs
  refine ⟨r,hr,?_,hrs⟩
  rw [hrf,hf,hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,selected,cfg,finished,Fin.addCases]
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,finished,Fin.addCases]

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Header
