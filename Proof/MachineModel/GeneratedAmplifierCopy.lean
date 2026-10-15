import Proof.MachineModel.GeneratedAmplifierSemantics

/-! A framed field is physically unframed while retaining its append cursor.
This is used to keep a whole-input endpoint for locating the trailing address. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copy
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some ⟨if bits 0 then 1 else 2,fun _ => none,![.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _ => .right⟩ else none
def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem marker_step (b : Bool) (pre tail out : List Bool) :
    step machine (cfg 0 (pre++b::tail) pre.length out)=
      some (cfg (if b then 1 else 2) (pre++b::tail) (pre.length+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem bit_step (b : Bool) (pre tail out : List Bool) :
    step machine (cfg 1 (pre++b::tail) pre.length out)=
      some (cfg 0 (pre++b::tail) (pre.length+1) (out++[b])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_timed (pre bits tail out : List Bool) :
    Timed machine (2*bits.length+1)
      (cfg 0 (pre++frame bits++tail) pre.length out)
      (cfg 2 (pre++frame bits++tail) (pre.length+2*bits.length+1) (out++bits)) := by
  induction bits generalizing pre out with
  | nil =>
    simpa only [frame,List.length_nil,Nat.mul_zero,Nat.add_zero,List.append_nil,
      List.append_assoc,List.cons_append,List.nil_append,Bool.false_eq_true,↓reduceIte] using
      Timed.single (by rfl : machine.halted (0 : Fin 3)=false) (marker_step false pre tail out)
  | cons b bits ih =>
    let source := pre++frame (b::bits)++tail
    have hm : step machine (cfg 0 source pre.length out)=some (cfg 1 source (pre.length+1) out) := by
      simpa [source,frame,List.append_assoc] using marker_step true pre (b::frame bits++tail) out
    have hb : step machine (cfg 1 source (pre.length+1) out)=
        some (cfg 0 source (pre.length+2) (out++[b])) := by
      simpa [source,frame,List.append_assoc] using bit_step b (pre++[true]) (frame bits++tail) out
    have he : (pre++[true,b])++frame bits++tail=source := by simp [source,frame,List.append_assoc]
    have ht := ih (pre++[true,b]) (out++[b])
    rw [he] at ht
    have hp : (pre++[true,b]).length=pre.length+2 := by simp
    rw [hp] at ht
    have h := (Timed.single (by rfl : machine.halted (0 : Fin 3)=false) hm).trans
      ((Timed.single (by rfl : machine.halted (1 : Fin 3)=false) hb).trans ht)
    have htime : 1+(1+(2*bits.length+1))=2*(b::bits).length+1 := by simp; omega
    have hpos : pre.length+2+2*bits.length+1=pre.length+2*(b::bits).length+1 := by simp; omega
    rw [htime,hpos] at h
    simpa only [source,List.append_assoc,List.singleton_append] using h

theorem copy_run (pre bits tail out : List Bool) :
    ∃ r,runFrom machine (2*bits.length+1) (cfg 0 (pre++frame bits++tail) pre.length out)=some r ∧
      r.final=cfg 2 (pre++frame bits++tail) (pre.length+2*bits.length+1) (out++bits) ∧
      r.steps=2*bits.length+1 := (copy_timed pre bits tail out).run (by rfl)

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Copy
