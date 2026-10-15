import Proof.PCP.PCPPNativeCanonicalTreeStep
import Proof.PCP.PCPStackReady

/-! The existing stack pop overwrites the current original-width code word.
This exact caller extension accounts for its nonblank output backing; the
ordinary machine itself is unchanged and erases every popped stack cell. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
open StablePartition.Workspace (overlay overlay_write)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev machine := PCPStackPop.machine
variable (backing : List Bool)

def cfg (q : Fin 4) (stack : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 4 :=
  ⟨q,![pos,out.length],![stack,overlay out backing]⟩

theorem marker_step (pre out : List Bool) (b : Bool) (z : ℕ) :
    step machine (cfg backing 1 (pre++b::true::List.replicate z false) (pre.length+1) out)=
      some (cfg backing 2 (pre++b::false::List.replicate z false) pre.length (out++[true])) := by
  have hb : readTapeBit (pre++b::true::List.replicate z false) (pre.length+1)=true := by
    simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using
      Streaming.read_append (pre++[b]) (List.replicate z false) true
  simp [step,machine,PCPStackPop.machine,cfg,Configuration.scanned,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,PCPStackPop.action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at (pre++[b]) (List.replicate z false) true false
      simpa [applyAction,PCPStackPop.action,List.append_assoc] using h
    · simpa [applyAction,PCPStackPop.action] using overlay_write out backing true

theorem payload_step (pre out : List Bool) (b : Bool) (z : ℕ) :
    step machine (cfg backing 2 (pre++b::false::List.replicate z false) pre.length out)=
      some (cfg backing 1 (pre++List.replicate (z+2) false) (pre.length-1) (out++[b])) := by
  simp [step,machine,PCPStackPop.machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,PCPStackPop.action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at pre (false::List.replicate z false) b false
      have he : List.replicate (z+2) false=false::false::List.replicate z false := by
        rw [show z+2=2+z by omega,List.replicate_add]
        rfl
      simpa [applyAction,PCPStackPop.action,he] using h
    · simpa [applyAction,PCPStackPop.action] using overlay_write out backing b

theorem finish_step (pre out : List Bool) (z : ℕ) :
    step machine (cfg backing 1 (pre++false::List.replicate z false) pre.length out)=
      some (cfg backing 3 (pre++List.replicate (z+1) false) pre.length (out++[false])) := by
  simp [step,machine,PCPStackPop.machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,PCPStackPop.action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at pre (List.replicate z false) false false
      simpa [applyAction,PCPStackPop.action,List.replicate_succ] using h
    · simpa [applyAction,PCPStackPop.action] using overlay_write out backing false

theorem pop_prefix (bits pre out : List Bool) (z : ℕ) :
    Timed machine (2*bits.length+1)
      (cfg backing 1 (pre++(frame bits).reverse++List.replicate z false)
        (pre.length+(frame bits).length-1) out)
      (cfg backing 3 (pre++List.replicate (2*bits.length+1+z) false) pre.length (out++frame bits)) := by
  induction bits generalizing out z with
  | nil =>
    have h := Timed.single (by rfl : machine.halted (1 : Fin 4)=false) (finish_step backing pre out z)
    simpa [frame,RepairOrdinary.frame,List.append_assoc,Nat.add_comm] using h
  | cons b bs ih =>
    let p := pre++(frame bs).reverse
    have hp : p.length=pre.length+2*bs.length+1 := by simp [p,frame_length]; omega
    have h1 := Timed.single (by rfl : machine.halted (1 : Fin 4)=false) (marker_step backing p out b z)
    have h2 := Timed.single (by rfl : machine.halted (2 : Fin 4)=false) (payload_step backing p (out++[true]) b z)
    have ht := ih (out++[true,b]) (z+2)
    have he : out++[true]++[b]=out++[true,b] := by simp only [List.append_assoc]; rfl
    rw [he] at h2
    have hi : p.length-1=pre.length+(frame bs).length-1 := by simp [p]
    rw [hi] at h2
    have h := h1.trans (h2.trans ht)
    have hsource : pre++(frame (b::bs)).reverse++List.replicate z false=
        p++b::true::List.replicate z false := by
      simp [p,frame,RepairOrdinary.frame,List.append_assoc]
    have hpos : pre.length+(frame (b::bs)).length-1=p.length+1 := by
      rw [frame_length,hp]
      simp only [List.length_cons]
      omega
    have htime : 1+(1+(2*bs.length+1))=2*(b::bs).length+1 := by simp; omega
    have hzeros : 2*bs.length+1+(z+2)=2*(b::bs).length+1+z := by simp; omega
    rw [htime,hzeros] at h
    rw [hsource,hpos]
    simpa only [frame,RepairOrdinary.frame,List.append_assoc,List.cons_append,List.nil_append] using h

theorem start_step (stack out : List Bool) (pos : ℕ) :
    step machine (cfg backing 0 stack pos out)=some (cfg backing 1 stack (pos-1) out) := by
  simp only [step,machine,PCPStackPop.machine,cfg,Fin.val_zero,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem pop_run (bits pre out : List Bool) (z : ℕ) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom machine (2*bits.length+2)
        (cfg backing 0 (pre++(frame bits).reverse++List.replicate z false)
          (pre.length+(frame bits).length) out)=some r ∧
      r.final=cfg backing 3 (pre++List.replicate (2*bits.length+1+z) false) pre.length (out++frame bits) ∧
      r.steps=2*bits.length+2 := by
  have h := (Timed.single (by rfl : machine.halted (0 : Fin 4)=false)
    (start_step backing (pre++(frame bits).reverse++List.replicate z false) out
      (pre.length+(frame bits).length))).trans (pop_prefix backing bits pre out z)
  have he : 1+(2*bits.length+1)=2*bits.length+2 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalStack
