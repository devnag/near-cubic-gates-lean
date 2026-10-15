import Proof.PCP.PCPStackPush

/-! Pop one reversed framed field from a retained physical stack. Every
popped cell is erased; the resulting zero tail stays allocated and charged.
The stack cursor returns to the previous boundary and the field is appended
in its original order to the output stream. -/
namespace NearCubicWires.RepairOrdinary.PCPStackPop
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 4) (bit : Bool) (move : HeadMove) : Action 2 4 :=
  ⟨q,![some false,some bit],![move,.right]⟩
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then some ⟨1,fun _ => none,![.left,.stay]⟩
    else if q.val=1 then some (if bits 0 then action 2 true .left else action 3 false .stay)
    else if q.val=2 then some (action 1 (bits 0) .left) else none
def cfg (q : Fin 4) (stack : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 4 :=
  ⟨q,![pos,out.length],![stack,out]⟩

theorem marker_step (pre out : List Bool) (b : Bool) (z : ℕ) :
    step machine (cfg 1 (pre++b::true::List.replicate z false) (pre.length+1) out)=
      some (cfg 2 (pre++b::false::List.replicate z false) pre.length (out++[true])) := by
  have hb : readTapeBit (pre++b::true::List.replicate z false) (pre.length+1)=true := by
    simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using
      Streaming.read_append (pre++[b]) (List.replicate z false) true
  simp [step,machine,cfg,Configuration.scanned,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at (pre++[b]) (List.replicate z false) true false
      simpa [applyAction,action,List.append_assoc] using h
    · simpa [applyAction,action] using Streaming.write_append out true

theorem payload_step (pre out : List Bool) (b : Bool) (z : ℕ) :
    step machine (cfg 2 (pre++b::false::List.replicate z false) pre.length out)=
      some (cfg 1 (pre++List.replicate (z+2) false) (pre.length-1) (out++[b])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at pre (false::List.replicate z false) b false
      have he : List.replicate (z+2) false=false::false::List.replicate z false := by
        rw [show z+2=2+z by omega,List.replicate_add]
        rfl
      simpa [applyAction,action,he] using h
    · simpa [applyAction,action] using Streaming.write_append out b

theorem finish_step (pre out : List Bool) (z : ℕ) :
    step machine (cfg 1 (pre++false::List.replicate z false) pre.length out)=
      some (cfg 3 (pre++List.replicate (z+1) false) pre.length (out++[false])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i
    · have h := DimensionTrim.write_at pre (List.replicate z false) false false
      simpa [applyAction,action,List.replicate_succ] using h
    · simpa [applyAction,action] using Streaming.write_append out false

theorem pop_prefix (bits pre out : List Bool) (z : ℕ) :
    Timed machine (2*bits.length+1)
      (cfg 1 (pre++(frame bits).reverse++List.replicate z false)
        (pre.length+(frame bits).length-1) out)
      (cfg 3 (pre++List.replicate (2*bits.length+1+z) false) pre.length (out++frame bits)) := by
  induction bits generalizing out z with
  | nil =>
    have h := Timed.single (by rfl : machine.halted (1 : Fin 4)=false) (finish_step pre out z)
    simpa [frame,RepairOrdinary.frame,List.append_assoc,Nat.add_comm] using h
  | cons b bs ih =>
    let p := pre++(frame bs).reverse
    have hp : p.length=pre.length+2*bs.length+1 := by simp [p,frame_length]; omega
    have h1 := Timed.single (by rfl : machine.halted (1 : Fin 4)=false) (marker_step p out b z)
    have h2 := Timed.single (by rfl : machine.halted (2 : Fin 4)=false) (payload_step p (out++[true]) b z)
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
    step machine (cfg 0 stack pos out)=some (cfg 1 stack (pos-1) out) := by
  simp only [step,machine,cfg,Fin.val_zero,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem pop_run (bits pre out : List Bool) (z : ℕ) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom machine (2*bits.length+2)
        (cfg 0 (pre++(frame bits).reverse++List.replicate z false)
          (pre.length+(frame bits).length) out)=some r ∧
      r.final=cfg 3 (pre++List.replicate (2*bits.length+1+z) false) pre.length (out++frame bits) ∧
      r.steps=2*bits.length+2 := by
  have h := (Timed.single (by rfl : machine.halted (0 : Fin 4)=false)
    (start_step (pre++(frame bits).reverse++List.replicate z false) out
      (pre.length+(frame bits).length))).trans (pop_prefix bits pre out z)
  have he : 1+(2*bits.length+1)=2*bits.length+2 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.PCPStackPop
