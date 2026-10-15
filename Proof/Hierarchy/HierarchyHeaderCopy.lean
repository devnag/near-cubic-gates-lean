import Proof.Hierarchy.HierarchyHeaderKernel

/-! Actual framed-field traversal and zero padding after the third header
field. The paid length driver advances together with every output bit. -/
namespace NearCubicWires.RepairOrdinary.HierarchyHeader
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem update_twice (pos : Fin 3 → ℕ) (j : Fin 3) (a b : ℕ) :
    Function.update (Function.update pos j a) j b=Function.update pos j b := by
  funext i
  by_cases hi : i=j
  · subst i; simp [Function.update]
  · simp [Function.update,hi]

theorem copy_pair (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out pre bits : List Bool) (j : Fin 3) (b : Bool)
    (hsource : source j=pre++frame (b::bits)) (hpos : pos j=pre.length) :
    Timed raw 2 (config (marker j) N source pos out)
      (config (marker j) N source (Function.update pos j (pre.length+2)) (out++[true,b])) := by
  have hread : readTapeBit (source j) (pos j)=true := by
    rw [hsource,hpos]
    exact Streaming.read_append pre (b::frame bits) true
  have hfirst := marker_true N source pos out j hread
  have hsecondread : readTapeBit (source j) ((Function.update pos j (pos j+1)) j)=b := by
    simp only [Function.update_self,hpos,hsource]
    simpa [frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame bits) b
  have hsecond := payload_step N source (Function.update pos j (pos j+1)) (out++[true]) j b hsecondread
  have hp := (Timed.single (by fin_cases j <;> rfl) hfirst).trans
    (Timed.single (by fin_cases j <;> rfl) hsecond)
  simpa [Function.update_self,update_twice,hpos,List.append_assoc] using hp

theorem copy_end (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out pre : List Bool) (j : Fin 3) (hsource : source j=pre++frame []) (hpos : pos j=pre.length) :
    Timed raw 1 (config (marker j) N source pos out)
      (config (following j) N source (Function.update pos j (pre.length+1)) (out++[false])) := by
  have hread : readTapeBit (source j) (pos j)=false := by
    rw [hsource,hpos]
    exact Streaming.read_append pre [] false
  simpa only [hpos] using Timed.single (by fin_cases j <;> rfl) (marker_false N source pos out j hread)

theorem copy_prefix (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out pre bits : List Bool) (j : Fin 3) (hsource : source j=pre++frame bits) (hpos : pos j=pre.length) :
    Timed raw (2*bits.length+1) (config (marker j) N source pos out)
      (config (following j) N source (Function.update pos j (pre.length+2*bits.length+1)) (out++frame bits)) := by
  induction bits generalizing pre pos out with
  | nil => simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,frame] using copy_end N source pos out pre j hsource hpos
  | cons b bits ih =>
    have hp := copy_pair N source pos out pre bits j b hsource hpos
    have hs : source j=(pre++[true,b])++frame bits := by
      simpa [frame,List.append_assoc] using hsource
    have hi := ih (Function.update pos j (pre.length+2)) (out++[true,b]) (pre++[true,b]) hs
      (by simp)
    have h := hp.trans hi
    simpa [update_twice,frame,List.append_assoc,Nat.mul_add,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using h

theorem padding_step (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (hsmall : out.length<N) :
    step raw (config 6 N source pos out)=some (config 6 N source pos (out++[false])) := by
  have hr : (config 6 N source pos out).scanned 3=true := by
    change readTapeBit (List.replicate N true) out.length=true
    rw [ClockUnaryProduct.read_unary]
    simp [hsmall]
  simp [step,raw,config] at hr ⊢
  rw [hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem padding_stop (N : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (heq : out.length=N) :
    step raw (config 6 N source pos out)=some (config 7 N source pos out) := by
  have hr : (config 6 N source pos out).scanned 3=false := by
    change readTapeBit (List.replicate N true) out.length=false
    rw [ClockUnaryProduct.read_unary,heq]
    simp
  simp [step,raw,config] at hr ⊢
  rw [hr]
  rfl

theorem padding_prefix (N remaining : ℕ) (source : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : List Bool) (heq : out.length+remaining=N) :
    Timed raw (remaining+1) (config 6 N source pos out)
      (config 7 N source pos (out++List.replicate remaining false)) := by
  induction remaining generalizing out with
  | zero =>
    have h := Timed.single (by rfl) (padding_stop N source pos out (by omega))
    simpa using h
  | succ remaining ih =>
    have hp := Timed.single (by rfl) (padding_step N source pos out (by omega))
    have hi := ih (out++[false]) (by simp; omega)
    have h := hp.trans hi
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end NearCubicWires.RepairOrdinary.HierarchyHeader
