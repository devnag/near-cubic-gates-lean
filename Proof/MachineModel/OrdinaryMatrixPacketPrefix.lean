import Proof.MachineModel.OrdinaryMatrixVariableWorkspace

/-! Physically append one plane's sign and framed power-of-two factor from
the retained Unary(2t) offset. The global output cursor advances; the driver
returns to head1. No separately prepared exponent or factor is assumed. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketPrefix
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine (negative : Bool) : Machine 2 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==6
  rule := fun q scan => if q.val=0 then
      some ⟨1,![none,some negative],![.stay,.right]⟩
    else if q.val=1 then
      some ⟨if scan 0 then 2 else 3,![none,some true],![if scan 0 then .right else .stay,.right]⟩
    else if q.val=2 then some ⟨1,![none,some false],![.right,.right]⟩
    else if q.val=3 then some ⟨4,![none,some true],![.stay,.right]⟩
    else if q.val=4 then some ⟨5,![none,some false],![.left,.right]⟩
    else if q.val=5 then
      some ⟨if scan 0 then 5 else 6,fun _ => none,![if scan 0 then .left else .right,.stay]⟩
    else none

def cfg (q : Fin 7) (count head : ℕ) (out : List Bool) : Configuration 2 7 :=
  ⟨q,![head,out.length],![UnaryTemplate.tape count,out]⟩
def pairs (n : ℕ) := Streaming.marks (List.replicate n false)
def prefixWord (negative : Bool) (n : ℕ) := [negative]++factor n

theorem pairs_zero : pairs 0=[] := rfl
theorem pairs_succ (n : ℕ) : pairs (n+1)=pairs n++[true,false] := by
  simp [pairs,Streaming.marks,List.replicate_add,List.flatMap_append]
theorem prefix_eq (negative : Bool) (n : ℕ) : prefixWord negative n=[negative]++pairs n++[true,true,false] := by
  simp [prefixWord,factor,Streaming.frame_append,pairs,Streaming.marks,frame]

theorem emit_step (negative bit : Bool) (q q' : Fin 7) (count head : ℕ) (out : List Bool) (move : HeadMove)
    (hr : (machine negative).rule q (cfg q count head out).scanned=some ⟨q',![none,some bit],![move,.right]⟩) :
    step (machine negative) (cfg q count head out)=some (cfg q' count (HeadMove.apply move head) (out++[bit])) := by
  change Option.map (applyAction (cfg q count head out)) ((machine negative).rule q (cfg q count head out).scanned)=_
  rw [hr]
  simp only [Option.map_some,Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,cfg,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,cfg,Streaming.write_append]

theorem pair_step (negative : Bool) (n k : ℕ) (hk : k<n) (out : List Bool) :
    Timed (machine negative) 2 (cfg 1 (2*n) (2*k+1) out)
      (cfg 1 (2*n) (2*(k+1)+1) (out++[true,false])) := by
  have h1 := emit_step negative true 1 2 (2*n) (2*k+1) out .right
    (by simp [machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark (2*n) (2*k) (by omega)])
  have h2 := emit_step negative false 2 1 (2*n) (2*k+2) (out++[true]) .right (by rfl)
  have h := (Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)
  simpa [HeadMove.apply,List.append_assoc,Nat.mul_add,Nat.add_assoc] using h

theorem pairs_run (negative : Bool) (n remaining k : ℕ) (he : k+remaining=n) (out : List Bool) :
    Timed (machine negative) (2*remaining) (cfg 1 (2*n) (2*k+1) (out++pairs k))
      (cfg 1 (2*n) (2*n+1) (out++pairs n)) := by
  induction remaining generalizing k with
  | zero =>
    have hk : k=n := by omega
    subst k
    exact Timed.refl _ _
  | succ remaining ih =>
    have h := pair_step negative n k (by omega) (out++pairs k)
    rw [List.append_assoc,←pairs_succ] at h
    have hj := h.trans (ih (k+1) (by omega))
    simpa [Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hj

theorem back_step (negative : Bool) (n h : ℕ) (hh : h<n) (out : List Bool) :
    step (machine negative) (cfg 5 n (h+1) out)=some (cfg 5 n h out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark n h hh]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem back_stop (negative : Bool) (n : ℕ) (out : List Bool) :
    step (machine negative) (cfg 5 n 0 out)=some (cfg 6 n 1 out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem back_run (negative : Bool) (n h : ℕ) (hh : h≤n) (out : List Bool) :
    Timed (machine negative) (h+1) (cfg 5 n h out) (cfg 6 n 1 out) := by
  induction h with
  | zero => exact Timed.single (by rfl) (back_stop negative n out)
  | succ h ih =>
    have hj := (Timed.single (by rfl) (back_step negative n h (by omega) out)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj

theorem tail_run (negative : Bool) (n : ℕ) (out : List Bool) :
    Timed (machine negative) (2*n+4) (cfg 1 (2*n) (2*n+1) out)
      (cfg 6 (2*n) 1 (out++[true,true,false])) := by
  have h1 := emit_step negative true 1 3 (2*n) (2*n+1) out .stay
    (by simp [machine,cfg,Configuration.scanned])
  have h2 := emit_step negative true 3 4 (2*n) (2*n+1) (out++[true]) .stay (by rfl)
  have h3 := emit_step negative false 4 5 (2*n) (2*n+1) ((out++[true])++[true]) .left (by rfl)
  have h := (Timed.single (by rfl) h1).trans ((Timed.single (by rfl) h2).trans (Timed.single (by rfl) h3))
  have hj := h.trans (back_run negative (2*n) (2*n) (by omega) (((out++[true])++[true])++[false]))
  convert hj using 1 <;> simp [List.append_assoc]; omega

theorem prefix_run (negative : Bool) (n : ℕ) (out : List Bool) : ∃ actual,
    runFrom (machine negative) (4*n+5) (cfg 0 (2*n) 1 out)=some actual ∧
    actual.final=cfg 6 (2*n) 1 (out++prefixWord negative n) ∧ actual.steps=4*n+5 := by
  have hs := emit_step negative negative 0 1 (2*n) 1 out .stay (by rfl)
  have hp := pairs_run negative n n 0 (by omega) (out++[negative])
  simp only [pairs_zero,List.append_nil,Nat.mul_zero,Nat.zero_add] at hp
  have hj := (Timed.single (by rfl) hs).trans (hp.trans (tail_run negative n ((out++[negative])++pairs n)))
  have he : 1+(2*n+(2*n+4))=4*n+5 := by omega
  rw [he] at hj
  have ho : ((out++[negative])++pairs n)++[true,true,false]=out++prefixWord negative n := by
    rw [prefix_eq]; simp only [List.append_assoc]
  rw [ho] at hj
  exact hj.run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixPacketPrefix
