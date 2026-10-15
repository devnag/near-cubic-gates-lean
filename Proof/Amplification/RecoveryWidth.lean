import Proof.Amplification.RecoveryAllCodeAccepted

/-! Extend the actually counted input length into the canonical certificate
width max(1,n)+2. The empty-input branch writes its extra mark, and the
whole unary driver returns to head1 after a paid left scan. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdWidth
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (n : Nat) := max 1 n+2
def word (n : Nat) := false::List.replicate n true
def cfg (q : Fin 6) (n pos : Nat) : Configuration 1 6 := ⟨q,fun _=>pos,fun _=>word n⟩
def action (q : Fin 6) (write : Option Bool) (move : HeadMove) : Action 1 6 :=
  ⟨q,fun _=>write,fun _=>move⟩
def machine : Machine 1 6 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==5
  rule := fun q bits=> ![
    some (if bits 0 then action 1 none .stay else action 2 (some true) .right),
    some (if bits 0 then action 1 none .right else action 2 none .stay),
    some (action 3 (some true) .right),
    some (action 4 (some true) .left),
    some (if bits 0 then action 4 none .left else action 5 none .right),none] q

theorem mark (n k : Nat) (hk : k<n) : readTapeBit (word n) (k+1)=true := by
  simp [word,readTapeBit,List.getD,hk]
theorem ending (n : Nat) : readTapeBit (word n) (n+1)=false := by
  simp [word,readTapeBit,List.getD]
theorem write_end (n : Nat) : writeTapeBit (word n) (n+1) true=word (n+1) := by
  have h := Streaming.write_append (word n) true
  simpa [word,List.replicate_succ',List.append_assoc] using h

theorem scan_step (n k : Nat) (hk : k<n) : step machine (cfg 1 n (k+1))=some (cfg 1 n (k+2)) := by
  simp [step,machine,cfg,Configuration.scanned,mark n k hk]
  apply configuration_ext
  · rfl
  · rfl
  · rfl

theorem scan_stop (n : Nat) : step machine (cfg 1 n (n+1))=some (cfg 2 n (n+1)) := by
  simp [step,machine,cfg,Configuration.scanned,ending]
  rfl

theorem append_first (n : Nat) : step machine (cfg 2 n (n+1))=some (cfg 3 (n+1) (n+2)) := by
  simp only [step,machine,cfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact write_end n

theorem append_last (n : Nat) : step machine (cfg 3 n (n+1))=some (cfg 4 (n+1) n) := by
  simp only [step,machine,cfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction,action,HeadMove.apply]
  · funext i
    exact write_end n

theorem back_step (n k : Nat) (hk : k<n) : step machine (cfg 4 n (k+1))=some (cfg 4 n k) := by
  simp [step,machine,cfg,Configuration.scanned,mark n k hk]
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction,action,HeadMove.apply]
  · rfl

theorem back_stop (n : Nat) : step machine (cfg 4 n 0)=some (cfg 5 n 1) := by
  simp [step,machine,cfg,Configuration.scanned,word,readTapeBit]
  rfl

theorem scan_trace (n k remaining : Nat) (hk : k+remaining=n) :
    Timed machine (remaining+1) (cfg 1 n (k+1)) (cfg 2 n (n+1)) := by
  induction remaining generalizing k with
  | zero=>
    have he : k=n := by omega
    subst k
    exact Timed.single (by rfl) (scan_stop n)
  | succ remaining ih=>
    have h := (Timed.single (by rfl) (scan_step n k (by omega))).trans (ih (k+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem back_trace (n k : Nat) (hk : k≤n) :
    Timed machine (k+1) (cfg 4 n k) (cfg 5 n 1) := by
  induction k with
  | zero=>exact Timed.single (by rfl) (back_stop n)
  | succ k ih=>
    have h := (Timed.single (by rfl) (back_step n k (by omega))).trans (ih (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem append_trace (n : Nat) : Timed machine 2 (cfg 2 n (n+1)) (cfg 4 (n+2) (n+1)) :=
  (Timed.single (by rfl) (append_first n)).trans (Timed.single (by rfl) (append_last (n+1)))

end NearCubicWires.RepairOrdinary.RecoveryColdWidth
