import Proof.Rows.Plan
import Proof.MachineModel.ClockUnaryProduct

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace CapDoublingPass
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- The implicit false cell after the marks is not allocated at each bit.
The old destination is shorter, so the pass overwrites it monotonically. -/
def word (n : Nat) : List Bool := false::List.replicate n true

def machine : Machine 3 8 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==7
  rule := fun s bs =>
    if s=0 then
      if bs 0 then some ⟨1,![none,some true,none],![.stay,.right,.stay]⟩
      else some ⟨2,fun _ => none,fun _ => .stay⟩
    else if s=1 then some ⟨0,![none,some true,none],![.right,.right,.stay]⟩
    else if s=2 then some ⟨3,![none,if bs 2 then some true else none,none],
      ![.stay,if bs 2 then .right else .stay,.stay]⟩
    else if s=3 then some ⟨4,fun _ => none,![.left,.stay,.stay]⟩
    else if s=4 then some ⟨if bs 0 then 4 else 5,fun _ => none,
      ![if bs 0 then .left else .right,.stay,.stay]⟩
    else if s=5 then some ⟨6,fun _ => none,![.stay,.left,.stay]⟩
    else if s=6 then some ⟨if bs 1 then 6 else 7,fun _ => none,
      ![.stay,if bs 1 then .left else .right,.stay]⟩
    else none

def cfg (s : Fin 8) (n v i j : Nat) (source : List Bool) (pos : Nat) :
    Configuration 3 8 := ⟨s,![i,j,pos],![word n,word v,source]⟩

theorem read_word (n k : Nat) : readTapeBit (word n) (k+1)=decide (k<n) :=
  ClockUnaryProduct.read_sentinel n k

theorem write_mark (n k : Nat) (hk : k<n) :
    writeTapeBit (word n) (k+1) true=word n := by
  unfold word
  simp only [writeTapeBit]
  congr 1
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [List.replicate_succ,writeTapeBit]
    | succ k =>
      simpa only [List.replicate_succ,writeTapeBit] using
        congrArg (List.cons true) (ih k (by omega))

theorem write_extend (m k : Nat) :
    writeTapeBit (word (max m k)) (k+1) true=word (max m (k+1)) := by
  by_cases h : k < m
  · rw [max_eq_left (by omega),max_eq_left (by omega)]
    exact write_mark m k h
  · rw [max_eq_right (by omega),max_eq_right (by omega)]
    have hl : (word k).length=k+1 := by simp [word]
    have hw := Streaming.write_append (word k) true
    rw [hl] at hw
    rw [hw]
    simp only [word,List.replicate_succ',List.cons_append]

theorem first_step (n m k : Nat) (source : List Bool) (pos : Nat) (hk : k<n) :
    step machine (cfg 0 n (max m (2*k)) (k+1) (2*k+1) source pos)=
      some (cfg 1 n (max m (2*k+1)) (k+1) (2*k+2) source pos) := by
  have hr : readTapeBit (word n) (k+1)=true := by rw [read_word];simp [hk]
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i;fin_cases i <;> simp [applyAction,write_extend]

theorem second_step (n m k : Nat) (source : List Bool) (pos : Nat) :
    step machine (cfg 1 n (max m (2*k+1)) (k+1) (2*k+2) source pos)=
      some (cfg 0 n (max m (2*(k+1))) (k+2) (2*(k+1)+1) source pos) := by
  have hw : writeTapeBit (word (max m (2*k+1))) (2*k+2) true=
      word (max m (2*(k+1))) := by
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using write_extend m (2*k+1)
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,HeadMove.apply]
    omega
  · funext i;fin_cases i <;> simp [applyAction,hw]

theorem copies (n m k remaining : Nat) (source : List Bool) (pos : Nat)
    (hk : k+remaining=n) :
    Timed machine (2*remaining)
      (cfg 0 n (max m (2*k)) (k+1) (2*k+1) source pos)
      (cfg 0 n (max m (2*n)) (n+1) (2*n+1) source pos) := by
  induction remaining generalizing k with
  | zero =>
    have he : k=n := by omega
    subst k
    exact Timed.refl _ _
  | succ remaining ih =>
    have h := ((Timed.single (by rfl) (first_step n m k source pos (by omega))).trans
      (Timed.single (by rfl) (second_step n m k source pos))).trans
      (ih (k+1) (by omega))
    have ht : 1+1+2*remaining=2*(remaining+1) := by omega
    rw [ht] at h
    exact h

theorem end_copy (n : Nat) (source : List Bool) (pos : Nat) :
    step machine (cfg 0 n (2*n) (n+1) (2*n+1) source pos)=
      some (cfg 2 n (2*n) (n+1) (2*n+1) source pos) := by
  have hr : readTapeBit (word n) (n+1)=false := by rw [read_word];simp
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i;rfl
  · funext i;rfl

theorem append_bit (n : Nat) (source : List Bool) (pos : Nat) (b : Bool)
    (hb : readTapeBit source pos=b) :
    step machine (cfg 2 n (2*n) (n+1) (2*n+1) source pos)=
      some (cfg 3 n (2*n+b.toNat) (n+1) (2*n+b.toNat+1) source pos) := by
  have hw : writeTapeBit (word (2*n)) (2*n+1) true=word (2*n+1) := by
    simpa using write_extend (2*n) (2*n)
  cases b <;> simp [step,machine,cfg,Configuration.scanned,hb]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,hw])

theorem left_start (n v : Nat) (source : List Bool) (pos : Nat) :
    step machine (cfg 3 n v (n+1) (v+1) source pos)=
      some (cfg 4 n v n (v+1) source pos) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem left_return (n v j : Nat) (source : List Bool) (pos : Nat) (hj : j≤n) :
    Timed machine (j+1) (cfg 4 n v j (v+1) source pos)
      (cfg 5 n v 1 (v+1) source pos) := by
  induction j with
  | zero =>
    apply Timed.single (by rfl)
    simp [step,machine,cfg,Configuration.scanned,word,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · rfl
  | succ j ih =>
    have hr : readTapeBit (word n) (j+1)=true := by rw [read_word];simp [show j<n by omega]
    have hs : step machine (cfg 4 n v (j+1) (v+1) source pos)=
        some (cfg 4 n v j (v+1) source pos) := by
      simp [step,machine,cfg,Configuration.scanned,hr]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
      · rfl
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (Timed.single (by rfl) hs).trans (ih (by omega))

theorem right_start (n v : Nat) (source : List Bool) (pos : Nat) :
    step machine (cfg 5 n v 1 (v+1) source pos)=some (cfg 6 n v 1 v source pos) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem right_return (n v j : Nat) (source : List Bool) (pos : Nat) (hj : j≤v) :
    Timed machine (j+1) (cfg 6 n v 1 j source pos) (cfg 7 n v 1 1 source pos) := by
  induction j with
  | zero =>
    apply Timed.single (by rfl)
    simp [step,machine,cfg,Configuration.scanned,word,readTapeBit]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · rfl
  | succ j ih =>
    have hr : readTapeBit (word v) (j+1)=true := by rw [read_word];simp [show j<v by omega]
    have hs : step machine (cfg 6 n v 1 (j+1) source pos)=
        some (cfg 6 n v 1 j source pos) := by
      simp [step,machine,cfg,Configuration.scanned,hr]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
      · rfl
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (Timed.single (by rfl) hs).trans (ih (by omega))

theorem run (n m : Nat) (source : List Bool) (pos : Nat) (b : Bool)
    (hm : m≤n) (hb : readTapeBit source pos=b) :
    Step machine (6*n+7) (![1,1,pos] : Fin 3 → Nat) ![word n,word m,source]
      (![1,1,pos] : Fin 3 → Nat) ![word n,word (2*n+b.toNat),source] := by
  have hc := copies n m 0 n source pos (by omega)
  simp only [Nat.mul_zero,Nat.zero_add,show max m 0=m from max_eq_left (Nat.zero_le m),
    max_eq_right (show m≤2*n by omega)] at hc
  have path := (((((hc.trans (Timed.single (by rfl) (end_copy n source pos))).trans
    (Timed.single (by rfl) (append_bit n source pos b hb))).trans
    (Timed.single (by rfl) (left_start n (2*n+b.toNat) source pos))).trans
    (left_return n (2*n+b.toNat) n source pos (by omega))).trans
    (Timed.single (by rfl) (right_start n (2*n+b.toNat) source pos))).trans
    (right_return n (2*n+b.toNat) (2*n+b.toNat) source pos (by omega))
  obtain ⟨r,hr,hf,hs⟩ := path.run (by rfl)
  have base := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  apply base.enlarge
  cases b <;> simp <;> omega

end CapDoublingPass
