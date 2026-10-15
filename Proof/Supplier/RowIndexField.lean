import Proof.Supplier.RowCachedCoordinateBounds

/-! An ordered occurrence-index field is raw unary with a false delimiter.
Its reader physically writes the existing sentinel template, retaining the
source cursor and every occurrence. This is an internal controller stream. -/
namespace NearCubicWires.RepairOrdinary.RowIndexField
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (n : ℕ) := List.replicate n true++[false]
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
    some ⟨1,![none,some false],![.stay,.right]⟩
    else if q.val=1 then some (if bits 0 then
      ⟨1,![none,some true],![.right,.right]⟩
      else ⟨2,![none,some false],![.right,.left]⟩)
    else if q.val=2 then some (if bits 1 then
      ⟨2,fun _=>none,![.stay,.left]⟩ else ⟨3,fun _=>none,![.stay,.right]⟩)
    else none
def entry (source : List Bool) (pos : ℕ) : Configuration 2 4 :=
  ⟨0,![pos,0],![source,[]]⟩
def scan (source : List Bool) (pos count : ℕ) : Configuration 2 4 :=
  ⟨1,![pos,count+1],![source,false::List.replicate count true]⟩
def back (state : Fin 4) (source : List Bool) (pos n k : ℕ) : Configuration 2 4 :=
  ⟨state,![pos,k],![source,UnaryTemplate.tape n]⟩

theorem boot_step (source : List Bool) (pos : ℕ) :
    step machine (entry source pos)=some (scan source pos 0) := by
  simp [step,machine,entry]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem true_step (pre tail : List Bool) (count : ℕ) :
    step machine (scan (pre++true::tail) pre.length count)=
      some (scan (pre++true::tail) (pre.length+1) (count+1)) := by
  have hw := write_append (false::List.replicate count true) true
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction,hw,List.replicate_add]

theorem delimiter_step (pre tail : List Bool) (n : ℕ) :
    step machine (scan (pre++false::tail) pre.length n)=
      some (back 2 (pre++false::tail) (pre.length+1) n n) := by
  have hw := write_append (false::List.replicate n true) false
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,back]
  · funext i; fin_cases i <;> simp [applyAction,back,hw,UnaryTemplate.tape]

theorem scan_timed (remaining : ℕ) (pre tail : List Bool) (count : ℕ) :
    let source := pre++word remaining++tail
    Timed machine (remaining+1) (scan source pre.length count)
      (back 2 source (pre.length+remaining+1) (count+remaining) (count+remaining)) := by
  induction remaining generalizing pre count with
  | zero => simpa [word] using Timed.single (by rfl) (delimiter_step pre tail count)
  | succ remaining ih =>
    have ht := ih (pre++[true]) (count+1)
    dsimp only at ht ⊢
    have hw : (pre++[true])++word remaining++tail=pre++word (remaining+1)++tail := by
      simp [word,List.replicate_succ,List.append_assoc]
    rw [hw] at ht
    simp only [List.length_append,List.length_cons,List.length_nil] at ht
    have hs := true_step pre (word remaining++tail) count
    have hsword : pre++true::(word remaining++tail)=pre++word (remaining+1)++tail := by
      simp [word,List.replicate_succ,List.append_assoc]
    rw [hsword] at hs
    have h := (Timed.single (by rfl) hs).trans ht
    simpa [List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem back_step (source : List Bool) (pos n k : ℕ) (hk : k<n) :
    step machine (back 2 source pos n (k+1))=some (back 2 source pos n k) := by
  simp [step,machine,back,Configuration.scanned,UnaryTemplate.tape_mark n k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (source : List Bool) (pos n : ℕ) :
    step machine (back 2 source pos n 0)=some (back 3 source pos n 1) := by
  simp [step,machine,back,Configuration.scanned,UnaryTemplate.tape_zero]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem back_timed (source : List Bool) (pos n k : ℕ) (hk : k≤n) :
    Timed machine (k+1) (back 2 source pos n k) (back 3 source pos n 1) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop_step source pos n)
  | succ k ih => exact Timed.step (by rfl) (back_step source pos n k (by omega)) (ih (by omega))

theorem field_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom machine (2*n+3) (entry (pre++word n++tail) pre.length)=some r ∧
      r.final=back 3 (pre++word n++tail) (pre.length+n+1) n 1 ∧ r.steps=2*n+3 := by
  have hs := scan_timed n pre tail 0
  simp only [Nat.zero_add] at hs
  have h := ((Timed.single (by rfl) (boot_step (pre++word n++tail) pre.length)).trans hs).trans
    (back_timed (pre++word n++tail) (pre.length+n+1) n n (by rfl))
  have ht : 1+(n+1)+(n+1)=2*n+3 := by omega
  rw [ht] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.RowIndexField
