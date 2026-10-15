import Proof.MachineModel.OrdinaryMatrixBatchRootCapacityBounds

/-! Literal unary division kernel for the canonical bucket arithmetic.
A quotient mark is written only after a whole positive divisor group. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketDivide
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits =>
    if q.val=0 then some ⟨1,fun _ => none,![.stay,.right,.stay]⟩
    else if q.val=1 then
      if bits 1 then
        if bits 0 then some ⟨1,fun _ => none,![.right,.right,.stay]⟩
        else some ⟨3,fun _ => none,fun _ => .stay⟩
      else some ⟨2,![none,none,some true],![.stay,.left,.right]⟩
    else if q.val=2 then
      if bits 1 then some ⟨2,fun _ => none,![.stay,.left,.stay]⟩
      else some ⟨1,fun _ => none,![.stay,.right,.stay]⟩
    else none
def cfg (q : Fin 4) (n d pos k count : ℕ) : Configuration 3 4 :=
  ⟨q,![pos,k,count],![List.replicate n true,UnaryTemplate.tape d,List.replicate count true]⟩
def input (n d : ℕ) : Fin 3 → List Bool := ![List.replicate n true,UnaryTemplate.tape d,[]]

theorem boot_step (n d : ℕ) : step raw (initialConfiguration raw (input n d))=some (cfg 1 n d 0 1 0) := by
  simp [step,raw,initialConfiguration,input,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
theorem scan_step (n d pos k count : ℕ) (hp : pos<n) (hk : k<d) :
    step raw (cfg 1 n d pos (k+1) count)=some (cfg 1 n d (pos+1) (k+2) count) := by
  have hn : readTapeBit (List.replicate n true) pos=true := by simp [readTapeBit,List.getD,hp]
  have hd := UnaryTemplate.tape_mark d k hk
  simp [step,raw,cfg,Configuration.scanned,hn,hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem emit_step (n d pos count : ℕ) :
    step raw (cfg 1 n d pos (d+1) count)=some (cfg 2 n d pos d (count+1)) := by
  have hd := UnaryTemplate.tape_end d
  have hw : writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true := by
    have h := Streaming.write_append (List.replicate count true) true
    calc writeTapeBit (List.replicate count true) count true=List.replicate count true++[true] := by
          simpa only [List.length_replicate] using h
      _ = List.replicate (count+1) true := by
        change List.replicate count true++List.replicate 1 true=_
        rw [←List.replicate_add]
  simp [step,raw,cfg,Configuration.scanned,hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,hw]
theorem rewind_step (n d pos count k : ℕ) (hk : k<d) :
    step raw (cfg 2 n d pos (k+1) count)=some (cfg 2 n d pos k count) := by
  have hd := UnaryTemplate.tape_mark d k hk
  simp [step,raw,cfg,Configuration.scanned,hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem rewind_done (n d pos count : ℕ) :
    step raw (cfg 2 n d pos 0 count)=some (cfg 1 n d pos 1 count) := by
  have hd : readTapeBit (UnaryTemplate.tape d) 0=false := rfl
  simp [step,raw,cfg,Configuration.scanned,hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
theorem stop_step (n d k count : ℕ) (hk : k<d) :
    step raw (cfg 1 n d n (k+1) count)=some (cfg 3 n d n (k+1) count) := by
  have hn : readTapeBit (List.replicate n true) n=false := by simp [readTapeBit,List.getD]
  have hd := UnaryTemplate.tape_mark d k hk
  simp [step,raw,cfg,Configuration.scanned,hn,hd]
  rfl

theorem scan_prefix (n d pos k count remaining : ℕ) (hp : pos+remaining≤n) (hk : k+remaining≤d) :
    Timed raw remaining (cfg 1 n d pos (k+1) count) (cfg 1 n d (pos+remaining) (k+remaining+1) count) := by
  induction remaining generalizing pos k with
  | zero => simp only [Nat.add_zero]; exact Timed.refl _ _
  | succ remaining ih =>
    have ht := ih (pos+1) (k+1) (by omega) (by omega)
    have hs := Timed.single (by rfl) (scan_step n d pos k count (by omega) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 remaining] using hs.trans ht

theorem rewind_prefix (n d pos count k : ℕ) (hk : k≤d) :
    Timed raw (k+1) (cfg 2 n d pos k count) (cfg 1 n d pos 1 count) := by
  induction k with
  | zero => exact Timed.single (by rfl) (rewind_done n d pos count)
  | succ k ih =>
    have hs := Timed.single (by rfl) (rewind_step n d pos count k (by omega))
    simpa only [Nat.add_comm 1] using hs.trans (ih (by omega))

theorem group_timed (n d pos count : ℕ) (hp : pos+d≤n) :
    Timed raw (2*d+2) (cfg 1 n d pos 1 count) (cfg 1 n d (pos+d) 1 (count+1)) := by
  have hscan := scan_prefix n d pos 0 count d hp (by omega)
  simp only [Nat.zero_add] at hscan
  have hemit := Timed.single (by rfl) (emit_step n d (pos+d) count)
  have hrewind := rewind_prefix n d (pos+d) (count+1) d (Nat.le_refl _)
  have hall := (hscan.trans hemit).trans hrewind
  have ht : d+1+(d+1)=2*d+2 := by omega
  rw [ht] at hall
  exact hall

end NearCubicWires.RepairOrdinary.MatrixBucketDivide
