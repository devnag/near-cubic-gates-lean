import Proof.MachineModel.OrdinaryWilliamsPaddingJoin

/-! Read the unary width prefix of a raw dimension header. Both raw width
drivers and the reusable sentinel template are written by this machine;
their creation is not a prepared-input premise. -/
namespace NearCubicWires.RepairOrdinary.MatrixDimensionHeader
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q bits => if q.val = 0 then
      some ⟨1, ![none,none,none,some false], ![.stay,.stay,.stay,.right]⟩
    else if q.val = 1 then
      if bits 0 then
        some ⟨1, ![none,some true,some true,some true], ![.right,.right,.right,.right]⟩
      else some ⟨2, ![none,none,none,some false], ![.right,.stay,.stay,.left]⟩
    else if q.val = 2 then
      if bits 3 then some ⟨2, ![none,none,none,none], ![.stay,.left,.left,.left]⟩
      else some ⟨3, ![none,none,none,none], ![.stay,.stay,.stay,.right]⟩
    else none

def input (source : List Bool) (pos : ℕ) : Configuration 4 4 :=
  ⟨0, ![pos,0,0,0], ![source,[],[],[]]⟩
def scan (source : List Bool) (pos width : ℕ) : Configuration 4 4 :=
  ⟨1, ![pos,width,width,width+1],
    ![source,List.replicate width true,List.replicate width true,
      false :: List.replicate width true]⟩
def reset (source : List Bool) (pos width head : ℕ) : Configuration 4 4 :=
  ⟨2, ![pos,head,head,head],
    ![source,List.replicate width true,List.replicate width true,UnaryTemplate.tape width]⟩
def output (source : List Bool) (pos width : ℕ) : Configuration 4 4 :=
  ⟨3, ![pos,0,0,1],
    ![source,List.replicate width true,List.replicate width true,UnaryTemplate.tape width]⟩

theorem start_step (source : List Bool) (pos : ℕ) :
    step machine (input source pos) = some (scan source pos 0) := by
  simp [step,machine,input]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,scan]
  · funext i; fin_cases i <;> simp [applyAction,scan,writeTapeBit]

theorem mark_step (pre tail : List Bool) (width : ℕ) :
    step machine (scan (pre ++ true :: tail) pre.length width) =
      some (scan (pre ++ true :: tail) (pre.length+1) (width+1)) := by
  have hout : writeTapeBit (false :: List.replicate width true) (width+1) true =
      false :: (List.replicate width true ++ [true]) := by
    simpa using write_append (false :: List.replicate width true) true
  simp [step,machine,scan,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,List.replicate_add,hout]

theorem delimiter_step (pre tail : List Bool) (width : ℕ) :
    step machine (scan (pre ++ false :: tail) pre.length width) =
      some (reset (pre ++ false :: tail) (pre.length+1) width width) := by
  have hout : writeTapeBit (false :: List.replicate width true) (width+1) false =
      false :: (List.replicate width true ++ [false]) := by
    simpa using write_append (false :: List.replicate width true) false
  simp [step,machine,scan,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,reset]
  · funext i; fin_cases i <;> simp [applyAction,reset,UnaryTemplate.tape,hout]

theorem left_step (source : List Bool) (pos width k : ℕ) (hk : k < width) :
    step machine (reset source pos width (k+1)) = some (reset source pos width k) := by
  simp [step,machine,reset,Configuration.scanned,UnaryTemplate.tape_mark width k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem stop_step (source : List Bool) (pos width : ℕ) :
    step machine (reset source pos width 0) = some (output source pos width) := by
  simp [step,machine,reset,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,output]
  · funext i; fin_cases i <;> simp [applyAction,output]

theorem scan_timed (pre tail : List Bool) (width remaining : ℕ) :
    Timed machine (remaining+1)
      (scan (pre ++ List.replicate remaining true ++ false :: tail) pre.length width)
      (reset (pre ++ List.replicate remaining true ++ false :: tail)
        (pre.length+remaining+1) (width+remaining) (width+remaining)) := by
  induction remaining generalizing pre width with
  | zero => simpa using Timed.single (by rfl) (delimiter_step pre tail width)
  | succ remaining ih =>
    have ht := ih (pre ++ [true]) (width+1)
    have hs := Timed.single (by rfl)
      (mark_step pre (List.replicate remaining true ++ false :: tail) width)
    have hall := hs.trans (by
      simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc] using ht)
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem reset_timed (source : List Bool) (pos width k : ℕ) (hk : k ≤ width) :
    Timed machine (k+1) (reset source pos width k) (output source pos width) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop_step source pos width)
  | succ k ih =>
    have hs := Timed.single (by rfl) (left_step source pos width k (by omega))
    simpa [Nat.add_assoc,Nat.add_comm] using hs.trans (ih (by omega))

theorem header_run (pre tail : List Bool) (width : ℕ) :
    ∃ r : ExecutionReceipt 4 4,
      runFrom machine (2*width+3)
        (input (pre ++ List.replicate width true ++ false :: tail) pre.length) = some r ∧
      r.final = output (pre ++ List.replicate width true ++ false :: tail)
        (pre.length+width+1) width ∧ r.steps = 2*width+3 := by
  have h0 := Timed.single (by rfl)
    (start_step (pre ++ List.replicate width true ++ false :: tail) pre.length)
  have h1 := scan_timed pre tail 0 width
  have h2 := reset_timed (pre ++ List.replicate width true ++ false :: tail)
    (pre.length+width+1) width width (by omega)
  have hall := (h0.trans (by simpa using h1)).trans h2
  have he : 1+(width+1)+(width+1) = 2*width+3 := by omega
  rw [he] at hall
  obtain ⟨r,hr,hf,hs⟩ := hall.run (by rfl)
  exact ⟨r,hr,hf,hs⟩

end NearCubicWires.RepairOrdinary.MatrixDimensionHeader
