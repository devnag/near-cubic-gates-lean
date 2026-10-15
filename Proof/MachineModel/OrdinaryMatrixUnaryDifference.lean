import Proof.MachineModel.OrdinaryMatrixTemplateCopy

/-! Physical unary difference for the padding and crop dimensions. The
smaller prefix is traversed on both inputs, then the remaining marks are
copied into a fresh sentinel template. Both inputs are preserved. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnaryDifference
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
    some ⟨1,![none,none,some false],![.right,.right,.right]⟩
    else if q.val=1 then
      if bits 1 then some ⟨1,fun _ => none,![.right,.right,.stay]⟩
      else some ⟨2,fun _ => none,fun _ => .stay⟩
    else if q.val=2 then
      if bits 0 then some ⟨2,![none,none,some true],![.right,.stay,.right]⟩
      else some ⟨3,![none,none,some false],fun _ => .stay⟩
    else none
def input (n m : ℕ) : Fin 3 → List Bool := ![UnaryTemplate.tape n,UnaryTemplate.tape m,[]]
def skip (n m k : ℕ) : Configuration 3 4 :=
  ⟨1,![k+1,k+1,1],![UnaryTemplate.tape n,UnaryTemplate.tape m,[false]]⟩
def emit (n m k : ℕ) : Configuration 3 4 :=
  ⟨2,![m+k+1,m+1,k+1],![UnaryTemplate.tape n,UnaryTemplate.tape m,false::List.replicate k true]⟩
def output (n m : ℕ) : Configuration 3 4 :=
  ⟨3,![n+1,m+1,n-m+1],![UnaryTemplate.tape n,UnaryTemplate.tape m,UnaryTemplate.tape (n-m)]⟩

theorem start_step (n m : ℕ) :
    step machine (initialConfiguration machine (input n m))=some (skip n m 0) := by
  simp [step,machine,initialConfiguration]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,skip]
  · funext i; fin_cases i <;> simp [applyAction,input,skip,writeTapeBit]

theorem skip_step (n m k : ℕ) (hk : k < m) :
    step machine (skip n m k)=some (skip n m (k+1)) := by
  simp [step,machine,skip,Configuration.scanned,UnaryTemplate.tape_mark m k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction]

theorem switch_step (n m : ℕ) : step machine (skip n m m)=some (emit n m 0) := by
  simp [step,machine,skip,Configuration.scanned,UnaryTemplate.tape_end]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,emit]
  · funext i; fin_cases i <;> simp [applyAction,emit]

theorem emit_step (n m k : ℕ) (hk : m+k<n) :
    step machine (emit n m k)=some (emit n m (k+1)) := by
  have hw : writeTapeBit (false::List.replicate k true) (k+1) true =
      false::(List.replicate k true++[true]) := by simpa using write_append (false::List.replicate k true) true
  simp [step,machine,emit,Configuration.scanned,UnaryTemplate.tape_mark n (m+k) hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction,hw,List.replicate_add]

theorem stop_step (n m : ℕ) (hm : m ≤ n) :
    step machine (emit n m (n-m))=some (output n m) := by
  have he : m+(n-m)=n := Nat.add_sub_of_le hm
  have hw : writeTapeBit (false::List.replicate (n-m) true) (n-m+1) false =
      false::(List.replicate (n-m) true++[false]) := by
    simpa using write_append (false::List.replicate (n-m) true) false
  simp [step,machine,emit,Configuration.scanned,he,UnaryTemplate.tape_end]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,output]
  · funext i; fin_cases i <;> simp [applyAction,output,hw,UnaryTemplate.tape]

theorem skip_timed (n m k rem : ℕ) (he : k+rem=m) :
    Timed machine (rem+1) (skip n m k) (emit n m 0) := by
  induction rem generalizing k with
  | zero =>
    have hk : k=m := by omega
    subst k
    exact Timed.single (by rfl) (switch_step n m)
  | succ rem ih =>
    have ht := (Timed.single (by rfl) (skip_step n m k (by omega))).trans (ih (k+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem emit_timed (n m : ℕ) (hm : m ≤ n) (k rem : ℕ) (he : k+rem=n-m) :
    Timed machine (rem+1) (emit n m k) (output n m) := by
  induction rem generalizing k with
  | zero =>
    have hk : k=n-m := by omega
    subst k
    exact Timed.single (by rfl) (stop_step n m hm)
  | succ rem ih =>
    have ht := (Timed.single (by rfl) (emit_step n m k (by omega))).trans (ih (k+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem difference_run (n m : ℕ) (hm : m ≤ n) :
    ∃ r : ExecutionReceipt 3 4,
      run machine (n+3) (input n m)=some r ∧ r.final=output n m ∧ r.steps=n+3 := by
  have ht := ((Timed.single (by rfl) (start_step n m)).trans
    (skip_timed n m 0 m (by omega))).trans (emit_timed n m hm 0 (n-m) (by omega))
  have htime : 1+(m+1)+(n-m+1)=n+3 := by omega
  rw [htime] at ht
  exact ht.run (by rfl)

def resetMachine := Rewind.machine machine
def resetInput (n m : ℕ) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input n m) (fun _ : Fin 1 => [])

theorem reset_run (n m : ℕ) (hm : m ≤ n) :
    ∃ r : ExecutionReceipt 4 6,
      run resetMachine (2*n+8) (resetInput n m)=some r ∧
      r.final.tapes 0=UnaryTemplate.tape n ∧ r.final.tapes 1=UnaryTemplate.tape m ∧
      r.final.tapes 2=UnaryTemplate.tape (n-m) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=2*n+8 := by
  obtain ⟨base,hb,hf,hs⟩ := difference_run n m hm
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run machine (n+3) (input n m) base hb
  have htime : 2*base.steps+2=2*n+8 := by omega
  rw [htime] at hr hsteps
  refine ⟨r,hr,?_,?_,?_,hh,hsteps⟩
  · exact (ht 0).trans (by rw [hf]; rfl)
  · exact (ht 1).trans (by rw [hf]; rfl)
  · exact (ht 2).trans (by rw [hf]; rfl)

end NearCubicWires.RepairOrdinary.MatrixUnaryDifference
