import Proof.Amplification.RecoveryValuationResumed

/-! The actual 2W unary driver used by the retained raw-view scalar skip.
Its source is the already produced W driver; all three heads are reset. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def doubleRaw : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bits=> ![
    some ⟨1,![none,some false],fun _=>.right⟩,
    some (if bits 0 then ⟨2,![none,some true],![.stay,.right]⟩
      else ⟨3,fun _=>none,fun _=>.stay⟩),
    some ⟨1,![none,some true],fun _=>.right⟩,none] q
def doubleCfg (n k : Nat) : Configuration 2 4 :=
  ⟨1,![k+1,2*k+1],![CompareMachine.word n,CompareMachine.word (2*k)]⟩
def doubleMid (n k : Nat) : Configuration 2 4 :=
  ⟨2,![k+1,2*k+2],![CompareMachine.word n,CompareMachine.word (2*k+1)]⟩
def doubleFinal (n : Nat) : Configuration 2 4 :=
  ⟨3,![n+1,2*n+1],![CompareMachine.word n,CompareMachine.word (2*n)]⟩

theorem double_first (n k : Nat) (hk : k<n) :
    step doubleRaw (doubleCfg n k)=some (doubleMid n k) := by
  have hm : readTapeBit (CompareMachine.word n) (k+1)=true := RecoveryColdWidth.mark n k hk
  simp only [step,doubleRaw,doubleCfg,Configuration.scanned,Matrix.cons_val_zero,hm,ite_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · exact RecoveryColdWidth.write_end (2*k)

theorem double_second (n k : Nat) :
    step doubleRaw (doubleMid n k)=some (doubleCfg n (k+1)) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i
    · rfl
    · change 2*k+2+1=2*(k+1)+1
      omega
  · funext i
    fin_cases i
    · rfl
    · change writeTapeBit (CompareMachine.word (2*k+1)) (2*k+2) true=CompareMachine.word (2*(k+1))
      rw [show 2*(k+1)=2*k+1+1 by omega]
      exact RecoveryColdWidth.write_end (2*k+1)

theorem double_end (n : Nat) : step doubleRaw (doubleCfg n n)=some (doubleFinal n) := by
  have hm : readTapeBit (CompareMachine.word n) (n+1)=false := RecoveryColdWidth.ending n
  simp only [step,doubleRaw,doubleCfg,Configuration.scanned,Matrix.cons_val_zero,hm,Bool.false_eq_true,ite_false]
  rfl

theorem double_trace (n k remaining : Nat) (hk : k+remaining=n) :
    Timed doubleRaw (2*remaining+1) (doubleCfg n k) (doubleFinal n) := by
  induction remaining generalizing k with
  | zero=>
    have he : k=n := by omega
    subst k
    exact Timed.single (by rfl) (double_end n)
  | succ remaining ih=>
    have h := ((Timed.single (by rfl) (double_first n k (by omega))).trans
      (Timed.single (by rfl) (double_second n k))).trans (ih (k+1) (by omega))
    rw [show 1+1+(2*remaining+1)=2*(remaining+1)+1 by omega] at h
    exact h

theorem double_raw_run (n : Nat) :
    ∃ r,run doubleRaw (2*n+2) ![CompareMachine.word n,[]]=some r ∧
      r.final=doubleFinal n ∧ r.steps=2*n+2 := by
  have hs : step doubleRaw (initialConfiguration doubleRaw ![CompareMachine.word n,[]])=
      some (doubleCfg n 0) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h := (Timed.single (by rfl) hs).trans (double_trace n 0 n (by omega))
  rw [show 1+(2*n+1)=2*n+2 by omega] at h
  exact h.run (by rfl)

def doubleMachine := Rewind.machine doubleRaw
theorem double_ready (n reset : Nat) :
    ReadyRun doubleMachine (4*n+6)
      ![CompareMachine.word n,[],List.replicate reset false]
      ![CompareMachine.word n,CompareMachine.word (2*n),List.replicate (max reset (2*n+2)) false] := by
  obtain ⟨base,hbase,hf,hsteps⟩ := double_raw_run n
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace doubleRaw (2*n+2)
    ![CompareMachine.word n,[]] base hbase reset
  have he : 2*base.steps+2=4*n+6 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,doubleFinal] using ht 0
    · simpa [hf,doubleFinal] using ht 1
    · simpa [hsteps] using hcounter

end NearCubicWires.RepairOrdinary.RecoveryColdView
