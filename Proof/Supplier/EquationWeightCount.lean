import Proof.Supplier.EquationHeaderBoot

/-! Actual weight-count production from the parsed d template and odd bit.
The result is the sentinel driver for 2*d-odd.toNat. -/
namespace NearCubicWires.RepairOrdinary.EquationWeightCount
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bs =>
    if q.val=0 then some ⟨1,![none,none,some false],![.right,.stay,.right]⟩
    else if q.val=1 then some
      (if bs 0 then
        if bs 1 then ⟨3,![none,none,some true],![.right,.stay,.right]⟩
        else ⟨2,![none,none,some true],![.stay,.stay,.right]⟩
      else ⟨4,fun _ => none,fun _ => .stay⟩)
    else if q.val=2 then some ⟨3,![none,none,some true],![.right,.stay,.right]⟩
    else if q.val=3 then some
      (if bs 0 then ⟨2,![none,none,some true],![.stay,.stay,.right]⟩
      else ⟨4,fun _ => none,fun _ => .stay⟩)
    else none
def cfg (q : Fin 5) (n : ℕ) (odd : Bool) (pos : ℕ) (out : List Bool) : Configuration 3 5 :=
  ⟨q,![pos,0,out.length],![UnaryTemplate.tape n,[odd],out]⟩

theorem read_mark (n p : ℕ) :
    readTapeBit (UnaryTemplate.tape n) (p+1)=decide (p<n) := by
  simp [UnaryTemplate.tape,readTapeBit,List.getElem?_append]
  split_ifs <;> simp_all

theorem second (n : ℕ) (odd : Bool) (pos : ℕ) (out : List Bool) :
    step raw (cfg 2 n odd pos out)=some (cfg 3 n odd (pos+1) (out++[true])) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem pair (n : ℕ) (odd : Bool) (pos : ℕ) (out : List Bool) (hp : pos<n) :
    Timed raw 2 (cfg 3 n odd (pos+1) out)
      (cfg 3 n odd (pos+2) (out++[true,true])) := by
  have hs : step raw (cfg 3 n odd (pos+1) out)=some (cfg 2 n odd (pos+1) (out++[true])) := by
    simp [step,raw,cfg,Configuration.scanned,read_mark,hp]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]
  have h := (Timed.single (by rfl) hs).trans (Timed.single (by rfl) (second n odd (pos+1) (out++[true])))
  simpa [List.append_assoc] using h

theorem stop (n : ℕ) (odd : Bool) (out : List Bool) :
    step raw (cfg 3 n odd (n+1) out)=some (cfg 4 n odd (n+1) out) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem loop (n rem pos : ℕ) (odd : Bool) (out : List Bool) (he : pos+rem=n) :
    Timed raw (2*rem+1) (cfg 3 n odd (pos+1) out)
      (cfg 4 n odd (n+1) (out++List.replicate (2*rem) true)) := by
  induction rem generalizing pos out with
  | zero =>
    have hp : pos=n := by omega
    subst pos
    simpa using Timed.single (by rfl) (stop n odd out)
  | succ rem ih =>
    have h := (pair n odd pos out (by omega)).trans
      (ih (pos+1) (out++[true,true]) (by omega))
    have hout : (out++[true,true])++List.replicate (2*rem) true=
        out++List.replicate (2*(rem+1)) true := by
      have hnum : 2*(rem+1)=2*rem+1+1 := by omega
      simp [hnum,List.replicate_succ,List.append_assoc]
    rw [hout] at h
    convert h using 1
    omega

theorem boot_step (n : ℕ) (odd : Bool) :
    step raw (cfg 0 n odd 0 [])=some (cfg 1 n odd 1 [false]) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]

theorem first_zero (odd : Bool) :
    step raw (cfg 1 0 odd 1 [false])=some (cfg 4 0 odd 1 [false]) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem first_succ (n : ℕ) (odd : Bool) :
    Timed raw (2-odd.toNat) (cfg 1 (n+1) odd 1 [false])
      (cfg 3 (n+1) odd 2 (CompareMachine.word (2-odd.toNat))) := by
  cases odd
  · have hs : step raw (cfg 1 (n+1) false 1 [false])=some (cfg 2 (n+1) false 1 [false,true]) := by
      simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape,List.replicate_succ,readTapeBit]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
      · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]
    exact (Timed.single (by rfl) hs).trans (Timed.single (by rfl) (second (n+1) false 1 [false,true]))
  · have hs : step raw (cfg 1 (n+1) true 1 [false])=some (cfg 3 (n+1) true 2 [false,true]) := by
      simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape,List.replicate_succ,readTapeBit]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
      · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]
    exact Timed.single (by rfl) hs

def ticks (n : ℕ) (odd : Bool) := 2*n+2-(if n=0 then 0 else odd.toNat)
def input (n : ℕ) (odd : Bool) : Fin 4 → List Bool := ![UnaryTemplate.tape n,[odd],[],[]]
def result (n : ℕ) (odd : Bool) : Fin 4 → List Bool :=
  ![UnaryTemplate.tape n,[odd],CompareMachine.word (2*n-odd.toNat),List.replicate (ticks n odd) false]
def machine := Rewind.machine raw

theorem raw_run (n : ℕ) (odd : Bool) :
    ∃ r,run raw (ticks n odd) ![UnaryTemplate.tape n,[odd],[]]=some r ∧
      r.final=cfg 4 n odd (n+1) (CompareMachine.word (2*n-odd.toNat)) ∧ r.steps=ticks n odd := by
  have ht : Timed raw (ticks n odd) (cfg 0 n odd 0 [])
      (cfg 4 n odd (n+1) (CompareMachine.word (2*n-odd.toNat))) := by
    cases n with
    | zero =>
      simpa [ticks,CompareMachine.word] using
        (Timed.single (by rfl) (boot_step 0 odd)).trans (Timed.single (by rfl) (first_zero odd))
    | succ n =>
      have h := ((Timed.single (by rfl) (boot_step (n+1) odd)).trans (first_succ n odd)).trans
        (loop (n+1) n 1 odd (CompareMachine.word (2-odd.toNat)) (by omega))
      have hout : CompareMachine.word (2-odd.toNat)++List.replicate (2*n) true=
          CompareMachine.word (2*(n+1)-odd.toNat) := by
        have hb : odd.toNat ≤ 1 := by cases odd <;> decide
        have hn : (2-odd.toNat)+2*n=2*(n+1)-odd.toNat := by omega
        simp only [CompareMachine.word,List.cons_append,←List.replicate_add,hn]
      rw [hout] at h
      have htime : 1+(2-odd.toNat)+(2*n+1)=ticks (n+1) odd := by
        cases odd <;> simp [ticks] <;> omega
      rw [htime] at h
      exact h
  have hi : cfg 0 n odd 0 []=initialConfiguration raw ![UnaryTemplate.tape n,[odd],[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at ht
  exact ht.run (by rfl)

theorem ready (n : ℕ) (odd : Bool) :
    ClockJoin.ReadyRun machine (4*n+6) (input n odd) (result n odd) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run n odd
  obtain ⟨r,hr,ht,hlog,hh,hrs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![UnaryTemplate.tape n,[odd],[]] (fun _ : Fin 1 => []))=input n odd := by
    funext i; fin_cases i <;> rfl
  change run machine (2*base.steps+2)
    (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![UnaryTemplate.tape n,[odd],[]] (fun _ : Fin 1 => []))=some r at hr
  rw [hi] at hr
  have hbnd : 2*base.steps+2 ≤ 4*n+6 := by unfold ticks at hs; omega
  have hm := run_moreFuel machine (2*base.steps+2) (4*n+6-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbnd] at hm
  refine ⟨r,hm,?_,hh,by omega⟩
  funext i
  fin_cases i
  · simpa [result,hf,cfg] using ht 0
  · simpa [result,hf,cfg] using ht 1
  · simpa [result,hf,cfg] using ht 2
  · simpa [result,hs] using hlog

end NearCubicWires.RepairOrdinary.EquationWeightCount
