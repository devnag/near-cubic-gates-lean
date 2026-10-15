import Proof.CaseAnalysis.RowsCircuitTopPublish

/-! Compare the symmetric table length with actual bottomCount+1 using
the produced bottom template itself. Two paid writes temporarily reuse its
leading sentinel and restore the exact template before the bottom loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopCount
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def set (bit : Bool) : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,![none,some bit,none,none],fun _=>.stay⟩ else none
def data (n m : ℕ) (lead : Bool) (flag log : List Bool) : Fin 4→List Bool:=
  ![CompareMachine.word n,lead::(List.replicate m true++[false]),flag,log]
def machine:=Composition.machine (Composition.machine (set true) CloseoutRowsGateArityCheck.machine) (set false)
def budget (n m : ℕ):=2*min n (m+1)+10

theorem set_run (n m : ℕ) (lead bit : Bool) (flag log : List Bool) :
    ClockJoin.ReadyRun (set bit) 1 (data n m lead flag log) (data n m bit flag log):=by
  let final:Configuration 4 2:=⟨1,fun _=>0,data n m bit flag log⟩
  have hs:step (set bit) (initialConfiguration (set bit) (data n m lead flag log))=some final:=by
    apply congrArg some;apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem patched (m : ℕ) : ZeroPadding.pad (m+2) (List.replicate (m+1) true)=
    true::(List.replicate m true++[false]):=by
  simp [ZeroPadding.pad,List.replicate_succ]

theorem compare_run (n m : ℕ) :
    ClockJoin.ReadyRun CloseoutRowsGateArityCheck.machine (2*min n (m+1)+6)
      (data n m true [] [])
      (data n m true [decide (n=m+1)] (List.replicate (min n (m+1)+2) false)):=by
  obtain ⟨base,hb,bt,bh,bs⟩:=CloseoutRowsGateArityCheck.arity_run n (m+1)
  let caps:Fin 4→ℕ:=![0,m+2,0,0]
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CloseoutRowsGateArityCheck.machine caps _ _ base hb
  have hi:ZeroPadding.config caps (initialConfiguration CloseoutRowsGateArityCheck.machine
      (CloseoutRowsGateArityCheck.input n (m+1)))=
      initialConfiguration CloseoutRowsGateArityCheck.machine (data n m true [] []):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;>
        simp [ZeroPadding.config,initialConfiguration,caps,CloseoutRowsGateArityCheck.input,data,patched]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs ▸ bs⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps i) (base.final.tapes i))=_
    rw [bt]
    funext i;fin_cases i <;>
      simp [caps,CloseoutRowsGateArityCheck.output,data,patched]
  · intro i;rw [rf];exact bh i

theorem count_run (n m : ℕ) : ClockJoin.ReadyRun machine (budget n m)
    ![CompareMachine.word n,UnaryTemplate.tape m,[],[]]
    ![CompareMachine.word n,UnaryTemplate.tape m,[decide (n=m+1)],List.replicate (min n (m+1)+2) false]:=by
  have first:=ClockJoin.join (set true) CloseoutRowsGateArityCheck.machine _ _ _ _ _
    (set_run n m false true [] []) (compare_run n m)
  have whole:=ClockJoin.join (Composition.machine (set true) CloseoutRowsGateArityCheck.machine) (set false)
    _ _ _ _ _ first (set_run n m true false [decide (n=m+1)] (List.replicate (min n (m+1)+2) false))
  have ht:(1+1+(2*min n (m+1)+6))+1+1=budget n m:=by unfold budget;omega
  simpa only [ht,machine,data,UnaryTemplate.tape] using whole

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopCount
