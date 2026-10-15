import Proof.Amplification.RecoveryTseitinBank

/-! The entire tautology stream from blank scratch, the actual capacity and
count tapes. The last driver head move is executed before entering the loop. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enter : Machine 242 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=241 then .right else .stay⟩ else none
noncomputable def readyMachine := Composition.machine bankMachine enter
noncomputable def preparedMachine := Composition.machine readyMachine loopMachine
def preparedBudget (cap count : Nat) := (2*cap+7)+(count*(24*cap+19)+3)

theorem enter_run (cap count : Nat) (out : List Bool) : ∃ r,
    runFrom enter 1 ⟨enter.start,bankHeads out,bankOutput cap count out⟩=some r ∧
      r.final.heads=(loopCfg 0 cap (initial cap) out count 1).heads ∧
      r.final.tapes=bankOutput cap count out ∧ r.steps=1 := by
  let final : Configuration 242 2 := ⟨1,(loopCfg 0 cap (initial cap) out count 1).heads,bankOutput cap count out⟩
  have hs : step enter ⟨enter.start,bankHeads out,bankOutput cap count out⟩=some final := by
    simp only [step,enter,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=241) (n:=1) (fun a=>?_) (fun a=>?_) i
      · refine Fin.addCases (m:=239) (n:=2) (fun b=>?_) (fun b=>?_) a
        · have h239 : ((b.castAdd 2).castAdd 1 : Fin 242)≠239 := by intro he; have hv:=congrArg Fin.val he; have hb:=b.isLt; change b.val=239 at hv; omega
          have h241 : ((b.castAdd 2).castAdd 1 : Fin 242)≠241 := by intro he; have hv:=congrArg Fin.val he; have hb:=b.isLt; change b.val=241 at hv; omega
          simp only [applyAction,if_neg h241,HeadMove.apply,bankHeads,if_neg h239,
            final,loopCfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,heads]
        · fin_cases b <;> rfl
      · fin_cases a; rfl
    · rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],ht⟩

theorem ready_run (cap count : Nat) (out : List Bool) : ∃ r,
    runFrom readyMachine (2*cap+6) ⟨readyMachine.start,bankHeads out,bankInput cap count out⟩=some r ∧
      r.final.heads=(loopCfg 0 cap (initial cap) out count 1).heads ∧
      r.final.tapes=(loopCfg 0 cap (initial cap) out count 1).tapes ∧ r.steps≤2*cap+6 := by
  obtain ⟨bank,hb,bh,bt,bs⟩ := bank_run cap count out
  obtain ⟨last,hl,lh,lt,ls⟩ := enter_run cap count out
  have he : Composition.restart bank.final enter.start=
      (⟨enter.start,bankHeads out,bankOutput cap count out⟩ : Configuration 242 2) := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [←he] at hl
  have hwhole := Composition.run_join bankMachine enter _ _ _ bank last hb hl
  have htime : (2*cap+4)+1+1=2*cap+6 := by omega
  rw [htime] at hwhole
  exact ⟨_,hwhole,lh,lt,by change bank.steps+1+last.steps≤_; omega⟩

theorem prepared_run (cap count : Nat) (out : List Bool) (hc : uniformCapacity count≤cap) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom preparedMachine (preparedBudget cap count)
        ⟨preparedMachine.start,bankHeads out,bankInput cap count out⟩=some r ∧
      r.final.heads=(loopCfg 3 cap after
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies count)) count 1).heads ∧
      r.final.tapes=(loopCfg 3 cap after
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies count)) count 1).tapes ∧
      Valid cap count after ∧ r.steps≤preparedBudget cap count := by
  have hpos : 1≤cap := by
    have hs : 0<(natBitLength count+1)^2 := by positivity
    unfold uniformCapacity at hc
    omega
  obtain ⟨ready,hr,rh,rt,rs⟩ := ready_run cap count out
  obtain ⟨after,last,hl,lf,lv,_keep,ls⟩ := stream_run cap count (initial cap) out hc (initial_valid cap hpos)
  have he : Composition.restart ready.final loopMachine.start=loopCfg 0 cap (initial cap) out count 1 := by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [←he] at hl
  have hwhole := Composition.run_join readyMachine loopMachine _ _ _ ready last hr hl
  have htime : (2*cap+6)+1+(count*(24*cap+19)+3)=preparedBudget cap count := by unfold preparedBudget; omega
  rw [htime] at hwhole
  exact ⟨after,_,hwhole,congrArg Configuration.heads lf,congrArg Configuration.tapes lf,lv,
    by change ready.steps+1+last.steps≤_; rw [←htime]; omega⟩

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
