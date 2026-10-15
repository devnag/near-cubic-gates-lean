import Proof.CaseAnalysis.WitnessFamilyReader

/-! The actual outer count enters its sentinel with one paid move and
then drives the unchanged complete family loop. Header workspace stays
outside the loop; its existing allocation is neither scanned nor copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
open LocalBitMultitape RecoveryRootRound
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads {s : ℕ} (source : Configuration 3063 s) (driver : ℕ) : Fin 3241 → ℕ:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>ℕ)
    (Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>ℕ) source.heads (fun _=>driver)) (fun _=>0)
def tapes {s : ℕ} (H total : ℕ) (source : Configuration 3063 s) (extra : Fin 177 → List Bool) : Fin 3241 → List Bool:=
  Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=3063) (n:=1) (motive:=fun _=>List Bool) source.tapes
      (fun _=>ZeroPadding.pad H (CompareMachine.word total))) extra
noncomputable def loop {s : ℕ} (body : Machine 3063 s):=
  TapeEmbedding.machine 177 (RepeatMachine.machine body (fun _ bits=>bits 724))
def directions (i : Fin 3241) : HeadMove:=if i=3063 then .right else .stay
def move:=DecompositionCountPosition.move directions
noncomputable def machine {s : ℕ} (body : Machine 3063 s):=Composition.machine move (loop body)
def budget (cost total : ℕ):=total*(cost+3)+5

private theorem move_heads {s : ℕ} (source : Configuration 3063 s) :
    (fun i=>(directions i).apply (heads source 0 i))=heads source 1 := by
  funext i
  refine Fin.addCases (m:=3064) (n:=177) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=3063) (n:=1) ?_ ?_ j
    · intro j
      have hj:(j.castAdd 1).castAdd 177≠(3063 : Fin 3241):=by
        intro h;have hv:=congrArg Fin.val h;change j.val=3063 at hv;omega
      simp only [directions,if_neg hj,HeadMove.apply,heads,Fin.addCases_left]
    · intro j;fin_cases j;rfl
  · intro j
    have hj:j.natAdd 3064≠(3063 : Fin 3241):=by
      intro h;have hv:=congrArg Fin.val h;change 3064+j.val=3063 at hv;omega
    simp only [directions,if_neg hj,HeadMove.apply,heads,Fin.addCases_right]

theorem work_run {α : Type} {s : ℕ} (body : Machine 3063 s) (source : ℕ → α → Configuration 3063 s)
    (Inv : ℕ → α → Prop) (H cost total : ℕ) (initial : α) (flag : Bool) (extra : Fin 177 → List Bool)
    (h : CountedFamily.PaddedRun body source Inv H cost total 724 initial flag) :
    ∃ r,runFrom (machine body) (budget cost total)
      ⟨(machine body).start,heads (source 0 initial) 0,tapes H total (source 0 initial) extra⟩=some r ∧
      r.steps ≤ budget cost total ∧ r.final.heads 724=0 ∧ r.final.tapes 724=[flag] ∧
      (flag=true → ∃ after,r.final.heads=heads (source total after) 1 ∧
        r.final.tapes=tapes H total (source total after) extra ∧ Inv total after) := by
  obtain ⟨base,hbase,bs,bh,bt,good⟩:=h
  let last:=TapeEmbedding.receipt (fun _ : Fin 177=>0) extra base
  have embedded:=TapeEmbedding.run_embed (RepeatMachine.machine body (fun _ bits=>bits 724))
    (fun _ : Fin 177=>0) extra _ _ base hbase
  have inputEq : TapeEmbedding.config (fun _ : Fin 177=>0) extra
      (ZeroPadding.config (CountedFamily.pads H) (RepeatMachine.cfg 0 (source 0 initial) total 1))=
      (⟨(loop body).start,heads (source 0 initial) 1,tapes H total (source 0 initial) extra⟩ : Configuration 3241 _) := by
    apply configuration_ext
    · rfl
    · simp only [TapeEmbedding.config,ZeroPadding.config,RepeatMachine.cfg,controlConfig,heads]
    · simp only [TapeEmbedding.config,ZeroPadding.config,RepeatMachine.cfg,controlConfig,
        CountedFamily.padded_data,tapes]
  rw [inputEq] at embedded
  obtain ⟨first,hfirst,ff,fs⟩:=DecompositionCountPosition.move_run directions
    (heads (source 0 initial) 0) (tapes H total (source 0 initial) extra)
  have firstHeads:first.final.heads=heads (source 0 initial) 1:=by rw [ff];exact move_heads _
  have firstTapes:first.final.tapes=tapes H total (source 0 initial) extra:=by rw [ff]
  have lastRun : runFrom (loop body) (total*(cost+3)+3)
      ⟨(loop body).start,first.final.heads,first.final.tapes⟩=some last := by
    rw [firstHeads,firstTapes];exact embedded
  obtain ⟨r,run,rs,rh,rt⟩:=joined move (loop body) 1 (total*(cost+3)+3) _ _ first last hfirst lastRun (by omega) bs
  have eq:1+1+(total*(cost+3)+3)=budget cost total:=by unfold budget;omega
  rw [eq] at run rs
  refine ⟨r,run,rs,?_,?_,?_⟩
  · rw [rh];exact bh
  · rw [rt];exact bt
  · intro accepted
    obtain ⟨after,ah,inv⟩:=good accepted
    refine ⟨after,?_,?_,inv⟩
    · rw [rh]
      change Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
      rw [ah]
      simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,heads]
    · rw [rt]
      change Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool) base.final.tapes extra=_
      rw [ah]
      simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        CountedFamily.padded_data,tapes]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
