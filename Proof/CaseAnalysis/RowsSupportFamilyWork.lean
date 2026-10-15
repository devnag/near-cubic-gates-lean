import Proof.CaseAnalysis.RowsSupportExchangeAny
import Proof.CaseAnalysis.WitnessFamilyWork

/-! The actual extended rejecting family loop shares the original outer
count driver and177-tape header bank. Static labels keep support last. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
open LocalBitMultitape RecoveryRootRound CloseoutWitness
open RepairSource.VerifierDecoding
open CloseoutWitness.SupportDock (lift)
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
open private move_heads from Proof.CaseAnalysis.WitnessFamilyWork
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def core {s : ℕ} (source : Configuration 3064 s):Configuration 3063 s:=
  ⟨source.control,fun i=>source.heads (i.castAdd 1),fun i=>source.tapes (i.castAdd 1)⟩
def heads {s : ℕ} (source : Configuration 3064 s) (driver : ℕ):Fin 3242→ℕ:=
  lift (CloseoutWitness.FamilyWork.heads (core source) driver) (source.heads 3063)
def tapes {s : ℕ} (H total : ℕ) (source : Configuration 3064 s) (extra : Fin 177→List Bool):Fin 3242→List Bool:=
  lift (CloseoutWitness.FamilyWork.tapes H total (core source) extra) (source.tapes 3063)
def renamed {s : ℕ} (body : Machine 3064 s):=
  TapeRenaming.machine (Exchange.layout 3063) (RepeatMachine.machine body (fun _ bits=>bits 724))
def loop {s : ℕ} (body : Machine 3064 s):=AppendBank.machine (e:=177) (renamed body)
def move:=TapeEmbedding.machine 1 CloseoutWitness.FamilyWork.move
def machine {s : ℕ} (body : Machine 3064 s):=Composition.machine move (loop body)
def budget (cost total : ℕ):=total*(cost+3)+5

theorem work_run {α : Type} {s : ℕ} (body : Machine 3064 s) (source : ℕ → α → Configuration 3064 s)
    (Inv : ℕ→α→Prop) (H cost total : ℕ) (initial : α) (flag : Bool) (extra : Fin 177→List Bool)
    (h:CountedFamily.PaddedRun body source Inv H cost total 724 initial flag):
    ∃ r,runFrom (machine body) (budget cost total)
      ⟨(machine body).start,heads (source 0 initial) 0,tapes H total (source 0 initial) extra⟩=some r ∧
      r.steps ≤ budget cost total ∧ r.final.heads 724=0 ∧ r.final.tapes 724=[flag] ∧
      (flag=true → ∃ after,r.final.heads=heads (source total after) 1 ∧
        r.final.tapes=tapes H total (source total after) extra ∧ Inv total after):=by
  obtain ⟨base,hbase,bs,bh,bt,good⟩:=h
  let exchanged:=TapeRenaming.receipt (Exchange.layout 3063) base
  have erun:=TapeRenaming.run_rename (Exchange.layout 3063)
    (RepeatMachine.machine body (fun _ bits=>bits 724)) _ _ base hbase
  obtain ⟨last,embedded,ls,lh,lt⟩:=AppendBank.run_any (renamed body) _ _ (fun _ : Fin 177=>0) extra exchanged erun
  have inputHeads:AppendBank.push
      ((ZeroPadding.config (CountedFamily.pads H) (RepeatMachine.cfg 0 (source 0 initial) total 1)).heads
        ∘ (Exchange.layout 3063).symm) (fun _ : Fin 177=>0)=heads (source 0 initial) 1:=by
    change AppendBank.push (lift (source 0 initial).heads 1 ∘ (Exchange.layout 3063).symm) _=_
    rw [Exchange.exchange_push];rfl
  have inputTapes:AppendBank.push
      ((ZeroPadding.config (CountedFamily.pads H) (RepeatMachine.cfg 0 (source 0 initial) total 1)).tapes
        ∘ (Exchange.layout 3063).symm) extra=tapes H total (source 0 initial) extra:=by
    simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,CountedFamily.padded_data]
    change AppendBank.push (lift (source 0 initial).tapes (ZeroPadding.pad H (CompareMachine.word total))
      ∘ (Exchange.layout 3063).symm) extra=_
    rw [Exchange.exchange_push];rfl
  change runFrom (loop body) _ _=some last at embedded
  simp only [TapeRenaming.config] at embedded
  rw [inputHeads,inputTapes] at embedded
  obtain ⟨oldFirst,oldRun,ff,fs⟩:=DecompositionCountPosition.move_run CloseoutWitness.FamilyWork.directions
    (CloseoutWitness.FamilyWork.heads (core (source 0 initial)) 0)
    (CloseoutWitness.FamilyWork.tapes H total (core (source 0 initial)) extra)
  let first:=TapeEmbedding.receipt (fun _ : Fin 1=>(source 0 initial).heads 3063)
    (fun _=>(source 0 initial).tapes 3063) oldFirst
  have firstRun:=TapeEmbedding.run_embed CloseoutWitness.FamilyWork.move
    (fun _ : Fin 1=>(source 0 initial).heads 3063) (fun _=>(source 0 initial).tapes 3063) _ _ oldFirst oldRun
  have fh:first.final.heads=heads (source 0 initial) 1:=by
    change lift oldFirst.final.heads _=_
    rw [ff]
    exact congrArg (fun Hs=>lift Hs ((source 0 initial).heads 3063)) (move_heads (core (source 0 initial)))
  have ft:first.final.tapes=tapes H total (source 0 initial) extra:=by
    change lift oldFirst.final.tapes _=_
    rw [ff];rfl
  have lastRun:runFrom (loop body) (total*(cost+3)+3) ⟨(loop body).start,first.final.heads,first.final.tapes⟩=some last:=by
    rw [fh,ft];exact embedded
  obtain ⟨r,run,rs,rh,rt⟩:=joined move (loop body) 1 (total*(cost+3)+3) _ _ first last firstRun lastRun
    (by exact fs.le) (by rw [ls];exact bs)
  have eq:1+1+(total*(cost+3)+3)=budget cost total:=by unfold budget;omega
  rw [eq] at run rs
  have ex724:(Exchange.layout 3063).symm (724 : Fin 3065)=724:=Exchange.old 3063 (724 : Fin 3063)
  refine ⟨r,run,rs,?_,?_,?_⟩
  · rw [rh,lh]
    change base.final.heads ((Exchange.layout 3063).symm 724)=0
    rw [ex724];exact bh
  · rw [rt,lt]
    change base.final.tapes ((Exchange.layout 3063).symm 724)=[flag]
    rw [ex724];exact bt
  · intro accepted
    obtain ⟨after,ah,inv⟩:=good accepted
    refine ⟨after,?_,?_,inv⟩
    · rw [rh,lh]
      change AppendBank.push (base.final.heads ∘ (Exchange.layout 3063).symm) _=_
      rw [ah]
      change AppendBank.push (lift (source total after).heads 1 ∘ (Exchange.layout 3063).symm) _=_
      rw [Exchange.exchange_push];rfl
    · rw [rt,lt]
      change AppendBank.push (base.final.tapes ∘ (Exchange.layout 3063).symm) _=_
      rw [ah]
      simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,CountedFamily.padded_data]
      change AppendBank.push (lift (source total after).tapes (ZeroPadding.pad H (CompareMachine.word total))
        ∘ (Exchange.layout 3063).symm) extra=_
      rw [Exchange.exchange_push];rfl

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyWork
