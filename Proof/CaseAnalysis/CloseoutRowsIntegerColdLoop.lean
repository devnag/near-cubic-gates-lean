import Proof.CaseAnalysis.RowsIntegerPrefix
import Proof.CaseAnalysis.RowsIntegerListMeaning
import Proof.Circuits.DecompositionCountPosition

/-! One paid head-positioning step enters the already checked counted
integer loop on the exact cold-produced stream, count and reusable bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (i : Fin 459) : HeadMove:=if i=220 then .right else .stay
def position:=DecompositionCountPosition.move directions
noncomputable def loop:=RecoveryFocus.machine loopSlots CloseoutRowsIntegerLoop.machine
noncomputable def finish:=Composition.machine position loop
def finishBudget (bits : List Bool):=CloseoutRowsIntegerLoop.budget bits.length (Reencode.fields bits).length+2
noncomputable def loopEntry (bits : List Bool):=
  RepeatMachine.cfg 0 (CloseoutRowsIntegerLoop.entry bits.length (CloseoutRowsCanonicalFlag.flag bits)
    (Reencode.fields bits) [] [] 0 []) (Reencode.fields bits).length 1
def produced (bits : List Bool):=(Reencode.fields bits).flatMap CloseoutRowsCheckedInteger.produced
noncomputable def loopResult (bits : List Bool):=
  RepeatMachine.cfg 3 (CloseoutRowsIntegerLoop.entry bits.length (CloseoutRowsCanonicalFlag.flag bits)
    (Reencode.fields bits) [] [] (Reencode.fields bits).length (produced bits))
      (Reencode.fields bits).length 1

theorem entry_tapes (bits : List Bool) : (loopEntry bits).tapes=loopInput bits:=by
  simp only [loopEntry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    CloseoutRowsIntegerLoop.entry,CloseoutRowsIntegerRound.cfg,List.take_zero,List.flatMap_nil,
    List.length_nil,Nat.zero_add,List.nil_append,List.append_nil,CloseoutRowsIntegerLoop.validity,
    List.range_zero,List.all_nil,Bool.and_true,loopInput]

theorem entry_heads (bits : List Bool) (i : Fin 221) :
    (directions (loopSlots i)).apply 0=(loopEntry bits).heads i:=by
  refine Fin.addCases (m:=220) (n:=1) ?_ ?_ i
  · intro j
    have hn:loopSlots (j.castAdd 1)≠220:=by
      intro h
      have hv:=congrArg Fin.val h
      change j.val=220 at hv
      omega
    simp only [directions,if_neg hn,HeadMove.apply,loopEntry,RepeatMachine.cfg,controlConfig,
      TapeEmbedding.config,Fin.addCases_left,CloseoutRowsIntegerLoop.entry,CloseoutRowsIntegerRound.cfg,
      CloseoutRowsIntegerRound.heads,List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add]
    split_ifs <;> rfl
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl

theorem finish_run (bits : List Bool) (tapes : Fin 459→List Bool)
    (htapes : ∀ i,tapes (loopSlots i)=loopInput bits i) : ∃ actual,
    run finish (finishBudget bits) tapes=some actual ∧ actual.steps≤finishBudget bits ∧
      (∀ i,actual.final.tapes (loopSlots i)=(loopResult bits).tapes i) ∧
      (∀ i,actual.final.heads (loopSlots i)=(loopResult bits).heads i):=by
  obtain ⟨p,hp,pf,ps⟩:=DecompositionCountPosition.move_run directions (fun _=>0) tapes
  obtain ⟨raw,hr,rf,rs⟩:=CloseoutRowsIntegerLoop.integers_run bits.length (CloseoutRowsCanonicalFlag.flag bits)
    (Reencode.fields bits) [] [] [] (by
      intro word hw
      exact (CloseoutRowsIntegerList.fields_bound bits).2 word hw |>.le)
  change runFrom CloseoutRowsIntegerLoop.machine _ (loopEntry bits)=some raw at hr
  have hrfinal:raw.final=loopResult bits:=by
    simpa only [List.nil_append,loopResult,produced] using rf
  obtain ⟨r,h,hcontrol,hsteps,hheads,ht,hother⟩:=RecoveryFocus.dock loopSlots loop_injective
    CloseoutRowsIntegerLoop.machine _ p.final.heads p.final.tapes (loopEntry bits)
    (by intro i;rw [pf];exact entry_heads bits i)
    (by intro i;rw [pf];exact (htapes i).trans (congrFun (entry_tapes bits).symm i)) raw hr
  have start:(loopEntry bits).control=loop.start:=rfl
  rw [start] at h
  change runFrom loop _ (Composition.restart p.final loop.start)=some r at h
  have whole:=Composition.run_join position loop _ _ _ p r hp h
  have he:1+1+CloseoutRowsIntegerLoop.budget bits.length (Reencode.fields bits).length=finishBudget bits:=by
    unfold finishBudget
    omega
  rw [he] at whole
  refine ⟨_,whole,?_,?_,?_⟩
  · change p.steps+1+r.steps≤_
    rw [ps,hsteps]
    unfold finishBudget
    omega
  · intro i
    change r.final.tapes (loopSlots i)=_
    rw [ht,hrfinal]
  · intro i
    change r.final.heads (loopSlots i)=_
    rw [hheads,hrfinal]

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
