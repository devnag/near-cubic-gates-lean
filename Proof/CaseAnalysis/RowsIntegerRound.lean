import Proof.CaseAnalysis.RowsIntegerErase

/-! One complete integer round consumes the next literal field, appends
the signed native word, folds its codec verdict, and restores local scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem restart_joined {t a b c : ℕ} (first : ExecutionReceipt t a)
    (second : ExecutionReceipt t b) (q : Fin c) :
    Composition.restart (Composition.joinedReceipt first second).final q=
      Composition.restart second.final q:=rfl

noncomputable def loaded:=Composition.machine loader parser
noncomputable def checked:=Composition.machine loaded foldFlag
noncomputable def machine:=Composition.machine checked eraser
def passes (bits : List Bool) : Bool:=(CanonicalBinary.decodeInt (value bits)).isSome
def budget (w : ℕ) (bits : List Bool):=
  CloseoutRowsIntegerReady.budget bits+2*CloseoutRowsIntegerReady.capacity w+4*bits.length+11

theorem budget_bound (w : ℕ) (bits : List Bool) (hw : bits.length ≤ w) :
    budget w bits ≤ 5*CloseoutRowsIntegerReady.capacity w:=by
  have h:=CloseoutRowsIntegerReady.budget_bound w bits hw
  have hp:1 ≤ (w+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold budget CloseoutRowsIntegerReady.capacity at *
  omega

theorem round_run (w : ℕ) (bits out pre tail : List Bool) (flag : Bool)
    (hw : bits.length ≤ w) :
    ∃ result,runFrom machine (budget w bits)
      (cfg machine.start (CloseoutRowsIntegerReady.capacity w) pre.length [] out (pre++frame bits++tail) flag)=some result ∧
      result.steps ≤ budget w bits ∧
      result.final.heads=heads (out++CloseoutRowsCheckedInteger.produced bits) (pre.length+2*bits.length+1) ∧
      result.final.tapes=data (CloseoutRowsIntegerReady.capacity w) [] (out++CloseoutRowsCheckedInteger.produced bits)
        (pre++frame bits++tail) (flag && passes bits):=by
  let cap:=CloseoutRowsIntegerReady.capacity w
  let source:=pre++frame bits++tail
  let position:=pre.length+2*bits.length+1
  let output:=out++CloseoutRowsCheckedInteger.produced bits
  have hb:=CloseoutRowsIntegerReady.budget_bound w bits hw
  have hload:2*bits.length+1 ≤ cap:=by unfold cap;omega
  obtain ⟨l,hlrun,ls,lh,lt⟩:=load_run cap bits out pre tail flag hload
  obtain ⟨p,hprun,ps,ph,pt,pflag⟩:=parse_run w position bits out source flag hw
  have hpl:runFrom parser (CloseoutRowsIntegerReady.budget bits)
      (Composition.restart l.final parser.start)=some p:=by
    rw [show Composition.restart l.final parser.start=
      cfg parser.start cap position bits out source flag from configuration_ext rfl lh lt]
    exact hprun
  let lp:=Composition.joinedReceipt l p
  have hlp:=Composition.run_join loader parser _ _ _ l p hlrun hpl
  obtain ⟨f,hfrun,fs,fh,_,fstore⟩:=flag_run cap position output source flag p.final.tapes pt
  have hfl:runFrom foldFlag 1 (Composition.restart lp.final foldFlag.start)=some f:=by
    rw [restart_joined l p]
    rw [show Composition.restart p.final foldFlag.start=
      (⟨foldFlag.start,heads output position,p.final.tapes⟩ : Configuration 220 2) from
        configuration_ext rfl ph rfl]
    exact hfrun
  let lpf:=Composition.joinedReceipt lp f
  have hlpf:=Composition.run_join loaded foldFlag _ _ _ lp f hlp hfl
  have hflag:readTapeBit (p.final.tapes 211) 0=passes bits:=
    Bool.eq_iff_iff.mpr pflag
  rw [hflag] at fstore
  obtain ⟨e,herun,es,eh,et⟩:=erase_run cap position output source (flag && passes bits) f.final.tapes
    (CloseoutRowsIntegerReady.capacity_positive w) fstore
  have hel:runFrom eraser (2*cap+4) (Composition.restart lpf.final eraser.start)=some e:=by
    rw [restart_joined lp f]
    rw [show Composition.restart f.final eraser.start=
      (⟨eraser.start,heads output position,f.final.tapes⟩ : Configuration 220 4) from
        configuration_ext rfl fh rfl]
    exact herun
  have hall:=Composition.run_join checked eraser _ _ _ lpf e hlpf hel
  have htime:((4*bits.length+3+1+CloseoutRowsIntegerReady.budget bits)+1+1)+1+(2*cap+4)=budget w bits:=by
    unfold budget cap
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt lpf e,hall,?_,eh,et⟩
  change ((l.steps+1+p.steps)+1+f.steps)+1+e.steps ≤ _
  rw [ls,fs,es]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
