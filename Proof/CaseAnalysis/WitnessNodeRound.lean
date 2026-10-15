import Proof.CaseAnalysis.WitnessNodeIncrement

/-! A complete reusable node round: load the next literal frame, validate
and append its native fields, fold validity, erase scratch, and increment
the strict-earlier-node bound. Every join is an actual transition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RadixSemantics SignedSortKey
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
noncomputable def cleared:=Composition.machine checked eraser
noncomputable def machine:=Composition.machine cleared increment
noncomputable def passes (n index : ℕ) (bits : List Bool) : Bool:=by
  classical
  exact decide (NodeMeaning.valid n index bits)
def budget (w : ℕ) (bits : List Bool):=
  NodeReady.budget w bits+2*NodeReady.capacity w+4*bits.length+4*w+14

theorem budget_bound (w : ℕ) (bits : List Bool) (hw : bits.length+1 ≤ w) :
    budget w bits ≤ 5*NodeReady.capacity w:=by
  have h:=NodeReady.budget_bound w bits hw
  have hp:w ≤ w^24:=Nat.le_self_pow (by decide) _
  unfold budget NodeReady.capacity at *
  omega

theorem round_run (w index : ℕ) (left bits out pre tail : List Bool) (flag : Bool)
    (hl : left.length=w) (hw : bits.length+1 ≤ w) (hindex : index+1<2^w) :
    let cap:=NodeReady.capacity w
    let resultWord:=NodeBody.appended bits out
    let nextFlag:=flag && passes (value left) index bits
    ∃ result,runFrom machine (budget w bits)
      (cfg machine.start cap w pre.length left (binary w index) [] out (pre++frame bits++tail) flag)=some result ∧
      result.steps ≤ budget w bits ∧
      result.final.heads=heads resultWord (pre.length+2*bits.length+1) ∧
      result.final.tapes=data cap w left (binary w (index+1)) [] resultWord (pre++frame bits++tail) nextFlag:=by
  dsimp only
  let cap:=NodeReady.capacity w
  let source:=pre++frame bits++tail
  let position:=pre.length+2*bits.length+1
  let output:=NodeBody.appended bits out
  have hp:w ≤ w^24:=Nat.le_self_pow (by decide) _
  have hC:1 ≤ cap:=by unfold cap NodeReady.capacity;omega
  have hload:2*bits.length+1 ≤ cap:=by unfold cap NodeReady.capacity;omega
  have hwidth:2*w ≤ cap:=by unfold cap NodeReady.capacity;omega
  obtain ⟨l,hlrun,ls,lh,lt⟩:=load_run cap w left (binary w index) bits out pre tail flag hload
  obtain ⟨p,hprun,ps,ph,pt,pflag⟩:=parse_run w position left (binary w index) bits out source flag
    hl (binary_length w index) hw
  have hpl:runFrom parser (NodeReady.budget w bits) (Composition.restart l.final parser.start)=some p:=by
    rw [show Composition.restart l.final parser.start=
      cfg parser.start cap w position left (binary w index) bits out source flag from
        configuration_ext rfl lh lt]
    exact hprun
  let lp:=Composition.joinedReceipt l p
  have hlp:=Composition.run_join loader parser _ _ _ l p hlrun hpl
  obtain ⟨f,hfrun,fs,fh,_,fstore⟩:=flag_run cap w position left (binary w index) output source flag p.final.tapes pt
  have hfl:runFrom foldFlag 1 (Composition.restart lp.final foldFlag.start)=some f:=by
    rw [restart_joined l p]
    rw [show Composition.restart p.final foldFlag.start=
      (⟨foldFlag.start,heads output position,p.final.tapes⟩ : Configuration 755 2) from
        configuration_ext rfl ph rfl]
    exact hfrun
  let lpf:=Composition.joinedReceipt lp f
  have hlpf:=Composition.run_join loaded foldFlag _ _ _ lp f hlp hfl
  have hflag:readTapeBit (p.final.tapes 745) 0=passes (value left) index bits:=by
    apply Bool.eq_iff_iff.mpr
    rw [binary_value w index (by omega)] at pflag
    simpa only [passes,decide_eq_true_eq] using pflag
  rw [hflag] at fstore
  obtain ⟨e,herun,es,eh,et⟩:=erase_run cap w position left (binary w index) output source
    (flag && passes (value left) index bits) f.final.tapes hC fstore
  have hel:runFrom eraser (2*cap+4) (Composition.restart lpf.final eraser.start)=some e:=by
    rw [restart_joined lp f]
    rw [show Composition.restart f.final eraser.start=
      (⟨eraser.start,heads output position,f.final.tapes⟩ : Configuration 755 4) from
        configuration_ext rfl fh rfl]
    exact herun
  let lpfe:=Composition.joinedReceipt lpf e
  have hlpfe:=Composition.run_join checked eraser _ _ _ lpf e hlpf hel
  obtain ⟨i,hirun,its,ih,it⟩:=increment_run cap w index position left output source
    (flag && passes (value left) index bits) hindex hwidth hC
  have hil:runFrom increment (4*w+2) (Composition.restart lpfe.final increment.start)=some i:=by
    rw [restart_joined lpf e]
    rw [show Composition.restart e.final increment.start=
      cfg increment.start cap w position left (binary w index) [] output source
        (flag && passes (value left) index bits) from configuration_ext rfl eh et]
    exact hirun
  have hall:=Composition.run_join cleared increment _ _ _ lpfe i hlpfe hil
  have htime:(((4*bits.length+3+1+NodeReady.budget w bits)+1+1)+1+(2*cap+4))+1+(4*w+2)=budget w bits:=by
    unfold budget cap
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt lpfe i,hall,?_,ih,it⟩
  change (((l.steps+1+p.steps)+1+f.steps)+1+e.steps)+1+i.steps ≤ _
  rw [ls,fs,es]
  unfold budget cap at *
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
