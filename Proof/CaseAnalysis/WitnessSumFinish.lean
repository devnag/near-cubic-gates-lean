import Proof.CaseAnalysis.WitnessSumCheck
import Proof.CaseAnalysis.RowsIntegerFlag
import Proof.PCP.PCPSerializerCapacityFocus
import Proof.CaseAnalysis.WitnessMassReset

/-! Preserve the exact mass verdict before resetting the accumulator. The
same source and coefficient stream survive both reusable-bank resets. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumFinish
open LocalBitMultitape RecoveryRootRound CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 94) : Fin 827:=((i.castAdd 7).natAdd 725).castAdd 1
def flagSlots : Fin 2→Fin 827:=![790,724]
noncomputable def foldFlag:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
noncomputable def reset:=RecoveryFocus.machine nativeSlots bootstrapProgram
noncomputable def checked (k : ℕ) (q : ℚ):=Composition.machine (SumCheck.machine k q) foldFlag
noncomputable def cleared (k : ℕ) (q : ℚ):=Composition.machine (checked k q) reset
noncomputable def machine (k : ℕ) (q : ℚ):=Composition.machine (cleared k q) TermCommit.erase
def budget (P B k : ℕ):=MassCheck.budget B k+1+1+1+bootstrapBudget B+1+(2*P+4)

def Ready {s : ℕ} (p : Machine 827 s) (fuel position : ℕ) (out : List Bool)
    (input output : Fin 827→List Bool) : Prop:=∃ r,
  runFrom p fuel ⟨p.start,TermCommit.heads position out,input⟩=some r ∧
    r.steps≤fuel ∧ r.final.heads=TermCommit.heads position out ∧ r.final.tapes=output

theorem data_native (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out : List Bool) (i : Fin 94) : TermCommit.data P terms ambient out (nativeSlots i)=ambient i:=by
  rw [nativeSlots,TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right,
    TermMass.tail,Fin.addCases_left]
theorem heads_native (position : ℕ) (out : List Bool) (i : Fin 94) :
    TermCommit.heads position out (nativeSlots i)=0:=by
  rw [nativeSlots,TermCommit.heads,Fin.addCases_left,TermMass.heads,Fin.addCases_right]
theorem native_outside (P : ℕ) (terms : Fin 725→List Bool) (a b : Fin 94→List Bool)
    (out : List Bool) (i : Fin 827) (hi : ∀ j,nativeSlots j≠i) :
    TermCommit.data P terms a out i=TermCommit.data P terms b out i:=by
  revert hi
  refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
    · intro k _;simp only [TermCommit.data,Fin.addCases_left,TermMass.data]
    · intro k
      refine Fin.addCases (m:=94) (n:=7) ?_ ?_ k
      · intro l hl;exact (hl l rfl).elim
      · intro l _;simp only [TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right,TermMass.tail]
  · intro j _;simp only [TermCommit.data,Fin.addCases_right]
theorem reset_run (P B position : ℕ) (a : Estimate) (out : List Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (hstore : Store B a [] ambient) (hB : 1≤B) : ∃ next,
    Ready reset (bootstrapBudget B) position out (TermCommit.data P terms ambient out)
      (TermCommit.data P terms next out) ∧ Store B CompetitorSumWidth.zero [] next:=by
  obtain ⟨next,⟨base,hb,bt,bh,bs⟩,hnext⟩:=MassReset.reset_run B a [] ambient hstore hB
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock nativeSlots
    (by intro i j h;apply Fin.ext;have hv:=congrArg (fun k : Fin 827=>k.val) h;change 725+i.val=725+j.val at hv;omega)
    bootstrapProgram _ (TermCommit.heads position out) (TermCommit.data P terms ambient out) _
    (heads_native position out) (data_native P terms ambient out) base hb
  refine ⟨next,⟨r,hr,rs.trans_le bs,?_,?_⟩,hnext⟩
  · funext i
    by_cases hs:∃ j,nativeSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,bh,heads_native]
    · exact (keep i (by simpa using hs)).1
  · funext i
    by_cases hs:∃ j,nativeSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rt,bt,data_native]
    · exact ((keep i (by simpa using hs)).2).trans
        (native_outside P terms ambient next out i (by simpa using hs))

theorem data_update (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out bits : List Bool) : Function.update (TermCommit.data P terms ambient out) 724 bits=
      TermCommit.data P (Function.update terms 724 bits) ambient out:=by
  funext i
  refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
    · intro k
      by_cases hk:k=724
      · subst k
        change Function.update (TermCommit.data P terms ambient out) (724 : Fin 827) bits 724=
          Function.update terms (724 : Fin 725) bits 724
        rw [Function.update_self,Function.update_self]
      · have hi:((k.castAdd 101).castAdd 1 : Fin 827)≠724:=by
          intro h;apply hk;exact Fin.ext (congrArg (fun l : Fin 827=>l.val) h)
        rw [Function.update_of_ne hi]
        change TermCommit.data _ _ _ _ (TermCommit.eraseSlots k)=TermCommit.data _ _ _ _ (TermCommit.eraseSlots k)
        rw [TermCommit.data_core,TermCommit.data_core,Function.update_of_ne hk]
    · intro k
      rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 725+k.val≠724;omega)]
      simp only [TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right]
  · intro j
    rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change 826+j.val≠724;omega)]
    simp only [TermCommit.data,Fin.addCases_right]

theorem flag_run (P position : ℕ) (out : List Bool) (flag : Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool) (hf : terms 724=[flag]) :
    Ready foldFlag 1 position out (TermCommit.data P terms ambient out)
      (TermCommit.data P (Function.update terms 724 [flag && readTapeBit (ambient 65) 0]) ambient out):=by
  let tapes:=TermCommit.data P terms ambient out
  obtain ⟨r,hr,rh,rt,rs⟩:=(CloseoutRowsIntegerRound.flag_ready (ambient 65) flag).focus_at
    flagSlots (by decide) (TermCommit.heads position out) tapes
    (by intro i;fin_cases i
        · exact data_native P terms ambient out 65
        · exact (TermCommit.data_core P terms ambient out 724).trans hf)
    (by intro i;fin_cases i <;> rfl)
  refine ⟨r,hr,rs.le,rh,?_⟩
  rw [rt,←data_update]
  funext i
  by_cases h724:i=724
  · subst i
    rw [Function.update_self]
    exact install_slot flagSlots (by decide) tapes _ 1
  rw [Function.update_of_ne h724]
  by_cases h790:i=790
  · subst i
    exact (install_slot flagSlots (by decide) tapes _ 0).trans (data_native P terms ambient out 65).symm
  · exact install_other flagSlots tapes _ i (by
      intro j;fin_cases j
      · exact Ne.symm h790
      · exact Ne.symm h724)

theorem blank_scratch (P b : ℕ) (source : List Bool) (flag : Bool) (hP : 1≤P) (i : Fin 719) :
    TermRead.data P b [] source flag (TermRead.scratchSlots i)=List.replicate P false:=by
  have hv:=TermRead.scratch_small i
  have hn:=TermRead.erase_width (i.castAdd 2)
  let j : Fin 720:=⟨(TermRead.scratchSlots i).val,hv⟩
  have hj:TermRead.scratchSlots i=j.castAdd 5:=Fin.ext rfl
  rw [hj,TermRead.data,Fin.addCases_left]
  have h149:j.val≠149:=by intro h;apply hn;exact Fin.ext h
  unfold TermPadded.input TermCoefficient.input
  rw [if_neg h149]
  split_ifs
  · exact CloseoutRowsIntegerReady.pad_empty_frame P hP
  · simp [ZeroPadding.pad]

theorem finish_run (P B b k position : ℕ) (q : ℚ) (a : Estimate)
    (source out : List Bool) (flag : Bool) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (ha : a.Valid B) (hB : 1≤B) (hq : 0≤q) (hk : k≤B)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k)
    (hc : MassCheck.budget B k+1≤P) (hi : ∀ i,(ambient i).length≤P) : ∃ next,
    Ready (machine k q) (budget P B k) position out
      (TermCommit.data P (TermRead.data P b [] source flag) ambient out)
      (TermCommit.data P (TermRead.data P b [] source (flag && decide (a.value≤q))) next out) ∧
      Store B CompetitorSumWidth.zero [] next:=by
  classical
  obtain ⟨check,c,hcRun,cs,ch,ct,store,meaning,bound⟩:=SumCheck.check_run P B b k position q a source out flag ambient
    h ha hq hk hp hd hc hi
  let terms:=SumCheck.changed (TermRead.data P b [] source flag) check
  let native:=CompetitorThresholdAmbient.project check
  have hflag:terms 724=[flag]:=by
    rw [show terms=SumCheck.changed _ _ by rfl,SumCheck.changed,dif_neg (by decide)]
    rfl
  have hvalue:readTapeBit (native 65) 0=decide (a.value≤q):=by
    have he:native 65=check 65:=rfl
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using meaning
  have hf:=flag_run P position out flag terms native hflag
  rw [hvalue] at hf
  let f:=flag && decide (a.value≤q)
  let finalTerms:=Function.update terms 724 [f]
  obtain ⟨next,hr,hnext⟩:=reset_run P B position a out finalTerms native store hB
  have hw:finalTerms 149=ZeroPadding.pad P (List.replicate b true):=by
    rw [show finalTerms=Function.update terms 724 [f] by rfl,Function.update_of_ne (by decide)]
    rw [show terms=SumCheck.changed _ _ by rfl,SumCheck.changed,dif_neg (by decide)]
    rfl
  have hextra (i : Fin 5) : finalTerms (i.natAdd 720)=TermRead.extra P source f i:=by
    fin_cases i
    all_goals first
      | (change Function.update terms 724 [f] 724=[f];exact Function.update_self _ _ _)
      | (rw [show finalTerms=Function.update terms 724 [f] by rfl,Function.update_of_ne (by decide)];
         rw [show terms=SumCheck.changed _ _ by rfl,SumCheck.changed,dif_neg (by decide)];rfl)
  have hs (i : Fin 719) : (finalTerms (TermRead.scratchSlots i)).length≤P:=by
    have hv:=TermRead.scratch_small i
    rw [show finalTerms=Function.update terms 724 [f] by rfl,
      Function.update_of_ne (by apply Fin.ne_of_val_ne;omega)]
    rw [show terms=SumCheck.changed _ _ by rfl,SumCheck.changed]
    split_ifs with hsmall
    · exact bound _
    · rw [blank_scratch P b source flag (by omega) i,List.length_replicate]
  obtain ⟨e,he,es,eh,et⟩:=TermCommit.erase_run P b position source out f finalTerms next (by omega) hs hw hextra
  obtain ⟨fRun,hfRun,fs,fh,ft⟩:=hf
  obtain ⟨rRun,hrRun,rs,rh,rt⟩:=hr
  have hcf:Composition.restart c.final foldFlag.start=
      ⟨foldFlag.start,TermCommit.heads position out,TermCommit.data P terms native out⟩:=
    configuration_ext rfl ch ct
  have hfr:Composition.restart fRun.final reset.start=
      ⟨reset.start,TermCommit.heads position out,TermCommit.data P finalTerms native out⟩:=
    configuration_ext rfl fh ft
  have hfold:runFrom foldFlag 1 (Composition.restart c.final foldFlag.start)=some fRun:=by
    rw [hcf];exact hfRun
  have hreset:runFrom reset (bootstrapBudget B) (Composition.restart fRun.final reset.start)=some rRun:=by
    rw [hfr];exact hrRun
  obtain ⟨three,hthree,th,tt,ts⟩:=PCPPRequestNodeFields.join_three_run (SumCheck.machine k q) foldFlag reset
    _ _ _ _ c fRun rRun hcRun hfold hreset
  have hce:Composition.restart three.final TermCommit.erase.start=
      ⟨TermCommit.erase.start,TermCommit.heads position out,TermCommit.data P finalTerms next out⟩:=
    configuration_ext rfl (th.trans rh) (tt.trans rt)
  have herase:runFrom TermCommit.erase (2*P+4) (Composition.restart three.final TermCommit.erase.start)=some e:=by
    rw [hce];exact he
  have hall:=Composition.run_join (cleared k q) TermCommit.erase _ _ _ three e hthree herase
  refine ⟨next,⟨Composition.joinedReceipt three e,hall,?_,eh,et⟩,hnext⟩
  change three.steps+1+e.steps≤budget P B k
  rw [ts,es]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumFinish
