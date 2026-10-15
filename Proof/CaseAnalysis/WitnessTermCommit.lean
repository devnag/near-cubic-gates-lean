import Proof.CaseAnalysis.WitnessTermRecord
import Proof.PCP.PCPPRequestNodeFieldsJoin

/-! An accepted term updates the exact mass, retains its compact coefficient,
then clears the reusable parser. All three calls share the existing driver;
the source, mass store, width and output cursor survive the whole commit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCommit
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (position : ℕ) (out : List Bool) : Fin 827→ℕ:=
  Fin.addCases (m:=826) (n:=1) (motive:=fun _=>ℕ) (TermMass.heads position) (fun _=>out.length)
def data (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out : List Bool) : Fin 827→List Bool:=
  Fin.addCases (m:=826) (n:=1) (motive:=fun _=>List Bool) (TermMass.data P terms ambient) (fun _=>out)
noncomputable def mass:=TapeEmbedding.machine 1 TermMass.machine
def eraseSlots (i : Fin 725) : Fin 827:=i.castAdd 102
noncomputable def erase:=RecoveryFocus.machine eraseSlots TermRead.eraser
noncomputable def kept:=Composition.machine mass TermRecord.machine
noncomputable def machine:=Composition.machine kept erase
def budget (P B b : ℕ):=MassReusableStep.budget P B+1+(8*b+14)+1+(2*P+4)

theorem heads_core (position : ℕ) (out : List Bool) (i : Fin 725) :
    heads position out (eraseSlots i)=TermRead.heads position i:=by
  change heads position out ((i.castAdd 101).castAdd 1)=_
  rw [heads,Fin.addCases_left,TermMass.heads,Fin.addCases_left]
theorem data_core (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out : List Bool) (i : Fin 725) : data P terms ambient out (eraseSlots i)=terms i:=by
  change data P terms ambient out ((i.castAdd 101).castAdd 1)=_
  rw [data,Fin.addCases_left,TermMass.data,Fin.addCases_left]
theorem data_outside (P : ℕ) (terms next : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out : List Bool) (i : Fin 827) (hi : ∀ j,eraseSlots j≠i) :
    data P terms ambient out i=data P next ambient out i:=by
  revert hi
  refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
    · intro k hk;exact (hk k rfl).elim
    · intro k _;simp only [data,Fin.addCases_left,TermMass.data,Fin.addCases_right]
  · intro j _;simp only [data,Fin.addCases_right]

theorem mass_run (P B b position : ℕ) (q : ℚ) (a : Estimate) (source out : List Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (hstore : Store B a source ambient) (ha : a.Valid B) (hb : b≤B)
    (hn : q.num.natAbs<2^b) (hd : q.den<2^b)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hp : terms 720=List.replicate P true) (he : terms 721=List.replicate (P+1) false)
    (hcap : MassStep.budget B+1≤P)
    (hi : ∀ i,(MassPrepare.input ambient (binary b q.num.natAbs) (binary b q.den) i).length≤P) :
    ∃ next result,runFrom mass (MassReusableStep.budget P B)
      ⟨mass.start,heads position out,data P terms ambient out⟩=some result ∧
      result.steps≤MassReusableStep.budget P B ∧ result.final.heads=heads position out ∧
      result.final.tapes=data P terms next out ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) source next:=by
  obtain ⟨next,r,hr,rs,rh,rt,store⟩:=TermMass.mass_run P B b position q a source terms ambient
    hstore ha hb hn hd hnum hden hp he hcap hi
  have h:=TapeEmbedding.run_embed TermMass.machine (fun _ : Fin 1=>out.length) (fun _=>out) _ _ r hr
  refine ⟨next,TapeEmbedding.receipt (fun _ : Fin 1=>out.length) (fun _=>out) r,h,rs,?_,?_,store⟩
  · change Fin.addCases (m:=826) (n:=1) (motive:=fun _=>ℕ) r.final.heads (fun _=>out.length)=_
    rw [rh]
    rfl
  · change Fin.addCases (m:=826) (n:=1) (motive:=fun _=>List Bool) r.final.tapes (fun _=>out)=_
    rw [rt]
    rfl

theorem record_run (P b position : ℕ) (q : ℚ) (bits out : List Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (hdecode : CanonicalWitnessCodec.decodeCanonicalRational (RadixSemantics.value bits)=some q)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hsign : terms 316=ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits))))
    (hlog : terms 723=List.replicate P false) (hwidth : 2*b+1≤P) : ∃ result,
    runFrom TermRecord.machine (8*b+14)
      ⟨TermRecord.machine.start,heads position out,data P terms ambient out⟩=some result ∧
      result.steps=8*b+14 ∧ result.final.heads=heads position (out++TermRecord.word b q) ∧
      result.final.tapes=data P terms ambient (out++TermRecord.word b q):=by
  let sign:=ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits)))
  obtain ⟨r,hr,rs,rh,rt⟩:=TermRecord.record_run P sign (binary b q.num.natAbs) (binary b q.den) out
    (heads position out) (data P terms ambient out)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i
        · exact hsign
        · exact hnum
        · exact hden
        · rfl
        · exact hlog)
    (by simpa only [binary_length] using hwidth) (by simpa only [binary_length] using hwidth)
  have ht:CoefficientRecord.budget (binary b q.num.natAbs) (binary b q.den)=8*b+14:=by
    simp only [CoefficientRecord.budget,binary_length];omega
  have hw:CoefficientRecord.produced sign (binary b q.num.natAbs) (binary b q.den)=TermRecord.word b q:=
    TermRecord.same_word P b bits q hdecode
  rw [ht] at hr rs
  rw [hw] at rh rt
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh]
    funext i
    refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
    · intro j
      rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change j.val≠826;omega)]
      simp only [heads,Fin.addCases_left]
    · intro j
      have hj:j.natAdd 826=(826 : Fin 827):=by apply Fin.ext;change 826+j.val=826;omega
      rw [hj,Function.update_self]
      rfl
  · rw [rt]
    funext i
    refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
    · intro j
      rw [Function.update_of_ne (by apply Fin.ne_of_val_ne;change j.val≠826;omega)]
      simp only [data,Fin.addCases_left]
    · intro j
      have hj:j.natAdd 826=(826 : Fin 827):=by apply Fin.ext;change 826+j.val=826;omega
      rw [hj,Function.update_self]
      rfl

theorem erase_run (P b position : ℕ) (source out : List Bool) (flag : Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool) (hP : 1≤P)
    (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length≤P)
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source flag i) : ∃ result,
    runFrom erase (2*P+4) ⟨erase.start,heads position out,data P terms ambient out⟩=some result ∧
      result.steps=2*P+4 ∧ result.final.heads=heads position out ∧
      result.final.tapes=data P (TermRead.data P b [] source flag) ambient out:=by
  obtain ⟨base,hb,bs,bh,bt⟩:=TermRead.erase_run P b position source flag terms hP hbound hwidth hextra
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock eraseSlots
    (by intro i j h;exact Fin.ext (congrArg (fun k : Fin 827=>k.val) h)) TermRead.eraser _
    (heads position out) (data P terms ambient out) _
    (heads_core position out) (data_core P terms ambient out) base hb
  refine ⟨r,hr,rs.trans bs,?_,?_⟩
  · funext i
    by_cases hs:∃ j,eraseSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,bh,heads_core]
    · exact (keep i (by simpa using hs)).1
  · funext i
    by_cases hs:∃ j,eraseSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rt,bt,data_core]
    · exact ((keep i (by simpa using hs)).2).trans
        (data_outside P terms (TermRead.data P b [] source flag) ambient out i (by simpa using hs))

theorem commit_run (P B b position : ℕ) (q : ℚ) (a : Estimate)
    (bits source out : List Bool) (flag : Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (hstore : Store B a [] ambient) (ha : a.Valid B) (hb : b≤B)
    (hn : q.num.natAbs<2^b) (hd : q.den<2^b)
    (hdecode : CanonicalWitnessCodec.decodeCanonicalRational (RadixSemantics.value bits)=some q)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hsign : terms 316=ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits))))
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source flag i)
    (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length≤P)
    (hcap : MassStep.budget B+1≤P) (hbits : 2*b+1≤P)
    (hi : ∀ i,(MassPrepare.input ambient (binary b q.num.natAbs) (binary b q.den) i).length≤P) :
    ∃ next result,runFrom machine (budget P B b)
      ⟨machine.start,heads position out,data P terms ambient out⟩=some result ∧
      result.steps≤budget P B b ∧ result.final.heads=heads position (out++TermRecord.word b q) ∧
      result.final.tapes=data P (TermRead.data P b [] source flag) next (out++TermRecord.word b q) ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) [] next:=by
  obtain ⟨next,m,hm,ms,mh,mt,store⟩:=mass_run P B b position q a [] out terms ambient
    hstore ha hb hn hd hnum hden (hextra 0) (hextra 1) hcap hi
  obtain ⟨r,hr,rs,rh,rt⟩:=record_run P b position q bits out terms next hdecode hnum hden hsign (hextra 3) hbits
  obtain ⟨e,he,es,eh,et⟩:=erase_run P b position source (out++TermRecord.word b q) flag terms next
    (by omega) hbound hwidth hextra
  have hmr:Composition.restart m.final TermRecord.machine.start=
      ⟨TermRecord.machine.start,heads position out,data P terms next out⟩:=configuration_ext rfl mh mt
  have hre:Composition.restart r.final erase.start=
      ⟨erase.start,heads position (out++TermRecord.word b q),data P terms next (out++TermRecord.word b q)⟩:=
    configuration_ext rfl rh rt
  have hr':runFrom TermRecord.machine (8*b+14) (Composition.restart m.final TermRecord.machine.start)=some r:=by
    rw [hmr];exact hr
  have he':runFrom erase (2*P+4) (Composition.restart r.final erase.start)=some e:=by
    rw [hre];exact he
  obtain ⟨result,hall,oh,ot,os⟩:=PCPPRequestNodeFields.join_three_run mass TermRecord.machine erase
    _ _ _ _ m r e hm hr' he'
  refine ⟨next,result,hall,?_,oh.trans eh,ot.trans et,store⟩
  rw [os,rs,es]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCommit
