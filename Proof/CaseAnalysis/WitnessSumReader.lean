import Proof.CaseAnalysis.WitnessSumReset

/-! The whole guarded header/count prefix is docked directly into the
term consumer's three shared fields. Its physical count and streams
remain the same objects throughout the sum body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem normal_slot (i : Fin 528) (h357 : i≠357) (h368 : i≠368) (h499 : i≠499) :
    slots i=i.natAdd 2533 := by
  have h357' : i.val≠357 := by intro h;exact h357 (Fin.ext h)
  have h368' : i.val≠368 := by intro h;exact h368 (Fin.ext h)
  have h499' : i.val≠499 := by intro h;exact h499 (Fin.ext h)
  simp only [slots,if_neg h357',if_neg h368',if_neg h499']
  rfl
private theorem hole_outside (j : Fin 528) (hj : j.val=357 ∨ j.val=368 ∨ j.val=499) :
    ∀ i,slots i≠j.natAdd 2533 := by
  intro i h
  have hv := congrArg (fun k : Fin 3061=>k.val) h
  change (if i.val=357 then 722 else if i.val=368 then 2532 else if i.val=499 then 724 else 2533+i.val)=2533+j.val at hv
  split_ifs at hv <;> omega
private theorem extra_heads_other (out next : List Bool) (i : Fin 528) (hi : i≠526) :
    SumCountStream.heads out i=SumCountStream.heads next i := by
  revert hi
  refine Fin.addCases (m:=510) (n:=18) ?_ ?_ i
  · intro j _;simp only [SumCountStream.heads,Fin.addCases_left]
  · intro j hj
    have hn : j.val≠16 := by intro h;exact hj (Fin.ext (by change 510+j.val=526;omega))
    simp only [SumCountStream.heads,Fin.addCases_right,SumCountStream.extraHeads,if_neg hn]
private theorem heads_other (out native counts next : List Bool) (i : Fin 3061) (hi : i≠3059) :
    heads out native counts i=heads out native next i := by
  revert hi
  refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
  · intro j _;simp only [heads,Fin.addCases_left]
  · intro j hj
    simp only [heads,Fin.addCases_right]
    exact extra_heads_other counts next j (by intro h;subst j;exact hj rfl)

private theorem core_data_other (P H b core W L : ℕ) (source next out native driver nextDriver : List Bool)
    (flag nextFlag : Bool) (ambient : Fin 94 → List Bool) (i : Fin 2533)
    (h722 : i≠722) (h724 : i≠724) (h2532 : i≠2532) :
    coreData P H b core W L source out native driver flag ambient i=
      coreData P H b core W L next out native nextDriver nextFlag ambient i := by
  revert h722 h724 h2532
  refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ i
  · intro j
    simp only [coreData,Fin.addCases_left]
    refine Fin.addCases (m:=827) (n:=1705) ?_ ?_ j
    · intro k
      simp only [TermRound.data,Fin.addCases_left]
      refine Fin.addCases (m:=826) (n:=1) ?_ ?_ k
      · intro l
        simp only [TermCommit.data,Fin.addCases_left]
        refine Fin.addCases (m:=725) (n:=101) ?_ ?_ l
        · intro z
          simp only [TermMass.data,Fin.addCases_left]
          refine Fin.addCases (m:=720) (n:=5) ?_ ?_ z
          · intro z _ _ _;simp only [TermRead.data,Fin.addCases_left]
          · intro z h722 h724 _
            simp only [TermRead.data,Fin.addCases_right]
            fin_cases z <;> first | rfl | exact (h722 rfl).elim | exact (h724 rfl).elim
        · intro z _ _ _;simp only [TermMass.data,Fin.addCases_right]
      · intro l _ _ _;simp only [TermCommit.data,Fin.addCases_right]
    · intro k _ _ _;simp only [TermRound.data,Fin.addCases_right]
  · intro j _ _ hj
    fin_cases j
    exact (hj rfl).elim

theorem reader_run (P H b core W L T : ℕ) (bits arityBits out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (hraw : 2*bits.length+1 ≤ H)
    (hbudget : SumGuard.budget bits arityBits T+1 ≤ H)
    (happend : SumHeader.flag bits arityBits T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H) :
    ∃ r,runFrom reader (SumPrefix.budget bits arityBits T)
      ⟨reader.start,heads out native counts,input P H b core W L T bits arityBits out native counts ambient⟩=some r ∧
      r.steps ≤ SumPrefix.budget bits arityBits T ∧ r.final.heads 724=0 ∧
      r.final.tapes 724=[SumHeader.flag bits arityBits T] ∧
      (SumHeader.flag bits arityBits T=true → ∃ after,
        r.final.heads=heads out native (counts++RepairRepresentation.natWord (SumFields.count bits)) ∧
        r.final.tapes=Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool)
          (coreData P H b core W L ((SumHeader.words bits).flatMap frame++SumHeader.tail H bits)
            out native (ZeroPadding.pad H (CompareMachine.word (SumFields.count bits))) true ambient) after ∧
        after 501=frame arityBits ∧ after 502=List.replicate T true ∧
        after 526=counts++RepairRepresentation.natWord (SumFields.count bits) ∧
        (∀ i : Fin 528,i≠501 → i≠502 → i≠526 → (after i).length ≤ H)) := by
  obtain ⟨base,hbase,bs,bh,bt,good⟩ := SumPrefix.prefix_run H T bits arityBits counts hraw hbudget happend
  obtain ⟨r,run,_rf,rs,rh,rt,keep⟩ := RecoveryFocus.dock slots slots_injective SumPrefix.machine _
    (heads out native counts) (input P H b core W L T bits arityBits out native counts ambient) _
    (heads_reader out native counts) (input_reader P H b core W L T bits arityBits out native counts ambient) base hbase
  refine ⟨r,run,rs.trans_le bs,(rh 499).trans bh,(rt 499).trans bt,?_⟩
  intro hp
  obtain ⟨baseHeads,arity,cap,stream,count,countWord,support⟩ := good hp
  let after := fun i : Fin 528=>r.final.tapes (i.natAdd 2533)
  have headEq : r.final.heads=heads out native (counts++RepairRepresentation.natWord (SumFields.count bits)) := by
    funext i
    by_cases hs : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,baseHeads,heads_reader]
    · exact ((keep i (by simpa using hs)).1).trans
        (heads_other out native counts _ i (by intro h;subst i;exact hs ⟨526,rfl⟩))
  refine ⟨after,headEq,?_,?_,?_,?_,?_⟩
  · funext i
    refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
      by_cases h722 : j=722
      · subst j;exact (rt 357).trans stream
      by_cases h724 : j=724
      · subst j;have h:=(rt 499).trans bt;rw [hp] at h;exact h
      by_cases h2532 : j=2532
      · subst j;exact (rt 368).trans count
      refine ((keep _ (core_outside j h722 h724 h2532)).2).trans ?_
      simpa only [input,Fin.addCases_left] using
        (core_data_other P H b core W L (List.replicate H false) _ out native (List.replicate H false) _
          false true ambient j h722 h724 h2532)
    · intro j;simp only [Fin.addCases_right,after]
  · change r.final.tapes (slots 501)=frame arityBits
    exact (rt 501).trans arity
  · change r.final.tapes (slots 502)=List.replicate T true
    exact (rt 502).trans cap
  · change r.final.tapes (slots 526)=counts++RepairRepresentation.natWord (SumFields.count bits)
    exact (rt 526).trans countWord
  · intro i h501 h502 h526
    by_cases hh : i.val=357 ∨ i.val=368 ∨ i.val=499
    · have retained := (keep (i.natAdd 2533) (hole_outside i hh)).2
      change (r.final.tapes (i.natAdd 2533)).length ≤ H
      rw [retained,input,Fin.addCases_right]
      have h1 : i.val≠1 := by omega
      have h501' : i.val≠501 := by intro h;exact h501 (Fin.ext h)
      have h502' : i.val≠502 := by intro h;exact h502 (Fin.ext h)
      have h526' : i.val≠526 := by intro h;exact h526 (Fin.ext h)
      simp only [extra,if_neg h1,if_neg h501',if_neg h502',if_neg h526',List.length_replicate]
      exact le_rfl
    · have h357 : i≠357 := by intro h;subst i;exact hh (Or.inl rfl)
      have h368 : i≠368 := by intro h;subst i;exact hh (Or.inr (Or.inl rfl))
      have h499 : i≠499 := by intro h;subst i;exact hh (Or.inr (Or.inr rfl))
      change (r.final.tapes (i.natAdd 2533)).length ≤ H
      rw [←normal_slot i h357 h368 h499,rt]
      exact support i h501 h502 h526

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
