import Proof.CaseAnalysis.RowsSupportSumLayout

/-! The actual counted sum runs in its original parser bank with the
additional support output, preserving all old physical stream aliases. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open CloseoutWitness.SupportDock (lift)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prepared_run {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (words : List (List Bool)) (tail out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool)
    (ambient : Fin 94 → List Bool) (extra : Fin 528 → List Bool)
    (hC : 0 < C) (hK : words.length ≤ T)
    (hread : ∀ bits∈words,TermCoefficient.budget C bits+1 ≤ P)
    (hraw : ∀ bits∈words,2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ bits∈words,TermAll.budget P H C (width T (natBitLength C)) circuitFuel bits ≤ cost)
    (worker : Term.CircuitSupplier circuit P H core W L circuitFuel words circuitPass nativeWord supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (body circuit k q) (SumBody.budget P (width T (natBitLength C)) k cost words.length)
      ⟨(body circuit k q).start,lift (CloseoutWitness.SumWork.heads 0 1 out native counts) supports.length,
        lift (CloseoutWitness.SumWork.data P H (natBitLength C) core W L words.length (words.flatMap frame++tail) out native ambient extra) supports⟩=some r ∧
      r.steps ≤ SumBody.budget P (width T (natBitLength C)) k cost words.length ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[SumBody.passed C q words circuitPass] ∧
      (SumBody.passed C q words circuitPass=true → ∃ after,
        r.final.heads=lift (CloseoutWitness.SumWork.heads (words.flatMap frame).length 1
          (CloseoutWitness.TermLoop.emitted (CloseoutWitness.TermLoop.coefficientWord C) words out words.length)
          (CloseoutWitness.TermLoop.emitted nativeWord words native words.length) counts)
          (CloseoutWitness.TermLoop.emitted supportWord words supports words.length).length ∧
        r.final.tapes=lift (CloseoutWitness.SumWork.data P H (natBitLength C) core W L words.length (words.flatMap frame++tail)
          (CloseoutWitness.TermLoop.emitted (CloseoutWitness.TermLoop.coefficientWord C) words out words.length)
          (CloseoutWitness.TermLoop.emitted nativeWord words native words.length) after extra)
          (CloseoutWitness.TermLoop.emitted supportWord words supports words.length) ∧
        Store (width T (natBitLength C)) zero [] after) := by
  obtain ⟨base,hbase,bs,bh,bt,good⟩ := SumBody.sum_run circuit P H C T core W L circuitFuel cost k q
    words [] tail out native supports circuitPass nativeWord supportWord ambient hC hK hread hraw hwidth
    hcap hbits hnative hcost worker hstore hq hk hp hd hcheck
  let exchanged:=TapeRenaming.receipt (Exchange.layout 2532) base
  have exchangeRun:=TapeRenaming.run_rename (Exchange.layout 2532) (SumBody.machine circuit k q) _ _ base hbase
  have inputEq:TapeRenaming.config (Exchange.layout 2532)
      (SumControl.start (TermLoop.machine circuit) (SumBody.ending k q)
        (RepeatMachine.cfg 0 (TermLoop.entry circuit P H C core W L words [] tail out native supports nativeWord supportWord 0 ambient)
          words.length 1))=
      (⟨(renamed circuit k q).start,
        lift (CloseoutWitness.SumBody.heads 0 out (TermEnvironment.heads native)) supports.length,
        lift (CloseoutWitness.SumBody.data P words.length
          (TermRead.data P (natBitLength C) [] (words.flatMap frame++tail) true) ambient out
          (TermEnvironment.tapes H core W L native)) supports⟩ : Configuration 2534 _):=by
    apply configuration_ext
    · rfl
    · simp only [TapeRenaming.config,SumControl.start,controlConfig,RepeatMachine.cfg,TapeEmbedding.config,
        TermLoop.entry,CloseoutWitness.TermLoop.position,CloseoutWitness.TermLoop.emitted,
        List.take_zero,List.flatMap_nil,List.length_nil,List.append_nil,Nat.zero_add]
      exact Exchange.exchange (TermRound.heads 0 out (TermEnvironment.heads native)) supports.length 1
    · simp only [TapeRenaming.config,SumControl.start,controlConfig,RepeatMachine.cfg,TapeEmbedding.config,
        TermLoop.entry,CloseoutWitness.TermLoop.emitted,List.take_zero,List.flatMap_nil,List.append_nil,List.nil_append]
      exact Exchange.exchange (TermRound.data P (TermRead.data P (natBitLength C) []
        (words.flatMap frame++tail) true) ambient out (TermEnvironment.tapes H core W L native)) supports
        (CompareMachine.word words.length)
  rw [inputEq] at exchangeRun
  obtain ⟨padded,hpadded,pf,ps,_⟩:=ZeroPadding.run_config (renamed circuit k q) (pads H) _ _ exchanged exchangeRun
  have ph:padded.final.heads=exchanged.final.heads:=by rw [pf];rfl
  have pt:padded.final.tapes=(fun i=>ZeroPadding.pad (pads H i) (exchanged.final.tapes i)):=by rw [pf];rfl
  obtain ⟨result,run,rs,rh,rt⟩:=AppendBank.run_any (renamed circuit k q) _ _
    (SumCountStream.heads counts) extra padded hpadded
  have dockHeads:AppendBank.push
      (lift (CloseoutWitness.SumBody.heads 0 out (TermEnvironment.heads native)) supports.length)
      (SumCountStream.heads counts)=
      lift (CloseoutWitness.SumWork.heads 0 1 out native counts) supports.length:=by
    rw [AppendBank.push_lift];rfl
  have dockTapes:AppendBank.push (fun i=>ZeroPadding.pad (pads H i)
      (lift (CloseoutWitness.SumBody.data P words.length
        (TermRead.data P (natBitLength C) [] (words.flatMap frame++tail) true) ambient out
        (TermEnvironment.tapes H core W L native)) supports i)) extra=
      lift (CloseoutWitness.SumWork.data P H (natBitLength C) core W L words.length
        (words.flatMap frame++tail) out native ambient extra) supports:=by
    rw [padded_core,AppendBank.push_lift];rfl
  change runFrom (body circuit k q) _ _=some result at run
  simp only [ZeroPadding.config] at run
  rw [dockHeads,dockTapes] at run
  have ex724:(Exchange.layout 2532).symm (724 : Fin 2534)=724:=Exchange.old 2532 (724 : Fin 2532)
  refine ⟨result,run,by rw [rs];exact ps.trans_le bs,?_,?_,?_⟩
  · rw [rh]
    change padded.final.heads 724=0
    rw [ph]
    change base.final.heads ((Exchange.layout 2532).symm 724)=0
    rw [ex724];exact bh
  · rw [rt]
    change padded.final.tapes 724=_
    rw [pt]
    change ZeroPadding.pad 0 (base.final.tapes ((Exchange.layout 2532).symm 724))=_
    rw [ex724,ZeroPadding.pad_zero];exact bt
  · intro accepted
    obtain ⟨after,ah,afterTapes,store⟩:=good accepted
    refine ⟨after,?_,?_,store⟩
    · rw [rh,ph]
      change AppendBank.push (base.final.heads ∘ (Exchange.layout 2532).symm) (SumCountStream.heads counts)=_
      rw [ah,renamed_heads,AppendBank.push_lift]
      simp only [CloseoutWitness.TermLoop.position,List.take_length,List.length_nil,Nat.zero_add]
      rfl
    · rw [rt,pt]
      change AppendBank.push (fun i=>ZeroPadding.pad (pads H i)
        ((base.final.tapes ∘ (Exchange.layout 2532).symm) i)) extra=_
      rw [afterTapes,renamed_data]
      simp only [List.nil_append]
      rw [padded_core,AppendBank.push_lift]
      rfl

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
