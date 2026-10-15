import Proof.CaseAnalysis.WitnessSumCursor

/-! The complete term loop and final mass decision run beside the retained
sum parser bank. Only the actual count driver carries its already-paid
zero allocation; no record stream is padded or copied at this join. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads (position driver : ℕ) (out native counts : List Bool) : Fin 3061 → ℕ :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>ℕ)
    (SumDock.coreHeads position driver out native) (SumCountStream.heads counts)
def data (P H b core W L K : ℕ) (source out native : List Bool)
    (ambient : Fin 94 → List Bool) (extra : Fin 528 → List Bool) : Fin 3061 → List Bool :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool)
    (SumDock.coreData P H b core W L source out native
      (ZeroPadding.pad H (CompareMachine.word K)) true ambient) extra
def pads (H : ℕ) (i : Fin 2533) := if i=2532 then H else 0

private theorem padded_data (H : ℕ) (left : Fin 2532 → List Bool) (driver : List Bool) :
    (fun i=>ZeroPadding.pad (pads H i)
      (Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool) left (fun _=>driver) i))=
    Fin.addCases (m:=2532) (n:=1) (motive:=fun _=>List Bool) left (fun _=>ZeroPadding.pad H driver) := by
  funext i
  refine Fin.addCases (m:=2532) (n:=1) ?_ ?_ i
  · intro j
    have hj : j.castAdd 1≠(2532 : Fin 2533) := by intro h;have hv:=congrArg Fin.val h;change j.val=2532 at hv;omega
    simp only [Fin.addCases_left,pads,if_neg hj,ZeroPadding.pad_zero]
  · intro j
    fin_cases j
    simp only [Fin.addCases_right]
    rfl

theorem prepared_run {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (words : List (List Bool)) (tail out native counts : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord : List Bool → List Bool)
    (ambient : Fin 94 → List Bool) (extra : Fin 528 → List Bool)
    (hC : 0 < C) (hK : words.length ≤ T)
    (hread : ∀ bits∈words,TermCoefficient.budget C bits+1 ≤ P)
    (hraw : ∀ bits∈words,2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ bits∈words,TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel bits ≤ cost)
    (worker : TermLoop.CircuitSupplier circuit P H core W L circuitFuel words circuitPass nativeWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (SumDock.body circuit k q) (SumBody.budget P (width T (natBitLength C)) k cost words.length)
      ⟨(SumDock.body circuit k q).start,heads 0 1 out native counts,
        data P H (natBitLength C) core W L words.length (words.flatMap frame++tail) out native ambient extra⟩=some r ∧
      r.steps ≤ SumBody.budget P (width T (natBitLength C)) k cost words.length ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[SumBody.passed C q words circuitPass] ∧
      (SumBody.passed C q words circuitPass=true → ∃ after,
        r.final.heads=heads (words.flatMap frame).length 1
          (TermLoop.emitted (TermLoop.coefficientWord C) words out words.length)
          (TermLoop.emitted nativeWord words native words.length) counts ∧
        r.final.tapes=data P H (natBitLength C) core W L words.length (words.flatMap frame++tail)
          (TermLoop.emitted (TermLoop.coefficientWord C) words out words.length)
          (TermLoop.emitted nativeWord words native words.length) after extra ∧
        Store (width T (natBitLength C)) zero [] after) := by
  obtain ⟨base,hbase,bs,bh,bt,good⟩ := SumBody.sum_run circuit P H C T core W L circuitFuel cost k q
    words [] tail out native circuitPass nativeWord ambient hC hK hread hraw hwidth hcap hbits hnative
    hcost worker hstore hq hk hp hd hcheck
  obtain ⟨padded,hpadded,pf,ps,_⟩ := ZeroPadding.run_config (SumBody.machine circuit k q) (pads H) _ _ base hbase
  let result:=TapeEmbedding.receipt (SumCountStream.heads counts) extra padded
  have run:=TapeEmbedding.run_embed (SumBody.machine circuit k q) (SumCountStream.heads counts) extra _ _ padded hpadded
  have inputEq : TapeEmbedding.config (SumCountStream.heads counts) extra
      (ZeroPadding.config (pads H)
        (SumControl.start (TermLoop.machine circuit) (SumBody.ending k q)
          (RepeatMachine.cfg 0
            (TermLoop.entry circuit P H C core W L words [] tail out native nativeWord 0 ambient) words.length 1)))=
      (⟨(SumDock.body circuit k q).start,heads 0 1 out native counts,
        data P H (natBitLength C) core W L words.length (words.flatMap frame++tail) out native ambient extra⟩ :
        Configuration 3061 _) := by
    apply configuration_ext
    · rfl
    · simp only [TapeEmbedding.config,ZeroPadding.config,SumControl.start,controlConfig,
        RepeatMachine.cfg,TermLoop.entry,TermLoop.position,TermLoop.emitted,List.take_zero,List.flatMap_nil,
        List.length_nil,List.append_nil,Nat.zero_add,heads,SumDock.coreHeads]
    · simp only [TapeEmbedding.config,ZeroPadding.config,SumControl.start,controlConfig,
        RepeatMachine.cfg,TermLoop.entry,TermLoop.emitted,List.take_zero,List.flatMap_nil,List.append_nil,
        List.nil_append,data,SumDock.coreData,padded_data]
  rw [inputEq] at run
  have ph : padded.final.heads=base.final.heads := by rw [pf];rfl
  have pt : padded.final.tapes=(fun i=>ZeroPadding.pad (pads H i) (base.final.tapes i)) := by rw [pf];rfl
  refine ⟨result,run,ps.trans_le bs,?_,?_,?_⟩
  · change padded.final.heads 724=0
    rw [ph];exact bh
  · change padded.final.tapes 724=_
    rw [pt]
    simp only [pads,show (724 : Fin 2533)≠2532 by decide,↓reduceIte,ZeroPadding.pad_zero,bt]
  · intro accepted
    obtain ⟨after,ah,afterTapes,store⟩:=good accepted
    refine ⟨after,?_,?_,store⟩
    · change Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>ℕ) padded.final.heads (SumCountStream.heads counts)=_
      rw [ph,ah]
      simp only [SumBody.heads,TermLoop.position,List.take_length,List.length_nil,Nat.zero_add,heads,SumDock.coreHeads]
    · change Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool) padded.final.tapes extra=_
      rw [pt,afterTapes]
      simp only [SumBody.data,List.nil_append,padded_data,data,SumDock.coreData]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
