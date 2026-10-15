import Proof.CaseAnalysis.CloseoutRecoveryGrammarColdBank

/-! Each original grammar atom receives its next packet from the paid
printer immediately before running. The retained scalars survive the atom. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (resultHeads)
open RecoveryBoundedGrammarContinue (bank)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {s : ℕ}
noncomputable def prepared (next : Selection) (p : Machine 79 s):=
  Composition.machine (refresh next) (TapeEmbedding.machine 33 p)
def preparedBudget (C index value limit upper B fuel : ℕ):=
  refreshBudget C index value limit upper B+1+fuel

theorem prepared_run (p : Machine 79 s) (next : Selection) (C index value limit upper B P fuel : ℕ)
    (fields : Fin 78→List Bool) (node finalNode : ℕ) (out stack packet finalOut finalStack source : List Bool)
    (cold : Fin 33→List Bool)
    (hScalar : ∀ j,data fields node B P out stack packet source cold (scalarPorts next j)=ZeroPadding.pad B
      (RecoveryBoundedGrammarPrototype.scalarValues C index value limit upper j))
    (hPacket : packet.length≤B)
    (bIndex : 2*index+4≤B) (bLimit : 2*limit+4≤B) (bValue : 2*value+4≤B)
    (bUpper : 2*upper+4≤B) (bC : 2*C+4≤B)
    (bp : (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper)).length≤B)
    (r : ExecutionReceipt 79 s)
    (hr : runFrom p fuel (RecoveryBoundedGrammarStep.entry p fields node B P out stack
      (ZeroPadding.pad B (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper))) source)=some r)
    (hs : r.steps≤fuel) (rh : r.final.heads=resultHeads finalOut.length finalStack.length)
    (rt : r.final.tapes=bank (RecoveryBoundedGrammarBank.ready
      (RecoveryBoundedGrammarPrototype.fields C index value limit upper) finalNode B finalOut finalStack
      (ZeroPadding.pad B (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper))) source) B P) :
    ∃ a,runFrom (prepared next p) (preparedBudget C index value limit upper B fuel)
      (entry (prepared next p) fields node B P out stack packet source cold)=some a ∧
      a.steps≤preparedBudget C index value limit upper B fuel ∧
      a.final.heads=heads finalOut finalStack ∧
      a.final.tapes=data (RecoveryBoundedGrammarPrototype.fields C index value limit upper)
        finalNode B P finalOut finalStack
        (ZeroPadding.pad B (RecoveryBoundedRowReload.word (RecoveryBoundedGrammarPrototype.fields C index value limit upper))) source cold := by
  let nextFields:=RecoveryBoundedGrammarPrototype.fields C index value limit upper
  let nextPacket:=ZeroPadding.pad B (RecoveryBoundedRowReload.word nextFields)
  obtain ⟨a,ar,as,ah,atapes⟩:=refresh_run next C index value limit upper B
    (heads out stack) (data fields node B P out stack packet source cold)
    (fun j=>heads_high out stack _ (scalarPorts_high next j)) rfl rfl rfl rfl hScalar
    (data73 fields node B P out stack packet source cold) (data76 fields node B P out stack packet source cold)
    (data77 fields node B P out stack packet source cold)
    (by rw [data75];exact hPacket) bIndex bLimit bValue bUpper bC bp
  rw [packet_data] at atapes
  let b:=TapeEmbedding.receipt (fun _ : Fin 33=>0) cold r
  have br:=TapeEmbedding.run_embed p (fun _ : Fin 33=>0) cold fuel _ r hr
  have br' : runFrom (TapeEmbedding.machine 33 p) fuel (restart a.final (TapeEmbedding.machine 33 p).start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have whole:=Composition.run_join (refresh next) (TapeEmbedding.machine 33 p) _ _ _ a b ar br'
  refine ⟨joinedReceipt a b,whole,?_,?_,?_⟩
  · change a.steps+1+r.steps≤preparedBudget C index value limit upper B fuel
    unfold preparedBudget
    omega
  · change (Fin.addCases (m:=79) (n:=33) (motive:=fun _=>ℕ) r.final.heads (fun _ : Fin 33=>0))=heads finalOut finalStack
    rw [rh]
    rfl
  · change (Fin.addCases (m:=79) (n:=33) (motive:=fun _=>List Bool) r.final.tapes cold)=_
    rw [rt]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
