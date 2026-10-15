import Proof.CaseAnalysis.RecoveryGrammarStepInput

/-! One complete original unary grammar atom, including its physical
output-reference save, actual-count increment and next-prototype reload. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedGrammarWorker (paddedData capacity resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem kept_result {t : ℕ} (slots : Fin t→Fin 78) (fields : Fin 78→List Bool)
    (node B : ℕ) (out stack packet source : List Bool) (input output : Fin t→List Bool)
    (i : Fin 78) (hi : ∀ j,slots j≠i) :
    paddedData B (install slots
      (install slots (RecoveryBoundedGrammarBank.logicalReady fields node B out stack packet source) input) output) i=
      RecoveryBoundedGrammarBank.ready fields node B out stack packet source i := by
  change ZeroPadding.pad (capacity B i) (install slots _ output i)=_
  rw [install_other slots _ output i hi,install_other slots _ input i hi]
  exact congrFun (RecoveryBoundedGrammarBank.logical_ready_padding fields node B out stack packet source) i

noncomputable def unary:=RecoveryBoundedGrammarContinue.after RecoveryBoundedGrammarUnary.machine
def unaryBudget (limit C ref B : ℕ) (next : Fin 78→List Bool):=
  (2*(RecoveryBoundedUnaryReuse.budget limit C+2)+2)+1+RecoveryBoundedGrammarAfter.budget ref B next

theorem unary_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit value upper W C D S B P : ℕ)
    (out stack source tail : List Bool) (next : Fin 78→List Bool)
    (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+3*limit≤W) (hC : 16384*(W+1)^2≤C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C≤D)
    (bC : C+1≤B) (bD : D≤B) (bW : W≤B) (bValue : value≤B)
    (bLimit : limit+1≤B) (bUpper : upper+1≤B)
    (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S) (hP : stack.length≤P)
    (hs : source.length≤B) (hPacket : (RecoveryBoundedRowReload.word next++tail).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(next j).length≤B)
    (hWord : (RecoveryBoundedRowReload.word next).length≤B)
    (hB : S+RecoveryBoundedUnaryReuse.budget limit C+3≤B)
    (hRef : 2*(compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val+2≤B) :
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start
    let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let fields:=RecoveryBoundedGrammarPrototype.fields C index value limit upper
    ∃ r,runFrom unary (unaryBudget limit C compiled.output.val B next)
      (entry unary fields b.nodes.length B P out stack (RecoveryBoundedRowReload.word next++tail) source)=some r ∧
      r.steps≤unaryBudget limit C compiled.output.val B next ∧
      r.final.heads=resultHeads result.length (RecoveryBoundedAddress.pushed compiled.output.val stack).length ∧
      r.final.tapes=bank (RecoveryBoundedGrammarBank.ready next compiled.final.nodes.length B result
        (RecoveryBoundedAddress.pushed compiled.output.val stack) (RecoveryBoundedRowReload.word next++tail) source) B P := by
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start
  let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
  let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let fields:=RecoveryBoundedGrammarPrototype.fields C index value limit upper
  let packet:=RecoveryBoundedRowReload.word next++tail
  let A:=RecoveryBoundedGrammarBank.unaryInput C D index b.nodes.length value limit upper B out stack packet source
  let flag:=(RecoveryBoundedUnaryReuse.forward (n:=q) row start b.nodes.length value limit out).flag
  let finalData:=RecoveryBoundedUnaryReuse.data 0 compiled.output.val C D value limit flag result
  let data:=paddedData B (install RecoveryBoundedGrammarUnary.slots A finalData)
  have hAB : ∀ j,(A j).length≤B:=RecoveryBoundedGrammarBank.unary_support
    C D index b.nodes.length value limit upper B out stack packet source bC bD (by dsimp only [index];omega)
    (by omega) bValue bLimit bUpper (by omega) (by omega) hPacket hs
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=RecoveryBoundedGrammarUnary.unary_run b row start limit value W C D S B out stack A
    hblock hi hp hC hD
    (by intro j;exact install_slot RecoveryBoundedGrammarUnary.slots RecoveryBoundedGrammarUnary.slots_injective _ _ j)
    hS ho hk hAB hB
  have keep (i : Fin 78) (hslots : ∀ j,RecoveryBoundedGrammarUnary.slots j≠i)
      (hport : i∉RecoveryBoundedRowReload.ports) : data i=RecoveryBoundedGrammarBank.base
      b.nodes.length B out stack packet source i := by
    exact (kept_result RecoveryBoundedGrammarUnary.slots fields b.nodes.length B out stack packet source
      (RecoveryBoundedUnaryReuse.data index b.nodes.length C D value limit false out) finalData i hslots).trans
      (RecoveryBoundedGrammarBank.ready_kept fields b.nodes.length B out stack packet source i hport)
  have d20 : data 20=result := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarUnary.slots A finalData (RecoveryBoundedGrammarUnary.slots 20))=_
    rw [install_slot _ RecoveryBoundedGrammarUnary.slots_injective,ZeroPadding.pad_zero]
    rfl
  have d25 : data 25=List.replicate compiled.output.val true := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarUnary.slots A finalData (RecoveryBoundedGrammarUnary.slots 25))=_
    rw [install_slot _ RecoveryBoundedGrammarUnary.slots_injective,ZeroPadding.pad_zero]
    rfl
  have d70 : data 70=source := by rw [keep 70 (by decide) (by decide)];rfl
  have d73 : data 73=List.replicate B false := by rw [keep 73 (by decide) (by decide)];rfl
  have d74 : data 74=stack++List.replicate 0 false := by rw [keep 74 (by decide) (by decide)];simp [RecoveryBoundedGrammarBank.base]
  have d75 : data 75=packet := by rw [keep 75 (by decide) (by decide)];rfl
  have d76 : data 76=List.replicate B true := by rw [keep 76 (by decide) (by decide)];rfl
  have d77 : data 77=List.replicate (B+1) false := by rw [keep 77 (by decide) (by decide)];rfl
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarFinishChild.finish_run RecoveryBoundedGrammarUnary.machine
    (2*(RecoveryBoundedUnaryReuse.budget limit C+2)+2)
    (RecoveryBoundedGrammarWorker.entry RecoveryBoundedGrammarUnary.body RecoveryBoundedGrammarUnary.driver
      out stack (paddedData B A) B) p data next result stack source tail compiled.output.val 0 B P
    pr ps ph pt d20 d25 d70 d73 d74 d75 d76 d77 (by omega) hRef
    (fun i=>pb (RecoveryBoundedRowErase.work i) (RecoveryBoundedRowErase.work_spec i).1) hf hWord
  have hInput : paddedData B A=RecoveryBoundedGrammarBank.ready fields b.nodes.length B out stack packet source:=
    RecoveryBoundedGrammarBank.unary_padding C D index b.nodes.length value limit upper B out stack packet source bC bD
  rw [hInput,worker_entry,left_entry] at rr
  rw [RecoveryBoundedNodeAddress.expression_next b (unaryEqualsExpr row start limit value hblock)] at rt
  exact ⟨r,rr,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
