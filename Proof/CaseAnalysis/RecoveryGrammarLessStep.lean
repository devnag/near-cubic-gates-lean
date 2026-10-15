import Proof.CaseAnalysis.RecoveryGrammarUnaryStep

/-! The complete original grammar less-than atom, followed by the shared
physical output save/count increment/next-prototype reload. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedGrammarWorker (paddedData resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank)
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def less:=RecoveryBoundedGrammarContinue.after RecoveryBoundedGrammarLessRun.machine
def lessBudget (upper W ref B : ℕ) (next : Fin 78→List Bool):=
  (2*(RecoveryBoundedAddressReuse.resetBudget upper W+2)+2)+1+RecoveryBoundedGrammarAfter.budget ref B next

theorem less_run {q bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth q bound))
    (row : Fin (bound+1)) (start limit upper W D L S B P : ℕ)
    (out stack source tail : List Bool) (next : Fin 78→List Bool)
    (hblock : start+limit≤rowWidth q bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start+limit≤W)
    (hp : b.nodes.length+upper*(3*limit+1)+3*limit≤W)
    (hg : (compileExpr b (BoolExpr.any ((List.range upper).map
      (fun value=>unaryEqualsExpr row start limit value hblock)))).final.nodes.length≤W)
    (hu : upper≤W) (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W)≤D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W≤L)
    (bC : capacity W+1≤B) (bD : D≤B) (bL : L≤B) (bW : W≤B)
    (bLimit : limit+1≤B) (bUpper : upper+1≤B)
    (hS : 1≤S) (ho : out.length≤S) (hk : stack.length≤S) (hP : stack.length≤P)
    (hs : source.length≤B) (hPacket : (RecoveryBoundedRowReload.word next++tail).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(next j).length≤B)
    (hWord : (RecoveryBoundedRowReload.word next).length≤B)
    (hB : S+RecoveryBoundedAddressReuse.resetBudget upper W+3≤B)
    (hRef : 2*(compileExpr b (BoolExpr.any ((List.range upper).map
      (fun value=>unaryEqualsExpr row start limit value hblock)))).output.val+2≤B) :
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start
    let compiled:=compileExpr b (BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock)))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let fields:=RecoveryBoundedGrammarPrototype.fields (capacity W) index 0 limit upper
    ∃ r,runFrom less (lessBudget upper W compiled.output.val B next)
      (entry less fields b.nodes.length B P out stack (RecoveryBoundedRowReload.word next++tail) source)=some r ∧
      r.steps≤lessBudget upper W compiled.output.val B next ∧
      r.final.heads=resultHeads result.length (RecoveryBoundedAddress.pushed compiled.output.val stack).length ∧
      r.final.tapes=bank (RecoveryBoundedGrammarBank.ready next compiled.final.nodes.length B result
        (RecoveryBoundedAddress.pushed compiled.output.val stack) (RecoveryBoundedRowReload.word next++tail) source) B P := by
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start
  let expression:=BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock))
  let compiled:=compileExpr b expression
  let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let fields:=RecoveryBoundedGrammarPrototype.fields (capacity W) index 0 limit upper
  let packet:=RecoveryBoundedRowReload.word next++tail
  let A:=RecoveryBoundedGrammarBank.lessInput (capacity W) D L index b.nodes.length limit upper B out stack packet source
  let finalData:=RecoveryBoundedAddressReuse.finalData index compiled.output.val (capacity W) D upper limit upper L result
    (List.replicate (capacity W) true)
  let data:=paddedData B (install RecoveryBoundedGrammarLessRun.slots A finalData)
  have hAB : ∀ j,(A j).length≤B:=RecoveryBoundedGrammarBank.less_support
    (capacity W) D L index b.nodes.length limit upper B out stack packet source bC bD bL (by dsimp only [index];omega)
    (by omega) bLimit bUpper (by omega) (by omega) hPacket hs
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=RecoveryBoundedGrammarLessRun.less_run b row start limit upper W D L S B out stack A
    hblock hi hp hg hu hD hL
    (by intro j;exact install_slot RecoveryBoundedGrammarLessRun.slots RecoveryBoundedGrammarLessRun.slots_injective _ _ j)
    hS ho hk hAB hB
  have keep (i : Fin 78) (hslots : ∀ j,RecoveryBoundedGrammarLessRun.slots j≠i)
      (hport : i∉RecoveryBoundedRowReload.ports) : data i=RecoveryBoundedGrammarBank.base
      b.nodes.length B out stack packet source i := by
    exact (kept_result RecoveryBoundedGrammarLessRun.slots fields b.nodes.length B out stack packet source
      (RecoveryBoundedAddressReuse.finalData index b.nodes.length (capacity W) D 0 limit upper L out
        (List.replicate (capacity W) true)) finalData i hslots).trans
      (RecoveryBoundedGrammarBank.ready_kept fields b.nodes.length B out stack packet source i hport)
  have d20 : data 20=result := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarLessRun.slots A finalData (RecoveryBoundedGrammarLessRun.slots 20))=_
    rw [install_slot _ RecoveryBoundedGrammarLessRun.slots_injective,ZeroPadding.pad_zero]
    change ZeroPadding.pad 0 result=result
    exact ZeroPadding.pad_zero _
  have d25 : data 25=List.replicate compiled.output.val true := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarLessRun.slots A finalData (RecoveryBoundedGrammarLessRun.slots 25))=_
    rw [install_slot _ RecoveryBoundedGrammarLessRun.slots_injective,ZeroPadding.pad_zero]
    change ZeroPadding.pad 0 (List.replicate compiled.output.val true)=List.replicate compiled.output.val true
    exact ZeroPadding.pad_zero _
  have d70 : data 70=source := by rw [keep 70 (by decide) (by decide)];rfl
  have d73 : data 73=List.replicate B false := by rw [keep 73 (by decide) (by decide)];rfl
  have d74 : data 74=stack++List.replicate 0 false := by rw [keep 74 (by decide) (by decide)];simp [RecoveryBoundedGrammarBank.base]
  have d75 : data 75=packet := by rw [keep 75 (by decide) (by decide)];rfl
  have d76 : data 76=List.replicate B true := by rw [keep 76 (by decide) (by decide)];rfl
  have d77 : data 77=List.replicate (B+1) false := by rw [keep 77 (by decide) (by decide)];rfl
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarFinishChild.finish_run RecoveryBoundedGrammarLessRun.machine
    (2*(RecoveryBoundedAddressReuse.resetBudget upper W+2)+2)
    (RecoveryBoundedGrammarWorker.entry RecoveryBoundedGrammarLessRun.body RecoveryBoundedGrammarLessRun.driver
      out stack (paddedData B A) B) p data next result stack source tail compiled.output.val 0 B P
    pr ps ph pt d20 d25 d70 d73 d74 d75 d76 d77 (by omega) hRef
    (fun i=>pb (RecoveryBoundedRowErase.work i) (RecoveryBoundedRowErase.work_spec i).1) hf hWord
  have hInput : paddedData B A=RecoveryBoundedGrammarBank.ready fields b.nodes.length B out stack packet source:=
    RecoveryBoundedGrammarBank.less_padding (capacity W) D L index b.nodes.length limit upper B out stack packet source bC bD bL
  rw [hInput,worker_entry,left_entry] at rr
  rw [RecoveryBoundedNodeAddress.expression_next b expression] at rt
  exact ⟨r,rr,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
