import Proof.CaseAnalysis.RecoveryGrammarLessStep

/-! The original all/any reverse fold joins the same physical continuation.
The popped frames remain as paid false backing on the enclosing stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open RecoveryBoundedGrammarWorker (paddedData resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fold (conjunction : Bool):=
  RecoveryBoundedGrammarContinue.after (RecoveryBoundedGrammarFoldRun.machine conjunction)
def foldBudget (conjunction : Bool) (count C ref B : ℕ) (next : Fin 78→List Bool):=
  (2*(RecoveryBoundedGrammarFold.budget conjunction count C+2)+2)+1+RecoveryBoundedGrammarAfter.budget ref B next

theorem fold_run (n : ℕ) (conjunction : Bool) (base W C S B P : ℕ)
    (out pre source tail : List Bool) (refs : List ℕ) (next : Fin 78→List Bool)
    (href : ∀ ref∈refs,ref≤W) (ha : base+refs.length≤W) (hC : 16384*(W+1)^2≤C)
    (bC : C+1≤B) (bW : W≤B) (bLimit : refs.length+1≤B)
    (hS : 1≤S) (ho : out.length≤S)
    (hk : (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤S)
    (hP : pre.length+refs.length*(2*W+1)≤P)
    (hs : source.length≤B) (hPacket : (RecoveryBoundedRowReload.word next++tail).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(next j).length≤B)
    (hWord : (RecoveryBoundedRowReload.word next).length≤B)
    (hB : S+RecoveryBoundedGrammarFold.budget conjunction refs.length C+3≤B)
    (hRef : 2*(base+refs.length)+2≤B) :
    let result:=out++([BooleanNode.const conjunction]++
      RecoveryBoundedNative.foldNodes (n:=n) conjunction base refs.reverse).flatMap PCPPRequestNodeSchema.native
    let fields:=RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0
    ∃ r,runFrom (fold conjunction) (foldBudget conjunction refs.length C (base+refs.length) B next)
      (entry (fold conjunction) fields base B P out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)
        (RecoveryBoundedRowReload.word next++tail) source)=some r ∧
      r.steps≤foldBudget conjunction refs.length C (base+refs.length) B next ∧
      r.final.heads=resultHeads result.length (RecoveryBoundedAddress.pushed (base+refs.length) pre).length ∧
      r.final.tapes=bank (RecoveryBoundedGrammarBank.ready next (base+refs.length+1) B result
        (RecoveryBoundedAddress.pushed (base+refs.length) pre) (RecoveryBoundedRowReload.word next++tail) source) B P := by
  let result:=out++([BooleanNode.const conjunction]++
    RecoveryBoundedNative.foldNodes (n:=n) conjunction base refs.reverse).flatMap PCPPRequestNodeSchema.native
  let fields:=RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0
  let packet:=RecoveryBoundedRowReload.word next++tail
  let A:=RecoveryBoundedGrammarBank.foldInput C base B out pre packet source refs
  let finalData:=(RecoveryBoundedGrammarFold.finalConfiguration conjunction base C out pre refs).tapes
  let data:=paddedData B (install RecoveryBoundedGrammarFoldRun.slots A finalData)
  let z:=(RecoveryBoundedNativeFoldLoop.State.iterate conjunction refs.reverse
    ⟨base,0,0,out++RecoveryBoundedGrammarFold.bits conjunction⟩).erased
  have hz : z≤refs.length*(2*W+1) := by
    have hh:=RecoveryBoundedSelectorLoop.erased_bound conjunction W refs.reverse
      ⟨base,0,0,out++RecoveryBoundedGrammarFold.bits conjunction⟩
      (by intro ref hr;exact href ref (List.mem_reverse.mp hr))
    simpa only [List.length_reverse,Nat.zero_add] using hh
  have hAB : ∀ j,(A j).length≤B:=RecoveryBoundedGrammarBank.fold_support
    C base B out pre packet source refs bC (by omega) bLimit (by omega) (by omega) hPacket hs
  obtain ⟨p,pr,ps,ph,pt,pb⟩:=RecoveryBoundedGrammarFoldRun.fold_run conjunction base W C S B out pre refs A href ha hC
    (by intro j;exact install_slot RecoveryBoundedGrammarFoldRun.slots RecoveryBoundedGrammarFoldRun.slots_injective _ _ j)
    hS ho hk hAB hB
  have keep (i : Fin 78) (hslots : ∀ j,RecoveryBoundedGrammarFoldRun.slots j≠i)
      (hport : i∉RecoveryBoundedRowReload.ports) : data i=RecoveryBoundedGrammarBank.base
      base B out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source i := by
    exact (kept_result RecoveryBoundedGrammarFoldRun.slots fields base B out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source
      (RecoveryBoundedGrammarFold.data base C out pre refs) finalData i hslots).trans
      (RecoveryBoundedGrammarBank.ready_kept fields base B out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source i hport)
  have graph : finalData 20=result:=RecoveryBoundedGrammarFold.output_graph n conjunction base C out pre refs
  have d20 : data 20=result := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarFoldRun.slots A finalData (RecoveryBoundedGrammarFoldRun.slots 20))=_
    rw [install_slot _ RecoveryBoundedGrammarFoldRun.slots_injective,ZeroPadding.pad_zero]
    exact graph
  have d25 : data 25=List.replicate (base+refs.length) true := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarFoldRun.slots A finalData (RecoveryBoundedGrammarFoldRun.slots 25))=_
    rw [install_slot _ RecoveryBoundedGrammarFoldRun.slots_injective,ZeroPadding.pad_zero]
    exact RecoveryBoundedGrammarFold.output_counter conjunction base C out pre refs
  have d70 : data 70=source := by rw [keep 70 (by decide) (by decide)];rfl
  have d73 : data 73=List.replicate B false := by rw [keep 73 (by decide) (by decide)];rfl
  have d74 : data 74=pre++List.replicate z false := by
    change ZeroPadding.pad 0 (install RecoveryBoundedGrammarFoldRun.slots A finalData (RecoveryBoundedGrammarFoldRun.slots 31))=_
    rw [install_slot _ RecoveryBoundedGrammarFoldRun.slots_injective,ZeroPadding.pad_zero]
    change RecoveryBoundedNativeFoldLoop.stack pre []++List.replicate z false=_
    simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_nil,
      RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]
  have d75 : data 75=packet := by rw [keep 75 (by decide) (by decide)];rfl
  have d76 : data 76=List.replicate B true := by rw [keep 76 (by decide) (by decide)];rfl
  have d77 : data 77=List.replicate (B+1) false := by rw [keep 77 (by decide) (by decide)];rfl
  change p.final.heads=resultHeads (finalData 20).length pre.length at ph
  rw [graph] at ph
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarFinishChild.finish_run (RecoveryBoundedGrammarFoldRun.machine conjunction)
    (2*(RecoveryBoundedGrammarFold.budget conjunction refs.length C+2)+2)
    (RecoveryBoundedGrammarWorker.entry (RecoveryBoundedGrammarFoldRun.body conjunction) RecoveryBoundedGrammarFoldRun.driver
      out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) (paddedData B A) B)
    p data next result pre source tail (base+refs.length) z B P
    pr ps ph pt d20 d25 d70 d73 d74 d75 d76 d77 (by omega) hRef
    (fun i=>pb (RecoveryBoundedRowErase.work i) (RecoveryBoundedRowErase.work_spec i).1) hf hWord
  have hInput : paddedData B A=RecoveryBoundedGrammarBank.ready fields base B out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source:=
    RecoveryBoundedGrammarBank.fold_padding C base B out pre packet source refs bC
  rw [hInput,worker_entry,left_entry] at rr
  exact ⟨r,rr,rs,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarStep
