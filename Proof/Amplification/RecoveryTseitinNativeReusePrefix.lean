import Proof.Amplification.RecoveryTseitinNativeReuseErase

/-! Put the actual node run and physical local-head reset beside the retained
global erase driver. Every tape required by the erase has a checked bound. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_run {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (pre tail out : List Bool) (cap : Nat) (hcap : coldNodeBudget index node ≤ cap) :
    ∃ r,runFrom prefixMachine (2*coldNodeBudget index node+2)
      ⟨prefixMachine.start,heads pre.length out.length,data n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out cap⟩=some r ∧
      r.final.heads=heads
        (pre.length+(natWord (PCPPRequestNodeSchema.tag node).val).length+
          (natWord (PCPPRequestNodeSchema.fields node 1)).length+(natWord (PCPPRequestNodeSchema.fields node 2)).length)
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length ∧
      (∀ i,retained i → r.final.tapes i=data n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2))
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)) cap i) ∧
      r.final.tapes 1336=List.replicate cap true ∧ r.final.tapes 1337=List.replicate (cap+1) false ∧
      (∀ j,(r.final.tapes ((scratch j).castAdd 2)).length ≤ cap) ∧
      r.steps ≤ 2*coldNodeBudget index node+2 := by
  obtain ⟨base,hbase,bo,boh,bsrc,bsrch,bn,bi,bheads,bwork,blog,blogh,bs⟩:=
    masked_node_run index node hw pre tail out cap hcap
  let eh : Fin 2→Nat:=fun _=>0
  let et : Fin 2→List Bool:=![List.replicate cap true,List.replicate (cap+1) false]
  let r:=TapeEmbedding.receipt eh et base
  have hr:=TapeEmbedding.run_embed maskedMachine eh et _ _ base hbase
  have hin : TapeEmbedding.config eh et
      ⟨maskedMachine.start,maskedHeads pre out,maskedInput n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out cap⟩=
      ⟨prefixMachine.start,heads pre.length out.length,data n index
        (PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
          (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)) out cap⟩ := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=1336) (n:=2) (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.config,Fin.addCases_left] using old_head pre out j
      · fin_cases j <;> rfl
    · funext i
      refine Fin.addCases (m:=1336) (n:=2) (fun j=>?_) (fun j=>?_) i
      · simpa only [TapeEmbedding.config,Fin.addCases_left] using old_input n index _ out cap j
      · fin_cases j <;> rfl
  rw [hin] at hr
  have rt (i : Fin 1336) : r.final.tapes (i.castAdd 2)=base.final.tapes i := TapeEmbedding.receipt_tapes_old eh et base i
  have rh (i : Fin 1336) : r.final.heads (i.castAdd 2)=base.final.heads i := TapeEmbedding.receipt_heads_old eh et base i
  refine ⟨r,hr,?_,?_,?_,?_,?_,bs⟩
  · funext i
    refine Fin.addCases (m:=1336) (n:=2) (fun j=>?_) (fun j=>?_) i
    · rw [rh]
      by_cases hs : j=1062
      · subst j; exact bsrch
      by_cases ho : j=1333
      · subst j; exact boh
      have hzero : heads
          (pre.length+(natWord (PCPPRequestNodeSchema.tag node).val).length+
            (natWord (PCPPRequestNodeSchema.fields node 1)).length+(natWord (PCPPRequestNodeSchema.fields node 2)).length)
          (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)).length (j.castAdd 2)=0 := by
        unfold heads
        rw [if_neg (by intro he; have hv:=congrArg Fin.val he; exact hs (Fin.ext hv)),
          if_neg (by intro he; have hv:=congrArg Fin.val he; exact ho (Fin.ext hv))]
      rw [hzero]
      by_cases hj : j.val<1335
      · let k : Fin 1335:=⟨j.val,hj⟩
        have hk : selected k=true := by
          apply decide_eq_true
          constructor
          · intro he; have hv:=congrArg Fin.val he; exact hs (Fin.ext hv)
          · intro he; have hv:=congrArg Fin.val he; exact ho (Fin.ext hv)
        exact bheads k hk
      · have he : j=1335 := Fin.ext (by have hj':=j.isLt; omega)
        subst j; exact blogh
    · fin_cases j <;> rfl
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact (rt 0).trans bn
    · exact (rt 1).trans bi
    · exact (rt 1062).trans bsrc
    · exact (rt 1333).trans bo
  · exact TapeEmbedding.receipt_tapes_new eh et base 0
  · exact TapeEmbedding.receipt_tapes_new eh et base 1
  · intro j
    rw [rt]
    by_cases hj : (scratch j).val<1335
    · let k : Fin 1335:=⟨(scratch j).val,hj⟩
      have hk : work k := by
        have hs:=scratch_range j
        refine ⟨?_,?_,?_,?_⟩
        all_goals intro he; have hv:=congrArg Fin.val he; dsimp [k] at hv; omega
      exact bwork k hk
    · have he : scratch j=1335 := Fin.ext (by have hs:=(scratch j).isLt; omega)
      rw [he,blog,List.length_replicate]

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
