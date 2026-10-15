import Proof.PCP.PCPPRequestNodeList

/-! Only the literal node-list entry and selected final fields needed by the
existing cold header producer and the balanced-list serializer. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeList
open LocalBitMultitape PCPPRequestNodeReuse
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_tapes (C M : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 647) :
    (entry C M source pos []).tapes i=
      if i.val=0 then source else if i.val=644 then List.replicate C true
      else if i.val=646 then CompareMachine.word M else [] := by
  refine Fin.addCases (m:=646) (n:=1) (fun j => ?_) (fun j => ?_) i
  · have h646 : j.val≠646 := by omega
    simp only [entry,input,Fin.addCases_left,PCPPRequestNodeStart.input,
      Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,
      show (643 : Fin 646).val=643 from rfl,show (644 : Fin 646).val=644 from rfl,
      h646,ite_false]
    split_ifs <;> first | rfl | omega
  · fin_cases j
    rfl

theorem entry_heads (C M : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 647) :
    (entry C M source pos []).heads i=if i.val=0 then pos else if i.val=646 then 1 else 0 := by
  refine Fin.addCases (m:=646) (n:=1) (fun j => ?_) (fun j => ?_) i
  · have h646 : j.val≠646 := by omega
    simp only [entry,heads,Fin.addCases_left,bodyHeads,List.length_nil,
      Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,h646,ite_false,ite_self]
  · fin_cases j
    rfl

theorem stream_run {n : ℕ} (pre : List Bool) (nodes : List (BooleanNode n))
    (suffix : List Bool) (C : ℕ)
    (hcap : ∀ node∈nodes,PCPPRequestNodeCold.budget node+1 ≤ C) :
    ∃ r,runFrom machine (budget C nodes.length)
      (entry C nodes.length (pre++PCPPRequestNodeLoop.stream nodes++suffix) pre.length [])=some r ∧
      r.final.tapes 0=pre++PCPPRequestNodeLoop.stream nodes++suffix ∧
      r.final.heads 0=pre.length+(PCPPRequestNodeLoop.stream nodes).length ∧
      r.final.tapes 643=PCPPRequestNodeLoop.encoded nodes ∧
      r.final.heads 643=(PCPPRequestNodeLoop.encoded nodes).length ∧
      r.final.tapes 644=List.replicate C true ∧ r.final.heads 644=0 ∧
      r.final.tapes 646=CompareMachine.word nodes.length ∧ r.final.heads 646=1 ∧
      r.steps ≤ budget C nodes.length := by
  obtain ⟨r,hr,rh,rt,rs⟩ := cold_run pre nodes suffix [] C hcap
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,?_,rs⟩
  · rw [rt]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_tapes,List.nil_append]
    rfl
  · rw [rh]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_heads,List.nil_append]
    rfl
  · rw [rt]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_tapes,List.nil_append]
    rfl
  · rw [rh]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_heads,List.nil_append]
    rfl
  · rw [rt]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_tapes,List.nil_append]
    rfl
  · rw [rh]
    simp only [PCPPRequestNodeLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      bodyEntry_heads,List.nil_append]
    rfl
  · rw [rt]
    rfl
  · rw [rh]
    rfl

end NearCubicWires.RepairOrdinary.PCPPRequestNodeList
