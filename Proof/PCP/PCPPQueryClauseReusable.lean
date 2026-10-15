import Proof.PCP.PCPPQueryClauseErase
import Proof.Amplification.RecoveryFocusDock

/-! One whole cached clause read with physical source/scratch reset and erase.
The native pair remains at head zero with explicit reusable zero padding. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (C : ℕ) : Fin 2 → List Bool := ![List.replicate C true,List.replicate (C+1) false]
noncomputable def first := TapeEmbedding.machine 2 PCPPQueryClauseReset.machine
noncomputable def machine := Composition.machine first eraseMachine
noncomputable def entry (source : List Bool) (arity index C : ℕ) :=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ => 0) (extra C)
    (PCPPQueryClauseReset.entry source arity index C))
def data (source : List Bool) (arity index C : ℕ) (pair : List Bool) : Fin 19 → List Bool :=
  ![source,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,UnaryTemplate.tape arity,UnaryTemplate.tape index,ZeroPadding.pad C pair,
    List.replicate C false,List.replicate C true,List.replicate (C+1) false]
def heads (j : Fin 19) := if j=13 ∨ j=14 then 1 else 0
def budget {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin (2^p.clauseBits)) (C : ℕ) := 2*PCPPQueryClause.queryBudget r p i+2*C+7

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin (2^p.clauseBits)) (C : ℕ) (hC : PCPPQueryClause.queryBudget r p i+1 ≤ C) :
    ∃ receipt,runFrom machine (budget r p i C) (entry (pcppOutput r p) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=data (pcppOutput r p) r.arity i.val C
        (natListWord [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]) ∧
      receipt.final.heads=heads ∧ receipt.steps≤budget r p i C := by
  obtain ⟨raw,hr,rs,hsource,harity,hindex,hpair,hh,hsmall⟩ :=
    PCPPQueryClauseReset.lookup_run r p i C hC
  let firstRun := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra C) raw
  have firstCall := TapeEmbedding.run_embed PCPPQueryClauseReset.machine
    (fun _ : Fin 2 => 0) (extra C) _ _ raw hr
  have pt (j : Fin 17) : firstRun.final.tapes (j.castAdd 2)=raw.final.tapes j :=
    TapeEmbedding.receipt_tapes_old _ _ raw j
  have ph (j : Fin 17) : firstRun.final.heads (j.castAdd 2)=raw.final.heads j :=
    TapeEmbedding.receipt_heads_old _ _ raw j
  have hb : ∀ j,(firstRun.final.tapes (scratchSlots j)).length ≤ C := by
    intro j
    have hlt : (scratchSlots j).val < 17 := by fin_cases j <;> decide
    let k : Fin 17 := ⟨(scratchSlots j).val,hlt⟩
    have he : scratchSlots j=k.castAdd 2 := Fin.ext rfl
    rw [he,pt]
    apply hsmall
    fin_cases j <;> simp [k,scratchSlots]
  have hheads : firstRun.final.heads=heads := by
    funext j
    refine Fin.addCases (m:=17) (n:=2) (motive:=fun j => firstRun.final.heads j=heads j)
      (fun k => ?_) (fun k => ?_) j
    · rw [ph,hh]
      fin_cases k <;> rfl
    · have h := TapeEmbedding.receipt_heads_new (fun _ : Fin 2 => 0) (extra C) raw k
      exact h.trans (by fin_cases k <;> rfl)
  obtain ⟨lastRun,lastCall,lh,lt,ls⟩ := erase_run C firstRun.final.heads firstRun.final.tapes hb
    rfl rfl (by intro j; rw [hheads]; fin_cases j <;> rfl) rfl rfl
  have joined := Composition.run_join first eraseMachine _ _ _ firstRun lastRun firstCall lastCall
  have hbudget : (2*PCPPQueryClause.queryBudget r p i+2)+1+(2*C+4)=budget r p i C := by
    unfold budget
    omega
  rw [hbudget] at joined
  refine ⟨Composition.joinedReceipt firstRun lastRun,joined,?_,lh.trans hheads,?_⟩
  · change lastRun.final.tapes=_
    rw [lt]
    funext j
    fin_cases j
    · change erased C firstRun.final.tapes (0 : Fin 19)=pcppOutput r p
      rw [erased_live C _ 0 (Or.inl rfl)]
      exact (pt 0).trans hsource
    · exact erased_slot C _ 0
    · exact erased_slot C _ 1
    · exact erased_slot C _ 2
    · exact erased_slot C _ 3
    · exact erased_slot C _ 4
    · exact erased_slot C _ 5
    · exact erased_slot C _ 6
    · exact erased_slot C _ 7
    · exact erased_slot C _ 8
    · exact erased_slot C _ 9
    · exact erased_slot C _ 10
    · exact erased_slot C _ 11
    · change erased C firstRun.final.tapes (13 : Fin 19)=UnaryTemplate.tape r.arity
      rw [erased_live C _ 13 (Or.inr (Or.inl rfl))]
      exact (pt 13).trans harity
    · change erased C firstRun.final.tapes (14 : Fin 19)=UnaryTemplate.tape i.val
      rw [erased_live C _ 14 (Or.inr (Or.inr (Or.inl rfl)))]
      exact (pt 14).trans hindex
    · change erased C firstRun.final.tapes (15 : Fin 19)=_
      rw [erased_live C _ 15 (Or.inr (Or.inr (Or.inr rfl)))]
      exact (pt 15).trans hpair
    · exact erased_slot C _ 12
    · exact erased_driver C _
    · exact erased_log C _
  · change raw.steps+1+lastRun.steps≤budget r p i C
    rw [ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
