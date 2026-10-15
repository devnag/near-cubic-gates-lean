import Proof.CaseAnalysis.RecoveryRowsFoldBank

/-! Execute the existing true/reverse-AND fold on the same retained bank.
All padding cells were already present in that bank and are preserved by
the checked zero-padding transport. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold
open LocalBitMultitape SourceInterfaces RecoveryBoundedRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Focus
variable {s : ℕ}
noncomputable def machine (p : Machine 35 s):=RecoveryFocus.machine slots p
theorem run (p : Machine 35 s) (u B : ℕ) (c : Configuration 35 s)
    (H : Fin 116→ℕ) (A : Fin 116→List Bool) (base : ExecutionReceipt 35 s)
    (hr : runFrom p u c=some base)
    (hH : ∀ j,H (slots j)=c.heads j)
    (hA : ∀ j,A (slots j)=ZeroPadding.pad (caps B j) (c.tapes j)) :
    ∃ r,runFrom (machine p) u ⟨c.control,H,A⟩=some r ∧ r.steps=base.steps ∧
      r.final.heads=(RecoveryFocus.config slots H A (ZeroPadding.config (caps B) base.final)).heads ∧
      r.final.tapes=(RecoveryFocus.config slots H A (ZeroPadding.config (caps B) base.final)).tapes := by
  obtain ⟨padded,pr,pf,ps,_⟩:=ZeroPadding.run_config p (caps B) u c base hr
  have he : RecoveryFocus.config slots H A (ZeroPadding.config (caps B) c)=
      (⟨c.control,H,A⟩ : Configuration 116 s):=
    WilliamsSourceCrop.focus_same slots (⟨c.control,H,A⟩ : Configuration 116 s) _ hH hA
  obtain ⟨r,rr,rf,rs⟩:=RecoveryFocus.run_config slots slots_injective p H A u _ padded pr
  rw [he] at rr
  rw [pf] at rf
  exact ⟨r,rr,rs.trans ps,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩
end Focus

noncomputable def machine:=Focus.machine (RecoveryBoundedGrammarFold.machine true)
noncomputable def result (node C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (P : Fin 37→List Bool):=
  RecoveryFocus.config slots (ambientHeads out pre refs)
    (ambient node C D F L B n count Q clauses out source pre packet refs P)
    (ZeroPadding.config (caps B) (RecoveryBoundedGrammarFold.finalConfiguration true node C out pre refs))

theorem fold_run (node W C D F L B n count Q clauses : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (P : Fin 37→List Bool) (href : ∀ ref∈refs,ref≤W) (ha : node+refs.length≤W)
    (hC : 16384*(W+1)^2≤C) (hCB : C+1≤B) (hD : D≤B) (hL : L≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarFold.budget true refs.length C)
      ⟨machine.start,ambientHeads out pre refs,ambient node C D F L B n count Q clauses out source pre packet refs P⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarFold.budget true refs.length C ∧
      r.final.heads=(result node C D F L B n count Q clauses out source pre packet refs P).heads ∧
      r.final.tapes=(result node C D F L B n count Q clauses out source pre packet refs P).tapes := by
  obtain ⟨base,br,bs,bh,bt⟩:=RecoveryBoundedGrammarFold.fold_run true node W C out pre refs href ha hC
  obtain ⟨r,rr,rs,rh,rt⟩:=Focus.run (RecoveryBoundedGrammarFold.machine true) _ B
    (RecoveryBoundedGrammarFold.entry true node C out pre refs) (ambientHeads out pre refs)
    (ambient node C D F L B n count Q clauses out source pre packet refs P) base br
    (input_heads out pre refs) (input_data node C D F L B n count Q clauses out source pre packet refs P hCB hD hL)
  refine ⟨r,rr,rs.le.trans bs,?_,?_⟩
  · rw [rh]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bh]
  · rw [rt]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bt]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowsFold
