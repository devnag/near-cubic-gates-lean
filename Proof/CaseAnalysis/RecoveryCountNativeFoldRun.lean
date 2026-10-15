import Proof.CaseAnalysis.RecoveryCountNativeFoldBank

/-! Execute the original terminal false and reverse OR on the paid
count bank, returning its exact native graph and actual output reference. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine slots (RecoveryBoundedGrammarFold.machine false)
noncomputable def result (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool):=
  RecoveryFocus.config slots (heads out pre refs)
    (bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd)
    (ZeroPadding.config (caps B P) (RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs))

theorem fold_run (node W C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
    (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool)
    (href : ∀ ref∈refs,ref≤W) (ha : node+refs.length≤W)
    (hC : 16384*(W+1)^2≤C) (hCB : C+1≤B) (hD : D≤B) (hL : L≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarFold.budget false refs.length C)
      ⟨machine.start,heads out pre refs,bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarFold.budget false refs.length C ∧
      r.final.heads=(result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).heads ∧
      r.final.tapes=(result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes := by
  obtain ⟨base,br,bs,bh,bt⟩:=RecoveryBoundedGrammarFold.fold_run false node W C out pre refs href ha hC
  obtain ⟨padded,pr,pf,ps,_⟩:=ZeroPadding.run_config (RecoveryBoundedGrammarFold.machine false)
    (caps B P) _ _ base br
  have he : RecoveryFocus.config slots (heads out pre refs)
      (bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd)
      (ZeroPadding.config (caps B P) (RecoveryBoundedGrammarFold.entry false node C out pre refs))=
      (⟨machine.start,heads out pre refs,bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd⟩ : Configuration 153 _) :=
    WilliamsSourceCrop.focus_same slots
      (⟨machine.start,heads out pre refs,bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd⟩ : Configuration 153 _)
      _ (input_heads out pre refs)
      (input_data node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd hCB hD hL)
  obtain ⟨r,rr,rf,rs⟩:=RecoveryFocus.run_config slots slots_injective (RecoveryBoundedGrammarFold.machine false)
    (heads out pre refs) (bank node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd)
    _ _ padded pr
  rw [he] at rr
  rw [pf] at rf
  refine ⟨r,rr,(rs.trans ps).le.trans bs,?_,?_⟩
  · rw [rf]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bh]
  · rw [rf]
    simp only [result,RecoveryFocus.config,ZeroPadding.config,bt]

variable (node C D F L B P n count Q clauses total : ℕ) (out source pre packet : List Bool)
variable (refs : List ℕ) (proj : Fin 37→List Bool) (cold : Fin 33→List Bool) (bd cd : List Bool)

theorem result_slot (j : Fin 35) :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes (slots j)=
      ZeroPadding.pad (caps B P j) ((RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs).tapes j) := by
  simp only [result,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,ZeroPadding.config]

theorem result_graph (arity : ℕ) :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes 20=
      out++(RecoveryBoundedCounts.anySuffix (q:=arity) node refs).flatMap PCPPRequestNodeSchema.native := by
  have h:=result_slot node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd 20
  change _=ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs).tapes 20) at h
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarFold.output_graph arity,←RecoveryBoundedCounts.anySuffix_reverse] at h
  exact h

theorem result_output :
    (result node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd).tapes 25=
      List.replicate (node+refs.length) true := by
  have h:=result_slot node C D F L B P n count Q clauses total out source pre packet refs proj cold bd cd 25
  change _=ZeroPadding.pad 0 ((RecoveryBoundedGrammarFold.finalConfiguration false node C out pre refs).tapes 25) at h
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarFold.output_counter] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountNativeFold
