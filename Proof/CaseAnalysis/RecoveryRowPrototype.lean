import Proof.CaseAnalysis.RecoveryRowMetadataFields

/-! The retained prototype consists of the original row metadata words.
Reloading it after the coarse erase restores exactly the same row bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPrototype
open LocalBitMultitape RecoveryBoundedRowReuse RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_original (node C D F L n total queries clauses : ℕ) (out source : List Bool)
    (i : Fin 73) (hi : (i.castAdd 5 : Fin 78)∈RecoveryBoundedRowReload.ports) :
    fields C D F L n total queries clauses (i.castAdd 5)=
      RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses i := by
  have hm : i=1 ∨ i=22 ∨ i=35 ∨ i=41 ∨ i=42 ∨ i=44 ∨ i=46 ∨ i=50 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=60 ∨ i=72 := by
    simpa [RecoveryBoundedRowReload.ports,Fin.ext_iff] using hi
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact field1 node C D F L n total queries clauses out source
  · exact field22 node C D F L n total queries clauses out source
  · exact field35 node C D F L n total queries clauses out source
  · exact field41 node C D F L n total queries clauses out source
  · exact field42 node C D F L n total queries clauses out source
  · exact field44 node C D F L n total queries clauses out source
  · exact field46 node C D F L n total queries clauses out source
  · exact field50 node C D F L n total queries clauses out source
  · exact field53 node C D F L n total queries clauses out source
  · exact field54 node C D F L n total queries clauses out source
  · exact field55 node C D F L n total queries clauses out source
  · exact field56 node C D F L n total queries clauses out source
  · exact field57 node C D F L n total queries clauses out source
  · exact field60 node C D F L n total queries clauses out source
  · exact field72 node C D F L n total queries clauses out source

theorem blank_original (node C D F L n total queries clauses B : ℕ) (out source : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B)
    (i : Fin 73) (hi : (i.castAdd 5 : Fin 78)∉RecoveryBoundedRowReload.ports)
    (h20 : i≠20) (h25 : i≠25) (h70 : i≠70) :
    paddedData B (RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses) i=
      List.replicate B false := by
  fin_cases i
  all_goals first
    | exact False.elim (hi (by decide))
    | exact False.elim (h20 rfl)
    | exact False.elim (h25 rfl)
    | exact False.elim (h70 rfl)
    | exact pad_erased B C (by omega)
    | exact pad_erased B (C+1) hC
    | exact pad_erased B D hD
    | exact pad_erased B L hL
    | exact pad_erased B 0 (Nat.zero_le B)

theorem reload_original (node C D F L n total queries clauses B : ℕ) (out source : List Bool)
    (A : Fin 78→List Bool) (hC : C+1≤B) (hD : D≤B) (hL : L≤B)
    (a20 : A 20=out) (a25 : A 25=List.replicate node true) (a70 : A 70=source) :
    ∀ i : Fin 73,
      RecoveryBoundedRowReload.loaded (fields C D F L n total queries clauses) B (RecoveryBoundedRowErase.data B A) (i.castAdd 5)=
        paddedData B (RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses) i := by
  intro i
  rw [RecoveryBoundedRowReload.loaded_apply]
  by_cases hm : (i.castAdd 5 : Fin 78)∈RecoveryBoundedRowReload.ports
  · rw [if_pos hm,field_original node C D F L n total queries clauses out source i hm]
    have hs : i≠20 ∧ i≠25 ∧ i≠70 := by
      constructor
      · intro he;subst i;simp [RecoveryBoundedRowReload.ports] at hm
      constructor
      · intro he;subst i;simp [RecoveryBoundedRowReload.ports] at hm
      · intro he;subst i;simp [RecoveryBoundedRowReload.ports] at hm
    simp only [paddedData,workCapacity,hs.1,hs.2.1,hs.2.2,or_self,↓reduceIte]
  · rw [if_neg hm]
    by_cases h20 : i=20
    · subst i
      change A 20=ZeroPadding.pad 0 out
      rw [ZeroPadding.pad_zero]
      exact a20
    by_cases h25 : i=25
    · subst i
      change A 25=ZeroPadding.pad 0 (List.replicate node true)
      rw [ZeroPadding.pad_zero]
      exact a25
    by_cases h70 : i=70
    · subst i
      change A 70=ZeroPadding.pad 0 source
      rw [ZeroPadding.pad_zero]
      exact a70
    · rw [blank_original node C D F L n total queries clauses B out source hC hD hL i hm h20 h25 h70]
      have ne20 : (i.castAdd 5 : Fin 78)≠20:=fun h=>h20 (Fin.ext (congrArg (fun j : Fin 78=>j.val) h))
      have ne25 : (i.castAdd 5 : Fin 78)≠25:=fun h=>h25 (Fin.ext (congrArg (fun j : Fin 78=>j.val) h))
      have ne70 : (i.castAdd 5 : Fin 78)≠70:=fun h=>h70 (Fin.ext (congrArg (fun j : Fin 78=>j.val) h))
      exact if_pos ⟨i.isLt,ne20,ne25,ne70⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPrototype
