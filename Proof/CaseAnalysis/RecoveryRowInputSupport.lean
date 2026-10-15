import Proof.CaseAnalysis.RecoveryRowPrototype

/-! Initial support of the SAME original verifier-row bank. The checked
prototype/blank identities handle its fixed fields; only the actual graph,
node count, source and three logical streams add input obligations. This
does not allocate any tape or replace the cold producers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryRowInputSupport
open LocalBitMultitape RecoveryBoundedRowReuse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem base_support (node C D F L n total queries clauses S : ℕ)
    (out source : List Bool) (hC : C+1≤S) (hD : D≤S) (hL : L≤S)
    (hnode : node≤S) (hout : out.length≤S) (hsource : source.length≤S)
    (hmeta : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D F L n total queries clauses j).length≤S)
    (i : Fin 73) :
    (RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses i).length≤S := by
  by_cases hm : (i.castAdd 5 : Fin 78)∈RecoveryBoundedRowReload.ports
  · rw [←RecoveryBoundedRowPrototype.field_original node C D F L n total queries clauses out source i hm]
    exact hmeta _ hm
  by_cases h20 : i=20
  · subst i;exact hout
  by_cases h25 : i=25
  · subst i
    change (List.replicate node true).length≤S
    simpa only [List.length_replicate] using hnode
  by_cases h70 : i=70
  · subst i;exact hsource
  have hp := RecoveryBoundedRowPrototype.blank_original node C D F L n total queries clauses S
    out source hC hD hL i hm h20 h25 h70
  have hl := congrArg List.length hp
  simp only [paddedData,workCapacity,h20,h25,h70,or_self,↓reduceIte,
    ZeroPadding.pad,List.length_append,List.length_replicate] at hl
  omega

theorem data_streams (node C D F L n total queries clauses : ℕ)
    (out addresses refs source stack : List Bool) (i : Fin 73) :
    RecoveryBoundedRow.data node C D F L out n total addresses refs queries source stack clauses i=
      if i=58 then addresses else if i=59 then refs else if i=71 then stack else
        RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses i := by
  fin_cases i <;> rfl

theorem data_support (node C D F L n total queries clauses S : ℕ)
    (out addresses refs source stack : List Bool) (hC : C+1≤S) (hD : D≤S) (hL : L≤S)
    (hnode : node≤S) (hout : out.length≤S) (hsource : source.length≤S)
    (haddresses : addresses.length≤S) (hrefs : refs.length≤S) (hstack : stack.length≤S)
    (hmeta : ∀ j∈RecoveryBoundedRowReload.ports,
      (RecoveryBoundedRowPrototype.fields C D F L n total queries clauses j).length≤S)
    (i : Fin 73) :
    (RecoveryBoundedRow.data node C D F L out n total addresses refs queries source stack clauses i).length≤S := by
  rw [data_streams]
  split_ifs
  · exact haddresses
  · exact hrefs
  · exact hstack
  · exact base_support node C D F L n total queries clauses S out source
      hC hD hL hnode hout hsource hmeta i

end NearCubicWires.RepairOrdinary.CloseoutRecoveryRowInputSupport
