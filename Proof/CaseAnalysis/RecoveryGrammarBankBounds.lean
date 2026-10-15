import Proof.CaseAnalysis.RecoveryGrammarFinishChild

/-! Symbolic support bounds for the three original grammar atom inputs.
All scalar and prototype lengths are charged by the caller's one backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_support (C index value limit upper B : ℕ)
    (hc : C≤B) (hi : index≤B) (hv : value≤B) (hl : limit+1≤B) (hu : upper+1≤B) :
    ∀ j,(RecoveryBoundedGrammarPrototype.fields C index value limit upper j).length≤B := by
  intro j
  unfold RecoveryBoundedGrammarPrototype.fields
  split_ifs <;>
    simp only [RepairSource.VerifierDecoding.CompareMachine.word,List.length_replicate,List.length_cons,List.length_nil] <;> omega

theorem logical_base_support (node B : ℕ) (out stack packet source : List Bool)
    (hn : node≤B) (ho : out.length≤B) (hs : stack.length≤B) (hp : packet.length≤B) (ht : source.length≤B) :
    ∀ j,(logicalBase node B out stack packet source j).length≤B := by
  intro j
  fin_cases j <;> simp [logicalBase,base,hn,ho,hs,hp,ht]

theorem logical_ready_support (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool)
    (hn : node≤B) (ho : out.length≤B) (hs : stack.length≤B) (hp : packet.length≤B) (ht : source.length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B) :
    ∀ j,(logicalReady fields node B out stack packet source j).length≤B := by
  intro j
  rw [logicalReady,RecoveryBoundedRowReload.loaded_apply]
  split
  · rename_i hj
    rw [ZeroPadding.pad_length]
    exact max_le (Nat.le_refl _) (hf j hj)
  · exact logical_base_support node B out stack packet source hn ho hs hp ht j

theorem install_support {t : ℕ} (slots : Fin t→Fin 78) (A : Fin 78→List Bool)
    (data : Fin t→List Bool) (B : ℕ) (hA : ∀ i,(A i).length≤B) (hd : ∀ j,(data j).length≤B) :
    ∀ i,(install slots A data i).length≤B := by
  intro i
  unfold install
  cases RecoveryFocus.pick slots i with
  | none=>exact hA i
  | some j=>exact hd j

theorem unary_data_support (C D index node value limit B : ℕ) (out : List Bool)
    (hc : C+1≤B) (hd : D≤B) (hi : index≤B) (hn : node≤B) (hv : value≤B)
    (hl : limit+1≤B) (ho : out.length≤B) :
    ∀ j,(RecoveryBoundedUnaryReuse.data index node C D value limit false out j).length≤B := by
  intro j
  fin_cases j <;>
    simp [RecoveryBoundedUnaryReuse.data,RecoveryBoundedUnaryReuse.baseData,
      RecoveryBoundedNativeFold.oldData,RecoveryBoundedNativeFold.values,PCPPNativeClauseBank.data,
      Fin.addCases,ZeroPadding.pad_length,RepairSource.VerifierDecoding.CompareMachine.word] <;> omega

theorem unary_support (C D index node value limit upper B : ℕ) (out stack packet source : List Bool)
    (hc : C+1≤B) (hd : D≤B) (hi : index≤B) (hn : node≤B) (hv : value≤B)
    (hl : limit+1≤B) (hu : upper+1≤B)
    (ho : out.length≤B) (hs : stack.length≤B) (hp : packet.length≤B) (ht : source.length≤B) :
    ∀ j,(unaryInput C D index node value limit upper B out stack packet source j).length≤B := by
  apply install_support
  · exact logical_ready_support _ node B out stack packet source hn ho hs hp ht
      (fun j _=>fields_support C index value limit upper B (by omega) hi hv hl hu j)
  · exact unary_data_support C D index node value limit B out hc hd hi hn hv hl ho

theorem less_data_support (C D L index node limit upper B : ℕ) (out : List Bool)
    (hc : C+1≤B) (hd : D≤B) (hL : L≤B) (hi : index≤B) (hn : node≤B)
    (hl : limit+1≤B) (hu : upper+1≤B) (ho : out.length≤B) :
    ∀ j,(RecoveryBoundedAddressReuse.finalData index node C D 0 limit upper L out (List.replicate C true) j).length≤B := by
  intro j
  refine Fin.addCases (m:=37) (n:=5) ?_ ?_ j
  · intro k
    rw [less_old_data]
    exact unary_data_support C D index node 0 limit B out hc hd hi hn (Nat.zero_le _) hl ho k
  · intro k
    fin_cases k <;>
      simp [RecoveryBoundedAddressReuse.finalData,RecoveryBoundedAddressReuse.paddedData,
        RecoveryBoundedAddressReuse.caps,RecoveryBoundedAddressFinish.data,RecoveryBoundedAddress.data,
        Fin.addCases,ZeroPadding.pad_length,RepairSource.VerifierDecoding.CompareMachine.word] <;> omega

theorem less_support (C D L index node limit upper B : ℕ) (out stack packet source : List Bool)
    (hc : C+1≤B) (hd : D≤B) (hL : L≤B) (hi : index≤B) (hn : node≤B)
    (hl : limit+1≤B) (hu : upper+1≤B)
    (ho : out.length≤B) (hs : stack.length≤B) (hp : packet.length≤B) (ht : source.length≤B) :
    ∀ j,(lessInput C D L index node limit upper B out stack packet source j).length≤B := by
  apply install_support
  · exact logical_ready_support _ node B out stack packet source hn ho hs hp ht
      (fun j _=>fields_support C index 0 limit upper B (by omega) hi (Nat.zero_le _) hl hu j)
  · exact less_data_support C D L index node limit upper B out hc hd hL hi hn hl hu ho

theorem fold_data_support (C node B : ℕ) (out pre : List Bool) (refs : List ℕ)
    (hc : C+1≤B) (hn : node≤B) (hl : refs.length+1≤B) (ho : out.length≤B)
    (hs : (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤B) :
    ∀ j,(RecoveryBoundedGrammarFold.data node C out pre refs j).length≤B := by
  intro j
  refine Fin.addCases (m:=29) (n:=6) ?_ ?_ j
  · intro k
    rw [fold_old_data]
    exact unary_data_support C 0 0 node 0 refs.length B out hc (Nat.zero_le _) (Nat.zero_le _) hn
      (Nat.zero_le _) hl ho (k.castAdd 8)
  · intro k
    simp only [List.length_append] at hs
    fin_cases k <;>
      simp [RecoveryBoundedGrammarFold.data,Fin.addCases,RepairSource.VerifierDecoding.CompareMachine.word] <;> omega

theorem fold_support (C node B : ℕ) (out pre packet source : List Bool) (refs : List ℕ)
    (hc : C+1≤B) (hn : node≤B) (hl : refs.length+1≤B) (ho : out.length≤B)
    (hs : (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤B)
    (hp : packet.length≤B) (ht : source.length≤B) :
    ∀ j,(foldInput C node B out pre packet source refs j).length≤B := by
  apply install_support
  · exact logical_ready_support _ node B out _ packet source hn ho hs hp ht
      (fun j _=>fields_support C 0 0 refs.length 0 B (by omega) (Nat.zero_le _) (Nat.zero_le _) hl (by omega) j)
  · exact fold_data_support C node B out pre refs hc hn hl ho hs

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
