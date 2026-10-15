import Proof.CaseAnalysis.RecoveryGrammarBankUnary

/-! The same physically loaded bank also supplies the literal less-than
worker and original all/any reverse fold. No atom receives derived tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedGrammarWorker (paddedData capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem less_old_slots (j : Fin 37) :
    RecoveryBoundedGrammarLessRun.slots (j.castAdd 5)=RecoveryBoundedGrammarUnary.slots j := by
  fin_cases j <;> rfl

theorem less_old_data (C D L index node limit upper : ℕ) (out : List Bool) (j : Fin 37) :
    RecoveryBoundedAddressReuse.finalData index node C D 0 limit upper L out (List.replicate C true) (j.castAdd 5)=
      RecoveryBoundedUnaryReuse.data index node C D 0 limit false out j := by
  fin_cases j <;>
    simp [RecoveryBoundedAddressReuse.finalData,RecoveryBoundedAddressReuse.paddedData,
      RecoveryBoundedAddressReuse.caps,RecoveryBoundedAddressFinish.data,RecoveryBoundedAddress.data,
      Fin.addCases]

theorem less_ports (C D L index node limit upper B : ℕ) (out stack packet source : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B) (j : Fin 42) :
    ZeroPadding.pad (capacity B (RecoveryBoundedGrammarLessRun.slots j))
      (RecoveryBoundedAddressReuse.finalData index node C D 0 limit upper L out (List.replicate C true) j)=
      ready (RecoveryBoundedGrammarPrototype.fields C index 0 limit upper)
        node B out stack packet source (RecoveryBoundedGrammarLessRun.slots j) := by
  refine Fin.addCases (m:=37) (n:=5) ?_ ?_ j
  · intro k
    rw [less_old_slots,less_old_data]
    exact unary_ports C D index node 0 limit upper B out stack packet source hC hD k
  · intro k
    have hc : ZeroPadding.pad B (ZeroPadding.pad C [])=List.replicate B false := by
      rw [MatrixBucketRootPower.pad_pad C B [] (by omega)]
      simp [ZeroPadding.pad]
    have hl : ZeroPadding.pad B (List.replicate L false)=List.replicate B false:=
      RecoveryBoundedSelectorLoop.pad_erased B L hL
    have hz : ZeroPadding.pad B []=List.replicate B false:=by simp [ZeroPadding.pad]
    fin_cases k <;>
      simp [RecoveryBoundedGrammarLessRun.slots,capacity,ready,RecoveryBoundedRowReload.loaded_apply,
        RecoveryBoundedRowReload.ports,RecoveryBoundedGrammarPrototype.fields,base,
        RecoveryBoundedAddressReuse.finalData,RecoveryBoundedAddressReuse.paddedData,
        RecoveryBoundedAddressReuse.caps,RecoveryBoundedAddressFinish.data,RecoveryBoundedAddress.data,
        Fin.addCases,hc,hl,hz]

noncomputable def lessInput (C D L index node limit upper B : ℕ) (out stack packet source : List Bool):=
  install RecoveryBoundedGrammarLessRun.slots
    (logicalReady (RecoveryBoundedGrammarPrototype.fields C index 0 limit upper) node B out stack packet source)
    (RecoveryBoundedAddressReuse.finalData index node C D 0 limit upper L out (List.replicate C true))

theorem less_padding (C D L index node limit upper B : ℕ) (out stack packet source : List Bool)
    (hC : C+1≤B) (hD : D≤B) (hL : L≤B) :
    paddedData B (lessInput C D L index node limit upper B out stack packet source)=
      ready (RecoveryBoundedGrammarPrototype.fields C index 0 limit upper) node B out stack packet source := by
  rw [lessInput,padded_install _ RecoveryBoundedGrammarLessRun.slots_injective,logical_ready_padding]
  apply install_existing
  intro j
  exact (less_ports C D L index node limit upper B out stack packet source hC hD hL j).symm

theorem fold_old_slots (j : Fin 29) :
    RecoveryBoundedGrammarFoldRun.slots (j.castAdd 6)=RecoveryBoundedGrammarUnary.slots (j.castAdd 8) := by
  fin_cases j <;> rfl

theorem fold_old_data (C node : ℕ) (out pre : List Bool) (refs : List ℕ) (j : Fin 29) :
    RecoveryBoundedGrammarFold.data node C out pre refs (j.castAdd 6)=
      RecoveryBoundedUnaryReuse.data 0 node C 0 0 refs.length false out (j.castAdd 8) := by
  fin_cases j <;> rfl

theorem fold_ports (C node B : ℕ) (out pre packet source : List Bool) (refs : List ℕ)
    (hC : C+1≤B) (j : Fin 35) :
    ZeroPadding.pad (capacity B (RecoveryBoundedGrammarFoldRun.slots j))
      (RecoveryBoundedGrammarFold.data node C out pre refs j)=
      ready (RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0)
        node B out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source
        (RecoveryBoundedGrammarFoldRun.slots j) := by
  refine Fin.addCases (m:=29) (n:=6) ?_ ?_ j
  · intro k
    rw [fold_old_slots,fold_old_data]
    exact unary_ports C 0 0 node 0 refs.length 0 B out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source hC (Nat.zero_le _) (k.castAdd 8)
  · intro k
    have hc : ZeroPadding.pad B (List.replicate C false)=List.replicate B false:=
      RecoveryBoundedSelectorLoop.pad_erased B C (by omega)
    have hf : ZeroPadding.pad B [false]=List.replicate B false:=RecoveryBoundedSelectorLoop.pad_false B (by omega)
    fin_cases k <;>
      simp [RecoveryBoundedGrammarFoldRun.slots,capacity,ready,RecoveryBoundedRowReload.loaded_apply,
        RecoveryBoundedRowReload.ports,RecoveryBoundedGrammarPrototype.fields,base,
        RecoveryBoundedGrammarFold.data,Fin.addCases,hc,hf]

noncomputable def foldInput (C node B : ℕ) (out pre packet source : List Bool) (refs : List ℕ):=
  install RecoveryBoundedGrammarFoldRun.slots
    (logicalReady (RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0) node B out
      (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source)
    (RecoveryBoundedGrammarFold.data node C out pre refs)

theorem fold_padding (C node B : ℕ) (out pre packet source : List Bool) (refs : List ℕ)
    (hC : C+1≤B) :
    paddedData B (foldInput C node B out pre packet source refs)=
      ready (RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0) node B out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet source := by
  rw [foldInput,padded_install _ RecoveryBoundedGrammarFoldRun.slots_injective,logical_ready_padding]
  apply install_existing
  intro j
  exact (fold_ports C node B out pre packet source refs hC j).symm

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarBank
