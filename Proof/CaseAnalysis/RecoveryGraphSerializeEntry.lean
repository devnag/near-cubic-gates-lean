import Proof.CaseAnalysis.RecoveryGraphSerializePrepare
import Proof.CaseAnalysis.RecoveryGraphSerializeDock

/-! Exact paid-preparation to cold-serializer projections. The old arity,
randomness width and full bound stay outside the serializer focus. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinNative
open RecoveryBoundedGrammarScalarAdd (unary)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Entry {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (H : Fin 1659→ℕ) (A : Fin 1659→List Bool) : Prop where
  heads : ∀ j,H (prepareSlots j)=RecoveryBoundedGraphSerializePrepare.heads (graph c) j
  tapes : ∀ j,A (prepareSlots j)=RecoveryBoundedGraphSerializePrepare.input n c.output.val B (graph c) j
  freshHeads : ∀ j : Fin 1506,H (j.natAdd 153)=0
  freshTapes : ∀ j : Fin 1506,A (j.natAdd 153)=[]

theorem fresh_away (i : Fin 1506) (hi : i≠0) : ∀ j,prepareSlots j≠i.natAdd 153 := by
  intro j he
  have hn : i.val≠0 := fun h=>hi (Fin.ext h)
  have hv := congrArg Fin.val he
  fin_cases j <;> simp only [prepareSlots,Fin.val_natAdd] at hv <;> norm_num at hv <;> omega

theorem prepared_projection {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (H OH : Fin 1659→ℕ) (A OA : Fin 1659→List Bool) (entry : Entry B c H A)
    (hlast : c.nodes.length=c.output.val+1)
    (hh : ∀ j,OH (prepareSlots j)=0)
    (ht : ∀ j,OA (prepareSlots j)=RecoveryBoundedGraphSerializePrepare.result n c.output.val B (graph c) j)
    (hk : ∀ i,(∀ j,prepareSlots j≠i) → OH i=H i ∧ OA i=A i) :
    ∀ j,OH (readySlots j)=0 ∧ OA (readySlots j)=RecoveryBoundedGraphSerializeReady.input B c j := by
  intro j
  refine Fin.addCases (m:=1506) (n:=1) (fun i=>?_) (fun i=>?_) j
  · rw [ready_old]
    simp only [RecoveryBoundedGraphSerializeReady.input,Fin.addCases_left]
    rw [padded_input]
    by_cases h0 : i=0
    · subst i
      exact ⟨hh 6,(ht 6).trans (RecoveryBoundedGraphSerializePrepare.result_copied n c.output.val B (graph c) 1)⟩
    by_cases h1062 : i=1062
    · subst i
      exact ⟨hh 0,(ht 0).trans (RecoveryBoundedGraphSerializePrepare.result_retained n c.output.val B (graph c) 0 (by decide))⟩
    by_cases h1339 : i=1339
    · subst i
      exact ⟨hh 1,(ht 1).trans (RecoveryBoundedGraphSerializePrepare.result_retained n c.output.val B (graph c) 1 (by decide))⟩
    by_cases h1342 : i=1342
    · subst i
      refine ⟨hh 3,?_⟩
      have h := (ht 3).trans (RecoveryBoundedGraphSerializePrepare.result_retained n c.output.val B (graph c) 3 (by decide))
      change OA 145=ZeroPadding.pad B (List.replicate (c.output.val+1) true) at h
      rw [←hlast] at h
      exact h
    rw [serializerSlots,if_neg h1062,if_neg h1339,if_neg h1342,
      if_neg h0,if_neg h1062,if_neg h1339,if_neg h1342]
    exact ⟨(hk _ (fresh_away i h0)).1.trans (entry.freshHeads i),
      (hk _ (fresh_away i h0)).2.trans (entry.freshTapes i)⟩
  · have hi : i=0 := Fin.eq_zero i
    subst hi
    change OH 1215=0 ∧ OA 1215=[]
    exact ⟨(hk _ (fresh_away 1062 (by decide))).1.trans (entry.freshHeads 1062),
      (hk _ (fresh_away 1062 (by decide))).2.trans (entry.freshTapes 1062)⟩

theorem prepared_old {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (H OH : Fin 1659→ℕ) (A OA : Fin 1659→List Bool) (entry : Entry B c H A)
    (hh : ∀ j,OH (prepareSlots j)=0)
    (ht : ∀ j,OA (prepareSlots j)=RecoveryBoundedGraphSerializePrepare.result n c.output.val B (graph c) j)
    (hk : ∀ i,(∀ j,prepareSlots j≠i) → OH i=H i ∧ OA i=A i)
    (i : Fin 1659) (hi : i.val<153) (h20 : i≠20) (h25 : i≠25) (h145 : i≠145) :
    OH i=H i ∧ OA i=A i := by
  by_cases hs : ∃ j,prepareSlots j=i
  · obtain ⟨j,rfl⟩ := hs
    fin_cases j
    · exact False.elim (h20 rfl)
    · exact False.elim (h25 rfl)
    · exact ⟨(hh 2).trans (entry.heads 2).symm,
        ((ht 2).trans (RecoveryBoundedGraphSerializePrepare.result_copied n c.output.val B (graph c) 0)).trans (entry.tapes 2).symm⟩
    · exact False.elim (h145 rfl)
    · exact ⟨(hh 4).trans (entry.heads 4).symm,
        ((ht 4).trans (RecoveryBoundedGraphSerializePrepare.result_retained n c.output.val B (graph c) 4 (by decide))).trans (entry.tapes 4).symm⟩
    · exact ⟨(hh 5).trans (entry.heads 5).symm,
        ((ht 5).trans (RecoveryBoundedGraphSerializePrepare.result_copied n c.output.val B (graph c) 2)).trans (entry.tapes 5).symm⟩
    · change 153<153 at hi
      omega
  · exact hk i (by intro j he;exact hs ⟨j,he⟩)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
