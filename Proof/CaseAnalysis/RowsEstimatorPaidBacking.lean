import Proof.CaseAnalysis.RowsEstimatorPaidPost

/-! Existing false backing is reused by the same actual machine without an erase pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Backed (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) (A : Fin (tapes a p) → List Bool) : Prop where
  output : A (old a p (WarmPrepare.spare p))=word
  work : ∀ i,∃ n,A (old a p (WarmPrepare.work p i))=List.replicate n false
  driver : ∃ n,A (old a p (WarmPrepare.driver p))=List.replicate n false
  log : ∃ n,A (old a p (WarmPrepare.log p))=List.replicate n false
  sources : ∀ i,A (old a p (WarmPrepare.source p i))=fields i
  protectedWords : ∀ i : Fin 70,i.val=52 ∨ i.val=68 →
    A (old a p (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p))))=Scanned.output row C i
  privateWords : ∀ i : Fin (ScannedClean.tapes a),∃ n,A (i.natAdd (WarmPrepare.tapes p))=List.replicate n false

def RetainedPort (a : WilliamsAlgorithm) (p : Program) (i : Fin (tapes a p)) : Prop:=
  i=old a p (WarmPrepare.spare p) ∨
    (∃ j,i=old a p (WarmPrepare.source p j)) ∨
    (∃ j : Fin 70,(j.val=52 ∨ j.val=68) ∧ i=old a p (WarmPrepare.old p (j.castAdd (CloseoutRowsRawRecord.tapes p))))
noncomputable def backingCaps (a : WilliamsAlgorithm) (p : Program) (caps : Fin (tapes a p) → ℕ)
    (i : Fin (tapes a p)):=by classical exact if RetainedPort a p i then 0 else caps i

theorem pad_false (C : ℕ) (A : List Bool) (h : ∃ n,A=List.replicate n false) :
    ∃ n,ZeroPadding.pad C A=List.replicate n false := by
  obtain ⟨n,rfl⟩:=h
  exact ⟨n+(C-n),by simp only [ZeroPadding.pad,List.length_replicate,List.replicate_add]⟩

theorem Clean.backed {a : WilliamsAlgorithm} {p : Program} {row : EquationRow.Input} {C D : ℕ}
    {word : List Bool} {fields : Fin 7 → List Bool} {A : Fin (tapes a p) → List Bool}
    (h : Clean a p row C D word fields A) (caps : Fin (tapes a p) → ℕ) :
    Backed a p row C word fields (fun i=>ZeroPadding.pad (backingCaps a p caps i) (A i)) := by
  have keep (i : Fin (tapes a p)) (hi : RetainedPort a p i) :
      ZeroPadding.pad (backingCaps a p caps i) (A i)=A i:=by
    simp only [backingCaps,if_pos hi,ZeroPadding.pad_zero]
  refine ⟨?_,?_,pad_false _ _ ⟨D,h.driver⟩,pad_false _ _ ⟨D+1,h.log⟩,?_,?_,?_⟩
  · exact (keep _ (Or.inl rfl)).trans h.output
  · intro i;exact pad_false _ _ ⟨D,h.work i⟩
  · intro i
    exact (keep _ (Or.inr (Or.inl ⟨i,rfl⟩))).trans (h.sources i)
  · intro i hi
    exact (keep _ (Or.inr (Or.inr ⟨i,hi,rfl⟩))).trans (h.protectedWords i hi)
  · intro i;exact pad_false _ _ (h.privateWords i)

theorem Owned.backed {s : ℕ} {a : WilliamsAlgorithm} {p : Program} {worker : Machine (tapes a p) s}
    {fuel bound : ℕ} {initial : Configuration (tapes a p) s} {row : EquationRow.Input} {C D : ℕ}
    {word : List Bool} {fields : Fin 7 → List Bool}
    (h : Owned a p worker fuel bound initial row C D word fields) (caps : Fin (tapes a p) → ℕ) : ∃ r,
    runFrom worker fuel (ZeroPadding.config (backingCaps a p caps) initial)=some r ∧
      r.final.heads=heads a p word ∧ r.steps ≤ bound ∧ Backed a p row C word fields r.final.tapes := by
  obtain ⟨source,hs,sh,ss,clean⟩:=h.clean
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config worker (backingCaps a p caps) fuel initial source hs
  refine ⟨r,hr,?_,rs.le.trans ss,?_⟩
  · rw [rf];exact sh
  · rw [rf];exact clean.backed caps

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
