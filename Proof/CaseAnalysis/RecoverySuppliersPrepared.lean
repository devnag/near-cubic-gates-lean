import Proof.CaseAnalysis.RecoverySuppliersFullKeep

/-! Exact equality with the original prepared recovery consumer. The clause
stream has its literal empty tail, and FULL bound is distinct from backing B. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem shared_data (k d B : ℕ) (clauseWord : List Bool)
    (A : Fin (tapes source k d)→List Bool) (C : Fin 49→List Bool)
    (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (h70 : A (old source k d 70)=clauseWord) (hB : P 104=List.replicate B true)
    (hlog : C 48=List.replicate (B+1) false) (i : Fin 78) :
    fullData source k d A C P F (old source k d ⟨i.val,by omega⟩)=
      RecoveryBoundedColdPrepared.shared B clauseWord i:=by
  have hi:=i.isLt
  by_cases h0 : i=70
  · subst i
    change fullData source k d A C P F (old source k d 70)=clauseWord
    exact (final_original source k d A C P F 70 (Or.inl (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h70
  by_cases h1 : i=76
  · subst i
    change fullData source k d A C P F (old source k d 76)=List.replicate B true
    rw [full_old source k d A C P F 76 (by decide) (by decide) (by decide)]
    exact (projection_backing source k d A C P).trans hB
  by_cases h2 : i=77
  · subst i
    change fullData source k d A C P F (old source k d 77)=List.replicate (B+1) false
    rw [full_old source k d A C P F 77 (by decide) (by decide) (by decide),
      projection_old source k d A C P 77 (Or.inl (by decide))
        (by decide) (by decide) (by decide) (by decide)]
    exact (capacity_log source k d A C).trans hlog
  simp only [RecoveryBoundedColdPrepared.shared,if_neg h0,if_neg h1,if_neg h2]
  rw [final_original source k d A C P F ⟨i.val,by omega⟩ (Or.inl hi)
    (fun he=>h1 (Fin.ext (congrArg (fun z : Fin 158=>z.val) he)))
    (fun he=>h2 (Fin.ext (congrArg (fun z : Fin 158=>z.val) he)))
    (by intro he;have hv:=congrArg Fin.val he;change i.val=115 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=152 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=153 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=154 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=155 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=156 at hv;omega)]
  exact hblank _ (fun he=>h0 (Fin.ext (congrArg (fun z : Fin 158=>z.val) he)))
    (by intro he;have hv:=congrArg Fin.val he;change i.val=106 at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=157 at hv;omega)

theorem prepared_data (k d R bound Cval Q clauses B : ℕ)
    (proj : Fin 37→List Bool) (clauseWord : List Bool)
    (A : Fin (tapes source k d)→List Bool) (C : Fin 49→List Bool)
    (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (h70 : A (old source k d 70)=clauseWord) (h157 : A (old source k d 157)=List.replicate clauses true)
    (hC : C 7=List.replicate Cval true) (hlog : C 48=List.replicate (B+1) false)
    (hproj : ∀ i,P (RecoveryProjectionCold.bankSlots i)=proj i)
    (hrows : P 106=CompareMachine.word (2^R)) (hQ : P 111=List.replicate Q true)
    (hB : P 104=List.replicate B true)
    (hR : F (RecoveryFullBound.sourceSlot d)=List.replicate R true)
    (hraw : F (RecoveryFullBound.rawSlot d)=List.replicate bound true)
    (hcompare : F (RecoveryFullBound.compareSlot d)=CompareMachine.word bound) :
    ∀ i : Fin 158,fullData source k d A C P F (old source k d i)=
      RecoveryBoundedColdPrepared.input R bound Cval Q clauses B proj clauseWord i:=by
  refine Fin.addCases (m:=153) (n:=5) (fun i=>?_) (fun i=>?_)
  · refine Fin.addCases (m:=116) (n:=37) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=78) (n:=38) (fun z=>?_) (fun z=>?_) j
      · simp only [RecoveryBoundedColdPrepared.input,Fin.addCases_left]
        change fullData source k d A C P F (old source k d ⟨z.val,by omega⟩)=
          RecoveryBoundedColdPrepared.shared B clauseWord z
        exact shared_data source k d B clauseWord A C P F hblank h70 hB hlog z
      · refine Fin.addCases (m:=37) (n:=1) (fun t=>?_) (fun t=>?_) z
        · simp only [RecoveryBoundedColdPrepared.input,Fin.addCases_left,Fin.addCases_right,
            RecoveryBoundedFixedRestart.extra]
          change fullData source k d A C P F (old source k d ⟨78+t.val,by omega⟩)=proj t
          have ht:=t.isLt
          rw [full_old source k d A C P F ⟨78+t.val,by omega⟩
            (by intro he;have hv:=congrArg Fin.val he;change 78+t.val=153 at hv;omega)
            (by intro he;have hv:=congrArg Fin.val he;change 78+t.val=155 at hv;omega)
            (by intro he;have hv:=congrArg Fin.val he;change 78+t.val=152 at hv;omega)]
          exact (projection_bank_data source k d A C P t).trans (hproj t)
        · have ht : t=0:=Subsingleton.elim _ _
          subst t
          change fullData source k d A C P F (old source k d 115)=CompareMachine.word (2^R)
          rw [full_old source k d A C P F 115 (by decide) (by decide) (by decide)]
          exact (projection_rows source k d A C P).trans hrows
    · refine Fin.addCases (m:=36) (n:=1) (fun z=>?_) (fun z=>?_) j
      · simp only [RecoveryBoundedColdPrepared.input,Fin.addCases_left,Fin.addCases_right]
        change fullData source k d A C P F (old source k d ⟨116+z.val,by omega⟩)=[]
        have hz:=z.isLt
        rw [final_original source k d A C P F ⟨116+z.val,by omega⟩
          (Or.inr (by change 115 ≤ 116+z.val;omega))
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=76 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=77 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=115 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=152 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=153 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=154 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=155 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=156 at hv;omega)]
        exact hblank _
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=70 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=106 at hv;omega)
          (by intro he;have hv:=congrArg Fin.val he;change 116+z.val=157 at hv;omega)
      · have hz : z=0:=Subsingleton.elim _ _
        subst z
        change fullData source k d A C P F (old source k d 152)=CompareMachine.word bound
        exact (full_compare_data source k d A C P F).trans hcompare
  · fin_cases i
    · change fullData source k d A C P F (old source k d 153)=List.replicate R true
      exact (full_r source k d A C P F).trans hR
    · change fullData source k d A C P F (old source k d 154)=List.replicate Cval true
      rw [full_old source k d A C P F 154 (by decide) (by decide) (by decide),
        projection_old source k d A C P 154 (Or.inr (by decide))
          (by decide) (by decide) (by decide) (by decide)]
      exact (capacity_c source k d A C).trans hC
    · change fullData source k d A C P F (old source k d 155)=List.replicate bound true
      exact (full_raw_data source k d A C P F).trans hraw
    · change fullData source k d A C P F (old source k d 156)=List.replicate Q true
      rw [full_old source k d A C P F 156 (by decide) (by decide) (by decide)]
      exact (projection_raw_q source k d A C P).trans hQ
    · change fullData source k d A C P F (old source k d 157)=List.replicate clauses true
      exact (final_original source k d A C P F 157 (Or.inr (by decide))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h157

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
