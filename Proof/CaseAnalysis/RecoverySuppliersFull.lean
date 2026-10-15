import Proof.CaseAnalysis.RecoverySuppliersProjectionKeep

/-! The original FULL oracle cap is computed from the actually produced raw
R. Its raw and Compare outputs dock directly to155 and152. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
open VerifierDecoding RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def fullMachine (k d : ℕ):=RecoveryFocus.machine (fullSlots source k d) (RecoveryFullBound.machine d)
def fullData (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool):=
  install (fullSlots source k d) (projectionData source k d A C P) F

theorem full_input (k d R : ℕ) (word : List Bool) (W : ℕ)
    (A : Fin (tapes source k d)→List Bool) (C : Fin 49→List Bool) (P : Fin 113→List Bool)
    (hR : P 109=List.replicate R true)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ A i=input source k d word W i)
    (j : Fin (RecoveryFullBound.tapes d)) :
    projectionData source k d A C P (fullSlots source k d j)=RecoveryFullBound.input d R j:=by
  by_cases hs : j=RecoveryFullBound.sourceSlot d
  · subst j
    rw [full_source]
    exact (projection_raw_r source k d A C P).trans hR
  have hin : RecoveryFullBound.input d R j=[]:=by
    simp only [RecoveryFullBound.input,if_neg (show j.val≠0 from fun he=>hs (Fin.ext he))]
  rw [hin]
  by_cases hraw : j=RecoveryFullBound.rawSlot d
  · subst j
    rw [full_raw,projection_old source k d A C P 155 (Or.inr (by decide))
      (by decide) (by decide) (by decide) (by decide),
      capacity_old source k d A C 155 (by decide) (by decide) (by decide)]
    exact hblank 155 (by decide) (by decide) (by decide)
  by_cases hcompare : j=RecoveryFullBound.compareSlot d
  · subst j
    rw [full_compare,projection_old source k d A C P 152 (Or.inr (by decide))
      (by decide) (by decide) (by decide) (by decide),
      capacity_old source k d A C 152 (by decide) (by decide) (by decide)]
    exact hblank 152 (by decide) (by decide) (by decide)
  · simp only [fullSlots,if_neg hs,if_neg hraw,if_neg hcompare]
    have hf : base source k+1+49+113 ≤ (fullWork source k d j).val:=by
      change base source k+1+49+113≤base source k+1+49+113+j.val
      omega
    rw [projection_far source k d A C P _ hf]
    exact (hfar _ (by omega)).trans (input_fresh source k d word W _ (by omega))

theorem full_heads (k d : ℕ) (H : Fin (tapes source k d)→ℕ)
    (hold : ∀ i : Fin 158,H (old source k d i)=0)
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ H i=0)
    (j : Fin (RecoveryFullBound.tapes d)) : H (fullSlots source k d j)=0:=by
  dsimp only [fullSlots]
  split_ifs
  · exact hold 153
  · exact hold 155
  · exact hold 152
  · exact hfar _ (by change base source k≤base source k+1+49+113+j.val;omega)

theorem full_run (k d R : ℕ) (word : List Bool) (W : ℕ)
    (A : Fin (tapes source k d)→List Bool) (H : Fin (tapes source k d)→ℕ)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (hR : P 109=List.replicate R true)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ A i=input source k d word W i)
    (hheads : ∀ i : Fin 158,H (old source k d i)=0)
    (hfarHeads : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ H i=0) :
    ∃ F r,runFrom (fullMachine source k d) (RecoveryFullBound.budget d R)
      ⟨(fullMachine source k d).start,H,projectionData source k d A C P⟩=some r ∧
      r.steps≤RecoveryFullBound.budget d R ∧ r.final.heads=H ∧ r.final.tapes=fullData source k d A C P F ∧
      F (RecoveryFullBound.sourceSlot d)=List.replicate R true ∧
      F (RecoveryFullBound.rawSlot d)=List.replicate (oracleSizeBound d R) true ∧
      F (RecoveryFullBound.compareSlot d)=CompareMachine.word (oracleSizeBound d R):=by
  obtain ⟨F,hf,hR',hraw,hcompare⟩:=RecoveryFullBound.cold_run d R
  obtain ⟨r,hr,hh,ht,hs⟩:=hf.focus_at (fullSlots source k d) (full_injective source k d)
    H (projectionData source k d A C P) (full_input source k d R word W A C P hR hblank hfar)
    (full_heads source k d H hheads hfarHeads)
  exact ⟨F,r,hr,hs,hh,ht,hR',hraw,hcompare⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
