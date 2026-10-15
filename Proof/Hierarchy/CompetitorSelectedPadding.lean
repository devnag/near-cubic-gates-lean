import Proof.Hierarchy.CompetitorSelectedPaddingMeaning

/-! The selected-total machine runs with a full-square driver on the actual
short cropped source. Trailing zeros are implicit tape blanks; no padding
writer or change to the paper's estimator is assumed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open LocalBitMultitape CompetitorCountMask SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceCaps (b N : ℕ) : Fin 20 → ℕ := fun i => if i=1 then N else if i=8 then b*N else 0
noncomputable def shortTapes (b w N : ℕ) (xs : List (Bool × ℕ)) :=
  Function.update (Function.update (wholeInput b w (padded N xs)).tapes 1 (mask xs))
    8 (CompetitorCountFold.raw b (counts xs))
noncomputable def shortInput (b w N : ℕ) (xs : List (Bool × ℕ)) :=
  { (wholeInput b w (padded N xs)) with tapes := shortTapes b w N xs }

theorem source_padded (b w N : ℕ) (xs : List (Bool × ℕ)) :
    ZeroPadding.config (sourceCaps b N) (shortInput b w N xs)=wholeInput b w (padded N xs) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i
    all_goals first
      | exact ZeroPadding.pad_zero _
      | exact (padded_mask N xs).symm
      | exact (padded_counts b N xs).symm

theorem short_run (b w N : ℕ) (xs : List (Bool × ℕ)) (hn : xs.length≤N)
    (hw : b≤w) (hx : ∀ x∈selected xs,x<2^b) (hfit : (selected xs).sum<2^w) :
    ∃ actual,runFrom machine (budget b w N) (shortInput b w N xs)=some actual ∧
      actual.steps≤budget b w N ∧ actual.final.heads=finalHeads b N ∧
      actual.final.tapes 15=frame (binary w (selected xs).sum) ∧
      actual.final.tapes 12=List.replicate w true := by
  obtain ⟨base,hb,bs,bh,b15,b12,_,_⟩ := native_run b w (padded N xs) hw (padded_fit b N xs hx)
    (by rw [padded_sum];exact hfit)
  rw [padded_length N xs hn] at hb bs bh
  rw [padded_sum] at b15
  rw [←source_padded] at hb
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_unpad machine (sourceCaps b N) _ _ base hb
  refine ⟨actual,ha,hs.trans_le bs,?_,?_,?_⟩
  · exact (congrArg (fun c => c.heads) hf).trans bh
  · have h := (congrArg (fun c => c.tapes 15) hf).trans b15
    simpa only [ZeroPadding.config,sourceCaps,show (15 : Fin 20)≠1 by decide,
      show (15 : Fin 20)≠8 by decide,↓reduceIte,ZeroPadding.pad_zero] using h
  · have h := (congrArg (fun c => c.tapes 12) hf).trans b12
    simpa only [ZeroPadding.config,sourceCaps,show (12 : Fin 20)≠1 by decide,
      show (12 : Fin 20)≠8 by decide,↓reduceIte,ZeroPadding.pad_zero] using h

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
