import Proof.MachineModel.OrdinaryMatrixScoreSetup

/-! The left score needs the negative linear form. A fixed tape permutation
of the actual reusable fold exchanges its two accumulators and native
constants; it reads the original weight bytes without rewriting signs. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreNegativeFold
open LocalBitMultitape SignedSortKey MatrixScoreFoldEntry
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 20 ≃ Fin 20 where
  toFun := ![0,1,2,3,4,5,6,7,8,9,11,10,12,13,14,15,16,17,19,18]
  invFun := ![0,1,2,3,4,5,6,7,8,9,11,10,12,13,14,15,16,17,19,18]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def swapWork (work : Fin 12 → List Bool) : Fin 12 → List Bool :=
  ![work 0,work 1,work 2,work 3,work 4,work 5,work 6,work 8,work 7,work 9,work 10,work 11]
noncomputable def machine := TapeRenaming.machine layout MatrixScoreFoldEntry.machine

theorem negative_run (weights : List ℤ) (pre suffix apre asuffix : List Bool) (p n s c cap : ℕ)
    (work : Fin 12 → List Bool) (hf : ∀ z ∈ weights,z.natAbs<2^p)
    (hw : p ≤ s+1) (hc : 4*(s+1)+3≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hp : MatrixScoreBatch.part false weights n<2^s)
    (hn : MatrixScoreBatch.part true weights n<2^s) :
    ∃ scratch : Fin 10 → List Bool,(∀ i,(scratch i).length≤c) ∧
      ∃ actual,runFrom machine (MatrixScoreFoldEntry.budget weights.length c p (s+1))
        (RecoveryCalls.restarted machine (heads pre.length apre.length)
          (tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
            (apre++frame (binary weights.length n)++asuffix) weights.length c cap (s+1) (2^s) 0 work))=some actual ∧
        actual.final.heads=heads (pre.length+(MatrixScoreCanonical.fields p weights).length)
          (apre.length+2*weights.length) ∧
        actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c (c+1) (s+1) (2^s) 0
          (accumulators c (s+1) (2^s+MatrixScoreBatch.part true weights n)
            (MatrixScoreBatch.part false weights n) scratch) ∧
        actual.steps≤MatrixScoreFoldEntry.budget weights.length c p (s+1) := by
  have hp' : 0+MatrixScoreBatch.part false weights n<2^(s+1) := by
    simp only [Nat.zero_add]
    exact hp.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  have hsw (i : Fin 12) : (swapWork work i).length≤c := by
    fin_cases i <;> first
      | exact hs 0 | exact hs 1 | exact hs 2 | exact hs 3 | exact hs 4 | exact hs 5
      | exact hs 6 | exact hs 7 | exact hs 8 | exact hs 9 | exact hs 10 | exact hs 11
  obtain ⟨scratch,hss,base,hb,bh,bt,bs⟩ := MatrixScoreFoldEntry.entry_run weights pre suffix apre asuffix
    p n c cap (s+1) 0 (2^s) (swapWork work) hf hw hc hcap hsw hp' (MatrixScoreShifted.offset_fit s _ hn)
  simp only [Nat.zero_add] at bt
  have hr := TapeRenaming.run_rename layout MatrixScoreFoldEntry.machine _ _ _ hb
  have hi : TapeRenaming.config layout
      (MatrixScoreFoldEntry.input (pre++MatrixScoreCanonical.fields p weights++suffix)
        (apre++frame (binary weights.length n)++asuffix) pre.length apre.length weights.length c cap (s+1) 0 (2^s) (swapWork work))=
      RecoveryCalls.restarted machine (heads pre.length apre.length)
        (tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c cap (s+1) (2^s) 0 work) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨scratch,hss,TapeRenaming.receipt layout base,hr,?_,?_,bs⟩
  · funext i
    fin_cases i <;> simp [TapeRenaming.receipt,TapeRenaming.config,layout,bh,heads]
  · funext i
    fin_cases i <;> simp [TapeRenaming.receipt,TapeRenaming.config,layout,bt,tapes,accumulators]

end NearCubicWires.RepairOrdinary.MatrixScoreNegativeFold
