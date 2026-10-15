import Proof.Hierarchy.CompetitorFixedScalar

/-! Actual cold construction of a fixed nonnegative rational threshold's
wide numerator, wide zero negative part and short exact denominator. The
two width tapes are runtime inputs. Every constant work tape starts blank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdConstants
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 3) : Fin 6 → Fin 17 :=
  if j.val=0 then ![0,2,3,4,5,6] else if j.val=1 then ![0,7,8,9,10,11] else ![1,12,13,14,15,16]
def input (b : ℕ) : Fin 17 → List Bool := fun i =>
  if i.val=0 then List.replicate (width b) true else if i.val=1 then List.replicate b true else []
noncomputable def fieldProgram (j : Fin 3) (bits : List Bool) :=
  RecoveryFocus.machine (slots j) (CompetitorFixedScalar.machine bits)
noncomputable def machine (k p d : ℕ) := Composition.machine (fieldProgram 0 (binary k p))
  (Composition.machine (fieldProgram 1 []) (fieldProgram 2 (binary k d)))
def budget (b k : ℕ) := 20*b+8*k+45

theorem constants_run (b k p d : ℕ) (hk : k≤b) (hp : p<2^k) (hd : d<2^k) :
    ∃ out,ClockJoin.ReadyRun (machine k p d) (budget b k) (input b) out ∧
      out 0=List.replicate (width b) true ∧ out 1=List.replicate b true ∧
      out 3=frame (binary (width b) p) ∧ out 8=frame (binary (width b) 0) ∧
      out 13=frame (binary b d) := by
  obtain ⟨num,hnum,hn0,hn2⟩ := CompetitorFixedScalar.number_run (width b) k p
    (by unfold width; omega) hp
  let first := install (slots 0) (input b) num
  have hfirst := bounded_focus (slots 0) (by decide) _ _ _ hnum (input b)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨zero,hzero,hz0,hz2⟩ := CompetitorFixedScalar.scalar_run (width b) [] (by simp)
  have hiZero : ∀ i,first (slots 1 i)=CompetitorFixedScalar.input (width b) i := by
    intro i
    fin_cases i
    · exact (install_slot (slots 0) (by decide) _ num 0).trans hn0
    · exact install_other (slots 0) _ _ 7 (by decide)
    · exact install_other (slots 0) _ _ 8 (by decide)
    · exact install_other (slots 0) _ _ 9 (by decide)
    · exact install_other (slots 0) _ _ 10 (by decide)
    · exact install_other (slots 0) _ _ 11 (by decide)
  let second := install (slots 1) first zero
  have hsecond := bounded_focus (slots 1) (by decide) _ _ _ hzero first hiZero
  obtain ⟨den,hden,hd0,hd2⟩ := CompetitorFixedScalar.number_run b k d hk hd
  have hiDen : ∀ i,second (slots 2 i)=CompetitorFixedScalar.input b i := by
    intro i
    have hs : ∀ j,slots 1 j≠slots 2 i := by fin_cases i <;> decide
    have hf : ∀ j,slots 0 j≠slots 2 i := by fin_cases i <;> decide
    rw [show second (slots 2 i)=first (slots 2 i) from install_other _ _ _ _ hs,
      show first (slots 2 i)=input b (slots 2 i) from install_other _ _ _ _ hf]
    fin_cases i <;> rfl
  let out := install (slots 2) second den
  have hthird := bounded_focus (slots 2) (by decide) _ _ _ hden second hiDen
  have htail := ClockJoin.join (fieldProgram 1 []) (fieldProgram 2 (binary k d)) _ _ _ _ _ hsecond hthird
  have hall := ClockJoin.join (fieldProgram 0 (binary k p))
    (Composition.machine (fieldProgram 1 []) (fieldProgram 2 (binary k d))) _ _ _ _ _ hfirst htail
  have hc : (4*k+4*width b+9)+1+(CompetitorFixedScalar.budget (width b) []+1+(4*k+4*b+9))=
      budget b k := by simp [CompetitorFixedScalar.budget,budget,width]; omega
  rw [hc] at hall
  refine ⟨out,hall,?_,?_,?_,?_,?_⟩
  · exact (install_other (slots 2) _ _ 0 (by decide)).trans
      ((install_slot (slots 1) (by decide) _ zero 0).trans hz0)
  · exact (install_slot (slots 2) (by decide) _ den 0).trans hd0
  · exact (install_other (slots 2) _ _ 3 (by decide)).trans
      ((install_other (slots 1) _ _ 3 (by decide)).trans
        ((install_slot (slots 0) (by decide) _ num 2).trans hn2))
  · exact (install_other (slots 2) _ _ 8 (by decide)).trans
      ((install_slot (slots 1) (by decide) _ zero 2).trans hz2)
  · exact (install_slot (slots 2) (by decide) _ den 2).trans hd2

end NearCubicWires.RepairOrdinary.CompetitorThresholdConstants
