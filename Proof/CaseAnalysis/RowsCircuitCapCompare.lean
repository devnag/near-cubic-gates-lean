import Proof.CaseAnalysis.RowsCircuitDescriptionMeaning
import Proof.CaseAnalysis.ScheduleCompare

/-! Compare an actual small circuit resource with its retained policy
cap. Only the measured resource is copied into the C workspace; the cap
may be larger, is retained exactly, and creates no cap-sized scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCapCompare
open LocalBitMultitape RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads (C : ℕ) (i : Fin 6):=if i=1 then 0 else C
def input (C a b : ℕ) (i : Fin 6):=ZeroPadding.pad (pads C i) (RawCompare.input a b i)
def output (C a b : ℕ) (i : Fin 6):=ZeroPadding.pad (pads C i) (RawCompare.output a b i)

theorem budget_bound (a b : ℕ) : RawCompare.budget a b ≤ 4*a+15:=by
  unfold RawCompare.budget
  omega

theorem compare_run (C a b : ℕ) (ha : 4*a+16 ≤ C) :
    ClockJoin.ReadyRun RawCompare.machine (RawCompare.budget a b)
      (input C a b) (output C a b) ∧
      output C a b 0=ZeroPadding.pad C (List.replicate a true) ∧
      output C a b 1=List.replicate b true ∧
      (readTapeBit (output C a b 4) 0=true ↔ a ≤ b) ∧
      (∀ i : Fin 6,i≠1 → (output C a b i).length ≤ C):=by
  obtain ⟨base,hb,bt,bh,bs⟩:=RawCompare.compare_run a b
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config RawCompare.machine (pads C) _ _ base hb
  have rt:r.final.tapes=output C a b:=by
    rw [rf];change (fun i=>ZeroPadding.pad (pads C i) (base.final.tapes i))=_
    rw [bt];rfl
  refine ⟨⟨r,hr,rt,?_,rs ▸ bs⟩,rfl,?_,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · exact ZeroPadding.pad_zero _
  · change readTapeBit (ZeroPadding.pad C [decide (a≤b)]) 0=true ↔ a≤b
    rw [ZeroPadding.read_pad]
    simp only [readTapeBit,List.getD_cons_zero,decide_eq_true_eq]
  · intro i hi
    have small:(r.final.tapes i).length ≤ C:=by
      apply CloseoutRowsProjectionReset.scratch_support RawCompare.machine _ C _ r hr i rfl
      · change (input C a b i).length ≤ C
        simp only [input,pads,if_neg hi,ZeroPadding.pad_length]
        refine max_le le_rfl ?_
        fin_cases i <;> first | (exact False.elim (hi rfl)) | (simp [RawCompare.input] <;> omega)
      · rw [rs];have htime:=budget_bound a b;omega
    rw [rt] at small
    exact small

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCapCompare
