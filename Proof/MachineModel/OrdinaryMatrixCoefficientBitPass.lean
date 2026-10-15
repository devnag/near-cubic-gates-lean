import Proof.MachineModel.OrdinaryMatrixSignedUEntry

/-! Whole coefficient-bit extraction with one paid bank/output return.
The canonical bank is reusable at the next sign/bit plane, and the actual
byte-offset and Gates sentinels remain positioned for their loops. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitPass
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 5) := decide (i=0 ∨ i=3)
noncomputable def machine (negative : Bool) := MaskedReset.machine (MatrixCoefficientBitLoop.machine negative) selected
def budget (r : Request) := 2*MatrixCoefficientBitNative.budget r+2
noncomputable def input (r : Request) (negative flag : Bool) (t : ℕ) :=
  Rewind.recording (MatrixCoefficientBitNative.cfg r negative flag t 0 0 []) 0

theorem pass_run (r : Request) (negative flag : Bool) (t : ℕ) (ht : t<r.p) : ∃ actual,
    runFrom (machine negative) (budget r) (input r negative flag t)=some actual ∧
    (∀ i : Fin 5,actual.final.tapes (i.castAdd 1)=
      (![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape (2*t),
        [MatrixCoefficientBitLoop.finalFlag negative flag (MatrixCoefficientBitNative.coefficients r)],
        MatrixCoefficientBitNative.output r negative t,UnaryTemplate.tape r.Gates] : Fin 5 → List Bool) i) ∧
    (∀ i : Fin 5,actual.final.heads (i.castAdd 1)=(![0,1,0,0,1] : Fin 5 → ℕ) i) ∧
    actual.final.heads 5=0 ∧
    (∃ n,actual.final.tapes 5=List.replicate n false ∧ n≤MatrixCoefficientBitNative.budget r) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixCoefficientBitNative.all_run r negative flag t ht []
  simp only [List.nil_append] at bf
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have hi03 : i=0 ∨ i=3 := by simpa only [selected,decide_eq_true_eq] using hi
    obtain ⟨hp,_⟩ := prefix_of_run (MatrixCoefficientBitLoop.machine negative) (MatrixCoefficientBitNative.budget r)
      (MatrixCoefficientBitNative.cfg r negative flag t 0 0 []) base hb
    have h := SelectiveReset.prefix_head hp i
    rcases hi03 with rfl | rfl
    all_goals simpa [MatrixCoefficientBitNative.cfg_heads] using h
  obtain ⟨actual,ha,af,as,_⟩ := MaskedReset.reset_run (MatrixCoefficientBitLoop.machine negative) selected _ _ base hb hh
  have hs : 2*base.steps+2≤budget r := by unfold budget; omega
  have he := runFrom_moreFuel (machine negative) _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hs] at he
  refine ⟨actual,he,?_,?_,?_,?_,as.trans_le hs⟩
  · intro i
    rw [af,bf]
    simp [SelectiveReset.finished,Rewind.config,Fin.addCases_left,MatrixCoefficientBitNative.cfg_tapes]
  · intro i
    rw [af,bf]
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,Fin.addCases,MatrixCoefficientBitNative.cfg_heads,selected]
  · rw [af]
    rfl
  · exact ⟨base.steps,by rw [af]; rfl,bs⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitPass
