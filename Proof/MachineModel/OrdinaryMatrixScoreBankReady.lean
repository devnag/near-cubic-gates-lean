import Proof.MachineModel.OrdinaryMatrixScoreBankCut

/-! Paid local bank rewind after copying the complete cut. The decoded
source cursor stays past the cut and the width sentinel stays at head1. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBankReady
open LocalBitMultitape SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 3) : Bool := decide (i=1)
noncomputable def machine := MaskedReset.machine MatrixScoreBankCut.machine selected
def budget (d p : ℕ) := 2*MatrixScoreBankCut.budget d p+2

theorem bank_run (r : Request) (gate : Fin r.Gates) (pre suffix : List Bool) :
    ∃ cap : ℕ,cap≤MatrixScoreBankCut.budget r.width r.p ∧
      ∃ actual,runFrom machine (budget r.width r.p)
        (RecoveryCalls.restarted machine ![pre.length,0,1,0]
          ![pre++cutWord r.p (r.cuts.get gate)++suffix,[],UnaryTemplate.tape r.width,[]])=some actual ∧
        actual.final.heads=![pre.length+(cutWord r.p (r.cuts.get gate)).length,0,1,0] ∧
        actual.final.tapes=![pre++cutWord r.p (r.cuts.get gate)++suffix,cutWord r.p (r.cuts.get gate),
          UnaryTemplate.tape r.width,List.replicate cap false] ∧ actual.steps≤budget r.width r.p := by
  obtain ⟨body,hb,bh,bt,bs⟩ := MatrixScoreBankCut.bank_run r gate pre suffix []
  simp only [List.length_nil,List.nil_append] at hb bh bt
  let input := RecoveryCalls.restarted MatrixScoreBankCut.machine ![pre.length,0,1]
    ![pre++cutWord r.p (r.cuts.get gate)++suffix,[],UnaryTemplate.tape r.width]
  have hhead (i : Fin 3) (hi : selected i=true) : body.final.heads i≤body.steps := by
    have h := SelectiveReset.prefix_head (prefix_of_run MatrixScoreBankCut.machine _ input body hb).1 i
    have he : i=1 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    simpa only [input,RecoveryCalls.restarted,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.zero_add] using h
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run MatrixScoreBankCut.machine selected _ input body hb hhead
  have hi : Rewind.recording input 0=RecoveryCalls.restarted machine ![pre.length,0,1,0]
      ![pre++cutWord r.p (r.cuts.get gate)++suffix,[],UnaryTemplate.tape r.width,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at ha
  have htime : 2*body.steps+2≤budget r.width r.p := by unfold budget; omega
  have he := runFrom_moreFuel machine (2*body.steps+2) (budget r.width r.p-(2*body.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le htime] at he
  refine ⟨body.steps,bs,actual,he,?_,?_,?_⟩
  · rw [hf,bh]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,selected,Fin.addCases]
  · rw [hf,bt]
    funext i
    fin_cases i <;> rfl
  · rw [hs]
    exact htime

end NearCubicWires.RepairOrdinary.MatrixScoreBankReady
