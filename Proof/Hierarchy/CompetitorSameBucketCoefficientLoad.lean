import Proof.Hierarchy.CompetitorSameBucketGateBounds

/-! Copy exactly one existing framed signed coefficient from its streaming
bank. Only the bounded local coefficient target is returned; the global
coefficient cursor advances to the next gate. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCoefficientLoad
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=1)
def machine := MaskedReset.machine MatrixScoreBankField.machine selected
def input (bits pre suffix : List Bool) := Rewind.recording
  (MatrixScoreBankField.cfg 0 (pre++frame bits++suffix) pre.length []) 0
def budget (bits : List Bool) := 4*bits.length+4

theorem load_run (bits pre suffix : List Bool) :
    ∃ actual,runFrom machine (budget bits) (input bits pre suffix)=some actual ∧
      actual.final.heads=![pre.length+(frame bits).length,0,0] ∧
      actual.final.tapes=![pre++frame bits++suffix,frame bits,List.replicate (2*bits.length+1) false] ∧
      actual.steps=budget bits := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixScoreBankField.field_run bits pre suffix []
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=1 := by simpa [selected] using hi
    subst i
    rw [bf,bs]
    simp [MatrixScoreBankField.cfg]
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run MatrixScoreBankField.machine selected _ _ base hb hh
  rw [bs] at ha hs
  have he : 2*(2*bits.length+1)+2=budget bits := by unfold budget; omega
  rw [he] at ha hs
  refine ⟨actual,ha,?_,?_,hs⟩
  · rw [hf,bf]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,MatrixScoreBankField.cfg,selected,Fin.addCases]
  · rw [hf,bf,bs]
    funext i
    fin_cases i <;> rfl

def paddedInput (cap : ℕ) (bits pre suffix : List Bool) := ZeroPadding.config (![0,cap,cap] : Fin 3 → ℕ) (input bits pre suffix)
theorem padded_heads (cap : ℕ) (bits pre suffix : List Bool) : (paddedInput cap bits pre suffix).heads=![pre.length,0,0] := by
  funext i; fin_cases i <;> rfl
theorem padded_tapes (cap : ℕ) (bits pre suffix : List Bool) :
    (paddedInput cap bits pre suffix).tapes=![pre++frame bits++suffix,List.replicate cap false,List.replicate cap false] := by
  funext i
  fin_cases i <;> simp [paddedInput,ZeroPadding.config,input,Rewind.recording,Rewind.config,MatrixScoreBankField.cfg,ZeroPadding.pad,Fin.addCases]

theorem padded_run (cap : ℕ) (bits pre suffix : List Bool) (hc : 2*bits.length+1≤cap) :
    ∃ actual,runFrom machine (budget bits) (paddedInput cap bits pre suffix)=some actual ∧
      actual.final.heads=![pre.length+(frame bits).length,0,0] ∧
      actual.final.tapes=![pre++frame bits++suffix,ZeroPadding.pad cap (frame bits),List.replicate cap false] ∧
      actual.steps=budget bits := by
  obtain ⟨base,hb,bh,bt,bs⟩ := load_run bits pre suffix
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (![0,cap,cap] : Fin 3 → ℕ) _ _ base hb
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    exact bh
  · rw [hf]
    simp only [ZeroPadding.config,bt]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · simp [Rewind.Workspace.pad_zeros,max_eq_left hc]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCoefficientLoad
