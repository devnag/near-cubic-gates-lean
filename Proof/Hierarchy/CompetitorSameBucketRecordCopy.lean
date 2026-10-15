import Proof.Hierarchy.CompetitorSameBucket

/-! Fixed-width raw record/block loading with a physical unary driver.
The input may contain an absent padded record: no delimiter is guessed.
Only the local target is reset, while the source cursor remains streaming.
The padded version is reusable after the caller's bounded local erase. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRecordCopy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 3) : Bool := decide (i=2)
def machine := MaskedReset.machine (MatrixRawBlock.machine true) selected
def budget (length : ℕ) := 4*length+10
def input (pre bits suffix : List Bool) :=
  Rewind.recording (MatrixRawBlock.config (MatrixRawBlock.machine true).start
    (UnaryTemplate.tape bits.length) 1 (pre++bits++suffix) pre.length []) 0

theorem copy_run (pre bits suffix : List Bool) :
    ∃ actual,runFrom machine (budget bits.length) (input pre bits suffix)=some actual ∧
      actual.final.heads=![1,pre.length+bits.length,0,0] ∧
      actual.final.tapes=![UnaryTemplate.tape bits.length,pre++bits++suffix,bits,
        List.replicate (2*bits.length+4) false] ∧ actual.steps=budget bits.length := by
  obtain ⟨base,hb,bf,bs,_⟩ := MatrixRawBlock.block_run true pre bits suffix []
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=2 := by simpa [selected] using hi
    subst i
    rw [bf,bs]
    change bits.length≤2*bits.length+4
    omega
  obtain ⟨actual,ha,hf,hs,_⟩ := MaskedReset.reset_run (MatrixRawBlock.machine true) selected _ _ base hb hh
  rw [bs] at ha hs
  have ht : 2*(2*bits.length+4)+2=budget bits.length := by unfold budget; omega
  rw [ht] at ha hs
  refine ⟨actual,ha,?_,?_,hs⟩
  · rw [hf,bf]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,MatrixRawBlock.config,
      MatrixRawBlock.selected,selected,Fin.addCases]
  · rw [hf,bf,bs]
    funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,MatrixRawBlock.config,
      MatrixRawBlock.selected,Fin.addCases]

def paddedInput (cap : ℕ) (pre bits suffix : List Bool) :=
  ZeroPadding.config (![0,0,cap,cap] : Fin 4 → ℕ) (input pre bits suffix)

theorem padded_heads (cap : ℕ) (pre bits suffix : List Bool) :
    (paddedInput cap pre bits suffix).heads=![1,pre.length,0,0] := by
  funext i
  fin_cases i <;> rfl

theorem padded_tapes (cap : ℕ) (pre bits suffix : List Bool) :
    (paddedInput cap pre bits suffix).tapes=
      ![UnaryTemplate.tape bits.length,pre++bits++suffix,List.replicate cap false,List.replicate cap false] := by
  funext i
  fin_cases i <;> simp [paddedInput,ZeroPadding.config,ZeroPadding.pad,input,Rewind.recording,
    Rewind.config,MatrixRawBlock.config,Fin.addCases]

theorem padded_run (cap : ℕ) (pre bits suffix : List Bool) (hc : 2*bits.length+4≤cap) :
    ∃ actual,runFrom machine (budget bits.length) (paddedInput cap pre bits suffix)=some actual ∧
      actual.final.heads=![1,pre.length+bits.length,0,0] ∧
      actual.final.tapes=![UnaryTemplate.tape bits.length,pre++bits++suffix,
        ZeroPadding.pad cap bits,List.replicate cap false] ∧ actual.steps=budget bits.length := by
  obtain ⟨base,hb,bh,bt,bs⟩ := copy_run pre bits suffix
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (![0,0,cap,cap] : Fin 4 → ℕ) _ _ base hb
  refine ⟨actual,ha,?_,?_,hs.trans bs⟩
  · rw [hf]
    exact bh
  · rw [hf]
    simp only [ZeroPadding.config,bt]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad cap (List.replicate (2*bits.length+4) false)=List.replicate cap false
      simp [ZeroPadding.pad,Nat.add_sub_of_le hc]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRecordCopy
