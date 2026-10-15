import Proof.Hierarchy.CompetitorSameBucketRankFields

/-! Literal reusable scalar backing for the same-bucket pair classifier.
Only the copied present record and actual M-bit template are live on entry;
all other fields are erased bounded scratch. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRankFields
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedInput (cap s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 13 → List Bool := fun i =>
  if i=0 then ZeroPadding.pad cap (source s k score id rank)
  else if i=7 then ZeroPadding.pad cap (frame (binary k 0)) else List.replicate cap false

def paddedOutput (cap s k : ℕ) (score : ℤ) (id rank : ℕ) : Fin 13 → List Bool := fun i =>
  if i=0 ∨ i=1 then ZeroPadding.pad cap (source s k score id rank)
  else if i=4 then ZeroPadding.pad cap (frame (binary (k+s+1) rank))
  else if i=7 then ZeroPadding.pad cap (frame (binary k 0))
  else if i=10 then ZeroPadding.pad cap (frame (binary k id)) else List.replicate cap false

theorem input_padding (cap s k : ℕ) (score : ℤ) (id rank : ℕ) (hc : 30*(k+s+2)≤cap) :
    (fun i => ZeroPadding.pad cap (input s k score id rank i))=paddedInput cap s k score id rank := by
  funext i
  fin_cases i
  all_goals simp [input,paddedInput,source,RecordExtractReset.input,RecordExtract.input,
    RecordClone.input,RecordClone.raw,KeyLoop.word_length,Fin.addCases,ZeroPadding.pad]
  all_goals first | omega | (rw [←List.replicate_succ]; congr 1; omega)

theorem output_padding (cap s k : ℕ) (score : ℤ) (id rank : ℕ) (hc : 30*(k+s+2)≤cap) :
    (fun i => ZeroPadding.pad cap (output s k score id rank i))=paddedOutput cap s k score id rank := by
  funext i
  fin_cases i
  all_goals simp [output,paddedOutput,ZeroPadding.pad]
  all_goals first | omega | (rw [←List.replicate_succ]; congr 1; omega)

theorem padded_ready (cap s k : ℕ) (score : ℤ) (id rank : ℕ) (hc : 30*(k+s+2)≤cap) :
    ClockJoin.ReadyRun machine (budget s k) (paddedInput cap s k score id rank)
      (paddedOutput cap s k score id rank) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := fields_ready s k score id rank
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config machine (fun _ => cap) _ _ base hb
  have hi : ZeroPadding.config (fun _ => cap) (initialConfiguration machine (input s k score id rank))=
      initialConfiguration machine (paddedInput cap s k score id rank) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact input_padding cap s k score id rank hc
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,hs.trans_le bs⟩
  · rw [hf]
    change (fun i => ZeroPadding.pad cap (base.final.tapes i))=_
    rw [bt]
    exact output_padding cap s k score id rank hc
  · intro i
    rw [hf]
    exact bh i

theorem padded_support (cap s k : ℕ) (score : ℤ) (id rank : ℕ) (hc : 30*(k+s+2)≤cap) (i : Fin 13) :
    (paddedOutput cap s k score id rank i).length≤cap := by
  have hsource : (source s k score id rank).length=4*(k+s+1)+1 := by
    simp [source,KeyLoop.word_length]
    omega
  fin_cases i <;> simp [paddedOutput,ZeroPadding.pad_length,hsource] <;> omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRankFields
