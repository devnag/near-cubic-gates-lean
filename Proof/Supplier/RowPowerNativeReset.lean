import Proof.Supplier.RowPowerNativeBlock
import Proof.PCP.PCPSerializerTapeSupport

/-! Actual local head restoration for the native-field block appender.
Cache/output cursors are excluded. Reused scratch padding is transported
through the same trace and its allocated lengths remain bounded. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReset
open LocalBitMultitape RecoveryExecution Streaming RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 12) := decide (1 ≤ i.val ∧ i.val < 10)
noncomputable def machine := MaskedReset.machine RowPowerNative.machine selected
def rawTime (z : ℤ) (w : ℕ) := 6*natBitLength z.natAbs+2*w+11
def caps (C : ℕ) (positive negative : List Bool) (i : Fin 13) : ℕ :=
  if 1 ≤ i.val ∧ i.val < 9 ∨ i.val=12 then C
  else if i.val=10 then positive.length+1 else if i.val=11 then negative.length+1 else 0
def entry (source : List Bool) (pos w C : ℕ) (positive negative : List Bool) : Configuration 13 16 :=
  ZeroPadding.config (caps C positive negative)
    (Rewind.recording (RowPowerNative.entry source pos w positive negative) 0)
noncomputable def output (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) : Configuration 13 16 :=
  let out := RowPowerNative.output source pos w
    (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative
  ZeroPadding.config (caps C positive negative)
    (SelectiveReset.finished (s := 14) (fun i => if selected i then 0 else out.heads i)
      out.tapes (rawTime z w))

theorem head_bound (source : List Bool) (pos w : ℕ) (z : ℤ) (positive negative : List Bool)
    (i : Fin 12) (hi : selected i=true) :
    (RowPowerNative.output source pos w (binary (natBitLength z.natAbs) z.natAbs)
      (decide (z<0)) positive negative).heads i ≤ rawTime z w := by
  rw [RowPowerNative.output_heads]
  have hm : min w (binary (natBitLength z.natAbs) z.natAbs).length ≤ w := Nat.min_le_left _ _
  fin_cases i <;> simp [selected] at hi ⊢ <;> simp only [rawTime] <;> omega

theorem initial_work {source : List Bool} {pos w : ℕ} {positive negative : List Bool}
    (i : Fin 12) (hi : 1 ≤ i.val ∧ i.val < 9) :
    (RowPowerNative.entry source pos w positive negative).heads i=0 ∧
      (RowPowerNative.entry source pos w positive negative).tapes i=[] := by
  fin_cases i <;> simp at hi <;> exact ⟨rfl,rfl⟩

theorem field_run (pre suffix positive negative : List Bool) (z : ℤ) (w C : ℕ)
    (hC : rawTime z w+1 ≤ C) :
    ∃ r,runFrom machine (2*rawTime z w+2)
      (entry (pre++intWord z++suffix) pre.length w C positive negative)=some r ∧
      r.final=output (pre++intWord z++suffix) (pre.length+(intWord z).length) w C z positive negative ∧
      r.steps=2*rawTime z w+2 ∧
      (∀ i : Fin 13,(1 ≤ i.val ∧ i.val < 9) ∨ i.val=12 → (r.final.tapes i).length ≤ C) := by
  obtain ⟨raw,hr,rf,rs⟩ := RowPowerNative.field_run pre suffix positive negative z w
  have hh : ∀ i,selected i=true → raw.final.heads i ≤ raw.steps := by
    intro i hi
    rw [rf,rs]
    exact head_bound _ _ _ _ _ _ i hi
  have hl (i : Fin 12) (hi : 1 ≤ i.val ∧ i.val < 9) :
      (raw.final.tapes i).length ≤ C := by
    have hc := initial_work (source := pre++intWord z++suffix) (pos := pre.length)
      (w := w) (positive := positive) (negative := negative) i hi
    have ht := PCPSerializerReuse.tape_support RowPowerNative.machine _ _ raw hr i 0 0
      (by rw [hc.1]) (by rw [hc.2]; simp)
    simp only [Nat.zero_add,max_eq_right (Nat.zero_le _),rs] at ht
    exact ht.trans hC
  obtain ⟨reset,hreset,resetFinal,resetSteps,_⟩ :=
    MaskedReset.reset_run RowPowerNative.machine selected _ _ raw hr hh
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine
    (caps C positive negative) _ _ reset hreset
  have timeEq : 2*raw.steps+2=2*rawTime z w+2 := by rw [rs]; rfl
  rw [timeEq] at hresult
  refine ⟨result,hresult,?_,resultSteps.trans (resetSteps.trans timeEq),?_⟩
  · rw [resultFinal,resetFinal,rf,rs]
    rfl
  · intro i hi
    rw [resultFinal,resetFinal]
    rcases hi with hi | hi
    · have hil : i.val < 12 := by omega
      let j : Fin 12 := ⟨i.val,hil⟩
      have hij : i=j.castAdd 1 := Fin.ext rfl
      rw [hij]
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
      change (ZeroPadding.pad (caps C positive negative (j.castAdd 1)) (raw.final.tapes j)).length ≤ C
      have hj : 1 ≤ j.val ∧ j.val < 9 := hi
      have hcap : caps C positive negative (j.castAdd 1)=C := by simp [caps,j,hi]
      rw [hcap,ZeroPadding.pad_length]
      exact max_le le_rfl (hl j hj)
    · have he : i=(0 : Fin 1).natAdd 12 := Fin.ext hi
      rw [he]
      change (ZeroPadding.pad C (List.replicate raw.steps false)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      rw [rs]
      exact max_le le_rfl (by unfold rawTime at hC; omega)

theorem output_heads (source : List Bool) (pos w C : ℕ) (z : ℤ) (positive negative : List Bool) :
    (output source pos w C z positive negative).heads=
      ![pos,0,0,0,0,0,0,0,0,0,positive.length+2*w,negative.length+2*w,0] := by
  funext i
  refine Fin.addCases (m := 12) (n := 1) (motive := fun j =>
    (output source pos w C z positive negative).heads j=
      (![pos,0,0,0,0,0,0,0,0,0,positive.length+2*w,negative.length+2*w,0] : Fin 13 → ℕ) j) ?_ ?_ i
  · intro j
    simp only [output,ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
    rw [RowPowerNative.output_heads]
    fin_cases j <;> rfl
  · intro j
    fin_cases j
    rfl

end NearCubicWires.RepairOrdinary.RowPowerNativeReset
