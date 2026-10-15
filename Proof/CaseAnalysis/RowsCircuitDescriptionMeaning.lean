import Proof.CaseAnalysis.RowsCircuitSymmetricDescription
import Proof.CaseAnalysis.RowsCircuitThresholdDescription

/-! The paid arithmetic outputs are the original public circuit
 descriptions. Their workspace depends only on actual measured counters. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitDescriptionMeaning
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsCircuitBottom CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem symmetric_exact {core : ℕ} (c : NormalizedSymmetricThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    (descriptions core words 0 c.bottomCount+c.bottomCount+2)/2=c.descriptionBits:=by
  rw [symmetric_description c words hd]
  omega

theorem threshold_exact {core : ℕ} (c : NormalizedThresholdThresholdCircuit core)
    (words : List (List Bool))
    (hd : ∀ i,decodeSupportedNormalizedGate core (value (words.getD i.val []))=some (c.bottom i)) :
    c.bottomCount+1 ≤ descriptions core words (descriptionBytes c.top) c.bottomCount ∧
      (descriptions core words (descriptionBytes c.top) c.bottomCount-(c.bottomCount+1))/2=c.descriptionBits:=by
  have typed:=threshold_description c words hd
  have changed:descriptions core words (descriptionBytes c.top) c.bottomCount=
      descriptions core words 0 c.bottomCount+descriptionBytes c.top:=by
    simp only [descriptions,total,Nat.zero_add,Nat.add_comm]
  rw [changed]
  omega

theorem symmetric_budget (D n : ℕ) :
    CloseoutRowsCircuitSymmetricDescription.budget D n=12*(D+n)+58:=by
  unfold CloseoutRowsCircuitSymmetricDescription.budget CloseoutRowsCircuitHalf.budget
  omega

theorem threshold_budget (D n : ℕ) :
    CloseoutRowsCircuitThresholdDescription.budget D n ≤ 16*D+2*n+57:=by
  unfold CloseoutRowsCircuitThresholdDescription.budget CloseoutRowsCircuitHalf.budget
  omega

theorem symmetric_padded (C D n : ℕ)
    (hi : D ≤ C ∧ n ≤ C) (hc : 12*(D+n)+59 ≤ C) : ∃ bank,
    ClockJoin.ReadyRun CloseoutRowsCircuitSymmetricDescription.machine
        (CloseoutRowsCircuitSymmetricDescription.budget D n)
        (fun i=>ZeroPadding.pad C (CloseoutRowsCircuitSymmetricDescription.input D n i)) bank ∧
      bank 0=ZeroPadding.pad C (List.replicate D true) ∧
      bank 1=ZeroPadding.pad C (List.replicate n true) ∧
      bank 10=ZeroPadding.pad C (List.replicate ((D+n+2)/2) true) ∧
      (∀ i,(bank i).length ≤ C):=by
  obtain ⟨out,⟨base,hb,bt,bh,bs⟩,o0,o1,o10⟩:=CloseoutRowsCircuitSymmetricDescription.description_run D n
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CloseoutRowsCircuitSymmetricDescription.machine
    (fun _=>C) _ _ base hb
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rs ▸ bs⟩,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 0)=_;rw [bt,o0]
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 1)=_;rw [bt,o1]
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 10)=_;rw [bt,o10]
  · intro i
    apply CloseoutRowsProjectionReset.scratch_support CloseoutRowsCircuitSymmetricDescription.machine
      _ C _ r hr i rfl
    · change (ZeroPadding.pad C (CloseoutRowsCircuitSymmetricDescription.input D n i)).length ≤ C
      rw [ZeroPadding.pad_length]
      refine max_le le_rfl ?_
      simp only [CloseoutRowsCircuitSymmetricDescription.input]
      split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega
    · rw [rs];have htime:=symmetric_budget D n;omega

theorem threshold_padded (C D n : ℕ) (hn : n+1 ≤ D)
    (hi : D ≤ C ∧ n ≤ C) (hc : 16*D+2*n+58 ≤ C) : ∃ bank,
    ClockJoin.ReadyRun CloseoutRowsCircuitThresholdDescription.machine
        (CloseoutRowsCircuitThresholdDescription.budget D n)
        (fun i=>ZeroPadding.pad C (CloseoutRowsCircuitThresholdDescription.input D n i)) bank ∧
      bank 0=ZeroPadding.pad C (List.replicate D true) ∧
      bank 1=ZeroPadding.pad C (List.replicate n true) ∧
      bank 14=ZeroPadding.pad C (List.replicate ((D-(n+1))/2) true) ∧
      (∀ i,(bank i).length ≤ C):=by
  obtain ⟨out,⟨base,hb,bt,bh,bs⟩,o0,o1,o14⟩:=CloseoutRowsCircuitThresholdDescription.description_run D n hn
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CloseoutRowsCircuitThresholdDescription.machine
    (fun _=>C) _ _ base hb
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rs ▸ bs⟩,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 0)=_;rw [bt,o0]
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 1)=_;rw [bt,o1]
  · rw [rf];change ZeroPadding.pad C (base.final.tapes 14)=_;rw [bt,o14]
  · intro i
    apply CloseoutRowsProjectionReset.scratch_support CloseoutRowsCircuitThresholdDescription.machine
      _ C _ r hr i rfl
    · change (ZeroPadding.pad C (CloseoutRowsCircuitThresholdDescription.input D n i)).length ≤ C
      rw [ZeroPadding.pad_length]
      refine max_le le_rfl ?_
      simp only [CloseoutRowsCircuitThresholdDescription.input]
      split_ifs <;> simp only [List.length_replicate,List.length_nil] <;> omega
    · rw [rs];have htime:=threshold_budget D n;omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitDescriptionMeaning
