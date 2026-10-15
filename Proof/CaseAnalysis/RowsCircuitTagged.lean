import Proof.CaseAnalysis.RowsCircuitHeaderRetained

/-! All-raw tagged-four circuit framing. Five existing literal classifiers
consume the retained tag markers and terminal zero; the four actual circuit
fields remain unchanged for their existing canonical component decoders. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTagged
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorRationalProducts
open CloseoutRowsCircuitHeader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 242) : Fin 268 := i.castAdd 26
def source (j : Fin 5) : Fin 268 := old (tagPort j)
def slots (j : Fin 5) (i : Fin 6) : Fin 268 :=
  if i.val=0 then source j else ⟨241+5*j.val+i.val,by omega⟩
theorem source_lt (j : Fin 5) : (source j).val<242 := by fin_cases j <;> decide
theorem source_injective : Function.Injective source := by decide
theorem slots_injective (j : Fin 5) : Function.Injective (slots j) := by
  intro i k h
  have hv := congrArg Fin.val h
  have hs := source_lt j
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega
theorem slots_disjoint (j k : Fin 5) (hjk : j≠k) (i z : Fin 6) : slots j i≠slots k z := by
  intro h
  have hv := congrArg Fin.val h
  have hj := source_lt j
  have hk := source_lt k
  simp only [slots] at hv
  split_ifs at hv with hi hz hz
  · exact hjk (source_injective (Fin.ext hv))
  · change (source j).val=241+5*k.val+z.val at hv;omega
  · change 241+5*j.val+i.val=(source k).val at hv;omega
  · change 241+5*j.val+i.val=241+5*k.val+z.val at hv
    exact hjk (Fin.ext (by omega))

def input (bits : List Bool) : Fin 268→List Bool :=
  Fin.addCases (m:=242) (n:=26) (motive:=fun _=>List Bool) (CloseoutRowsCircuitHeader.input bits) (fun _=>[])
noncomputable def start (bits : List Bool) : Fin 268→List Bool :=
  Fin.addCases (m:=242) (n:=26) (motive:=fun _=>List Bool) (CloseoutRowsCircuitHeader.output bits) (fun _=>[])
noncomputable def result (bits : List Bool) (j : Fin 5) := CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (tagWord bits j)) (CompetitorWitnessKind.flags (tagWord bits j)) (2*(tagWord bits j).length+1)
noncomputable def before (bits : List Bool) : ℕ→Fin 268→List Bool
  | 0=>start bits
  | k+1=>if hk:k<5 then install (slots ⟨k,hk⟩) (before bits k) (result bits ⟨k,hk⟩) else before bits k
noncomputable def program (j : Fin 5) := RecoveryFocus.machine (slots j) CompetitorWitnessKind.machine
noncomputable def header := TapeEmbedding.machine 26 CloseoutRowsCircuitHeader.machine
noncomputable def two := Composition.machine (program 0) (program 1)
noncomputable def three := Composition.machine two (program 2)
noncomputable def four := Composition.machine three (program 3)
noncomputable def classify := Composition.machine four (program 4)

theorem start_input (bits : List Bool) (j : Fin 5) (i : Fin 6) :
    start bits (slots j i)=CompetitorWitnessKind.input (tagWord bits j) i := by
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi;subst i
    simp only [slots,Fin.val_zero,ite_true,source,old,start,Fin.addCases_left,
      CompetitorWitnessKind.input]
    exact output_tags bits j
  · let k : Fin 26 := ⟨5*j.val+i.val-1,by omega⟩
    have he:slots j i=k.natAdd 242:=by apply Fin.ext;simp [slots,hi,k];omega
    rw [he,start,Fin.addCases_right,CompetitorWitnessKind.input,if_neg hi]

theorem before_unused (bits : List Bool) (k : ℕ) (j : Fin 5) (hk:k≤j.val) (i : Fin 6) :
    before bits k (slots j i)=start bits (slots j i) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before,dif_pos (show k<5 by omega),install_other]
    · exact ih (by omega)
    · intro z
      exact slots_disjoint ⟨k,by omega⟩ j (by intro he;have hv:=congrArg Fin.val he;change k=j.val at hv;omega) z i

theorem tag_length (bits : List Bool) (j : Fin 5) : (tagWord bits j).length=bits.length := by
  fin_cases j <;> simp [tagWord,RecoveryFixedUnpair.word_lengths,CompetitorWitnessTriple.word_length]

theorem step_ready (bits : List Bool) (j : Fin 5) :
    ClockJoin.ReadyRun (program j) (16*bits.length+27) (before bits j.val) (before bits (j.val+1)) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := CompetitorWitnessKind.kind_ready (tagWord bits j)
  have h := (show ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*(tagWord bits j).length+27)
      (CompetitorWitnessKind.input (tagWord bits j)) (result bits j) from ⟨r,hr,rt,rh,rs.le⟩).focus
    (slots j) (slots_injective j) (before bits j.val)
    (by intro i;rw [before_unused bits j.val j (by rfl),start_input])
  simpa only [before,dif_pos j.isLt,program,tag_length] using h

theorem classify_ready (bits : List Bool) :
    ClockJoin.ReadyRun classify (80*bits.length+139) (start bits) (before bits 5) := by
  have h1:=ClockJoin.join _ _ _ _ _ _ _ (step_ready bits 0) (step_ready bits 1)
  have h2:=ClockJoin.join _ _ _ _ _ _ _ h1 (step_ready bits 2)
  have h3:=ClockJoin.join _ _ _ _ _ _ _ h2 (step_ready bits 3)
  have h4:=ClockJoin.join _ _ _ _ _ _ _ h3 (step_ready bits 4)
  have ht : (((16*bits.length+27+1+(16*bits.length+27))+1+(16*bits.length+27))+1+
      (16*bits.length+27))+1+(16*bits.length+27)=80*bits.length+139 := by omega
  rw [ht] at h4
  exact h4

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTagged
