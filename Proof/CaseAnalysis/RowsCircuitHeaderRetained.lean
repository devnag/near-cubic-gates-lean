import Proof.CaseAnalysis.RowsGateMeasuredRun
import Proof.CaseAnalysis.RowsCircuitHeader

/-! The SAME four-field header traversal retains every structural marker
and terminal zero. These exact fields permit the public circuit-code test
without rebuilding and comparing an entire normalized circuit encoding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHeader
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorWitnessTriple CanonicalBinary CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def output (bits : List Bool) :=
  install lastSlots (middle bits) (stage [] (word bits 6) 6)
def tagPort : Fin 5→Fin 242 := ![18,58,98,138,159]
def tagWord (bits : List Bool) (i : Fin 5) :=
  if i.val<4 then RecoveryFixedUnpair.leftWord (word bits (2*i.val)) else word bits 8

theorem node_two (x bits : List Bool) : stage x bits 6 39=frame (word bits 2) := by
  have stable := stage_stable x bits 3 3 39 (by decide)
  rw [stable]
  change stage x bits (2+1) (CompetitorWitnessTriple.slots 2 0)=_
  rw [stage,dif_pos (show 2<6 by omega)]
  exact install_slot (CompetitorWitnessTriple.slots (2 : Fin 6)) (slots_injective 2) _ _ 0

theorem header_ready (bits : List Bool) :
    ClockJoin.ReadyRun machine (budget bits) (input bits) (output bits) := by
  obtain ⟨a,ha,ta,ah,as⟩ := triple_run [] bits
  have hf := bounded_focus firstSlots first_injective _ _ _ ⟨a,ha,ta,ah,as⟩
    (input bits) (by intro i;simp only [input,firstSlots,Fin.addCases_left])
  obtain ⟨b,hb,bt,bh,bs⟩ := triple_run [] (word bits 6)
  have hl := bounded_focus lastSlots last_injective _ _ _ ⟨b,hb,bt,bh,bs⟩ (middle bits) (last_input bits)
  have h := ClockJoin.join first last _ _ _ _ _ hf hl
  have htime : CompetitorWitnessTriple.budget bits+1+CompetitorWitnessTriple.budget (word bits 6) ≤ budget bits := by
    unfold CompetitorWitnessTriple.budget budget
    rw [CompetitorWitnessTriple.word_length]
    have hp : 1 ≤ (bits.length+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega
  exact ClockJoin.enlarge machine _ _ _ _ h htime

theorem output_fields (bits : List Bool) (i : Fin 4) : output bits (port i)=frame (codeWord bits i) := by
  obtain ⟨other,hother,fields⟩ := header_run bits
  obtain ⟨a,ha,aT,_aH,_aS⟩ := header_ready bits
  obtain ⟨b,hb,bT,_bH,_bS⟩ := hother
  have he := CloseoutRowsGateGuard.receipt_unique _ _ _ _ a b ha hb
  subst b
  rw [←aT,bT]
  exact fields i

theorem output_tags (bits : List Bool) (i : Fin 5) : output bits (tagPort i)=frame (tagWord bits i) := by
  have earlier (j : Fin 6) (hj : j=0 ∨ j=2 ∨ j=4) :
      output bits (firstSlots (CompetitorWitnessTriple.slots j 17))=
        frame (RecoveryFixedUnpair.leftWord (word bits j.val)) := by
    rw [output,install_other _ _ _ _ (by rcases hj with rfl|rfl|rfl <;> decide)]
    exact (middle_old bits _).trans (field_output [] bits j)
  fin_cases i
  · exact earlier 0 (Or.inl rfl)
  · exact earlier 2 (Or.inr (Or.inl rfl))
  · exact earlier 4 (Or.inr (Or.inr rfl))
  · change install lastSlots (middle bits) _ (lastSlots 18)=_
    rw [install_slot _ last_injective]
    exact field_output [] (word bits 6) 0
  · change install lastSlots (middle bits) _ (lastSlots 39)=_
    rw [install_slot _ last_injective]
    exact node_two [] (word bits 6)

def structural (bits : List Bool) : Prop :=
  field bits 0=1 ∧ field bits 2=1 ∧ field bits 4=1 ∧ field bits 6=1 ∧ node bits 8=0

theorem structural_iff (bits : List Bool) : structural bits ↔
    value bits=encodeTaggedList [value (codeWord bits 0),value (codeWord bits 1),
      value (codeWord bits 2),value (codeWord bits 3)] := by
  constructor
  · rintro ⟨h0,h2,h4,h6,h8⟩
    change node bits 0=encodeTaggedList [field bits 1,field bits 3,field bits 5,field bits 7]
    rw [←pair_node bits 0,←pair_node bits 1,←pair_node bits 2,←pair_node bits 3,
      ←pair_node bits 4,←pair_node bits 5,←pair_node bits 6,←pair_node bits 7,h0,h2,h4,h6,h8]
    rfl
  · intro h
    simp only [structural,field_eq,node_eq,h,nodeCode,encodeTaggedList,Nat.unpair_pair]
    trivial

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHeader
