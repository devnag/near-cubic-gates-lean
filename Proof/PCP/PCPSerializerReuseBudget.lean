import Proof.PCP.PCPSerializerReuseBody

/-! A single physically supplied global envelope gives the repeated caller
one uniform body clock. The envelope producer remains an executed caller
obligation; these inequalities do not install its tape. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def envelope (B : ℕ) : ℕ := 1000000000001*(B+1)^12
theorem envelope_covers (B b : ℕ) (hb : b ≤ B) : PCPTraversal.budget b+1 ≤ envelope B := by
  have hp : (b+1)^12 ≤ (B+1)^12 := by gcongr
  have hpos : 1 ≤ (B+1)^12 := Nat.one_le_pow 12 _ (by omega)
  unfold PCPTraversal.budget envelope
  omega

theorem framedCode_le_budget (fields : List (List Bool)) :
    2*(PCPTraversal.code fields).bits.length+1 ≤ PCPTraversal.budget (mass fields) := by
  have hb := PCPTraversal.bounded_code fields (mass fields) le_rfl
  have hp : (mass fields+1)^5 ≤ (mass fields+1)^12 := pow_le_pow_right₀ (by omega) (by omega)
  have hpos : 1 ≤ (mass fields+1)^12 := Nat.one_le_pow 12 _ (by omega)
  unfold PCPTraversal.budget
  omega

def Result {s : ℕ} (capacity log pos count : ℕ) (source out : List Bool)
    (final : Configuration 132 s) : Prop :=
  final.heads=bodyHeads pos out.length ∧ final.tapes 0=source ∧
  final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word count ∧
  final.tapes 129=out ∧ final.tapes 130=List.replicate capacity true ∧
  final.tapes 131=List.replicate (max log (capacity+1)) false ∧
  ∀ j,final.tapes (scratchSlots j)=List.replicate capacity false

theorem body_uniform_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool)
    (capacity log : ℕ) (hcap : PCPTraversal.budget (mass fields)+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine (6*capacity+8)
      (bodyEntry capacity log (pre++FieldList.stream fields++suffix) pre.length fields.length out)=some r ∧
      Result capacity log (pre.length+(FieldList.stream fields).length) fields.length
        (pre++FieldList.stream fields++suffix) (out++frame (PCPTraversal.code fields).bits) r.final ∧
      r.steps ≤ 6*capacity+8 := by
  obtain ⟨r,hr,hh,h0,h2,ho,hd,hl,hscratch,hs⟩ := body_run pre fields suffix out capacity log hcap
  have hbits := framedCode_le_budget fields
  have hf : 2*PCPTraversal.budget (mass fields)+4*(PCPTraversal.code fields).bits.length+2*capacity+12 ≤
      6*capacity+8 := by omega
  have hmore := runFrom_moreFuel bodyMachine _
    (6*capacity+8-(2*PCPTraversal.budget (mass fields)+4*(PCPTraversal.code fields).bits.length+2*capacity+12)) _ r hr
  rw [Nat.add_sub_of_le hf] at hmore
  exact ⟨r,hmore,⟨hh,h0,h2,ho,hd,hl,hscratch⟩,hs.trans hf⟩

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
