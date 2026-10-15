import Proof.Circuits.DecompositionAtomStreamReady
import Proof.Circuits.DecompositionGroups

/-! The same shared serializer executes every fixed-arity child, then its
whole emitted child stream is physically rewound for the outer list call. -/
namespace NearCubicWires.RepairOrdinary.DecompositionChildStreamReady
open LocalBitMultitape RecoveryExecution PCPSerializerReuse
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := SelectiveReset.machine DecompositionGroupsCold.machine 129
def budget (C M : ℕ) := 2*DecompositionGroupsCold.budget C M+2
noncomputable def entry (C count M : ℕ) (source : List Bool) (pos : ℕ) :=
  Rewind.recording (DecompositionGroupsCold.entry C count M source pos []) 0

theorem cfg_tapes (phase : Fin 5) (count C : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :
    (DecompositionBalancedGroups.cfg phase count C source pos out total driver).tapes=
      Fin.addCases (m:=132) (n:=1) (bodyTapes C (C+1) source count out)
        (fun _ => CompareMachine.word total) := by
  simp only [DecompositionBalancedGroups.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bodyEntry_tapes]

theorem cfg_heads (phase : Fin 5) (count C : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :
    (DecompositionBalancedGroups.cfg phase count C source pos out total driver).heads=
      Fin.addCases (m:=132) (n:=1) (bodyHeads pos out.length) (fun _ => driver) := by
  simp only [DecompositionBalancedGroups.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bodyEntry_heads]

theorem child_run (pre : List Bool) (groups : List (List (List Bool))) (suffix : List Bool)
    (count C : ℕ) (hcount : ∀ fields∈groups,fields.length=count)
    (hcap : ∀ fields∈groups,PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ C) :
    ∃ r,runFrom machine (budget C groups.length)
      (entry C count groups.length (pre++DecompositionBalancedGroups.stream groups++suffix) pre.length)=some r ∧
      r.final.tapes 0=pre++DecompositionBalancedGroups.stream groups++suffix ∧
      r.final.heads 0=pre.length+(DecompositionBalancedGroups.stream groups).length ∧
      r.final.tapes 129=DecompositionBalancedGroups.encoded groups ∧ r.final.heads 129=0 ∧
      r.final.tapes 2=CompareMachine.word count ∧ r.final.heads 2=1 ∧
      r.final.tapes 130=List.replicate C true ∧ r.final.heads 130=0 ∧
      r.final.tapes 132=CompareMachine.word groups.length ∧ r.final.heads 132=1 ∧
      r.steps ≤ budget C groups.length := by
  obtain ⟨p,hp,ph,pt,_⟩ := DecompositionGroupsCold.cold_run pre groups suffix [] count C hcount hcap
  obtain ⟨r,hr,rt,rh,rs⟩ := DecompositionStreamReset.reset_output_run
    DecompositionGroupsCold.machine 129 _ _ p hp (by rfl)
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rs⟩
  · exact (rt 0).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 0).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)
  · exact (rt 129).trans (by rw [pt,cfg_tapes]; rfl)
  · exact rh 129
  · exact (rt 2).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 2).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)
  · exact (rt 130).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 130).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)
  · exact (rt 132).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 132).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)

end NearCubicWires.RepairOrdinary.DecompositionChildStreamReady
