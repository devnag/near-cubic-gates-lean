import Proof.Circuits.DecompositionStreamReset

/-! Whole signed stream with its actual emitted atom fields rewound for the
shared child serializer. Source, field count and capacity are retained. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomStreamReady
open LocalBitMultitape RecoveryExecution DecompositionAtomReuse
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := SelectiveReset.machine DecompositionAtomCold.machine 176
def budget (C T : ℕ) := 2*DecompositionAtomCold.budget C T+2
noncomputable def entry (C T : ℕ) (source : List Bool) (pos : ℕ) :=
  Rewind.recording (DecompositionAtomCold.entry C T source pos []) 0

theorem cfg_tapes (phase : Fin 5) (C : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :
    (DecompositionAtomLoop.cfg phase C source pos out total driver).tapes=
      Fin.addCases (m:=179) (n:=1) (bodyTapes C source out) (fun _ => CompareMachine.word total) := by
  simp only [DecompositionAtomLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bodyEntry_tapes]

theorem cfg_heads (phase : Fin 5) (C : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (total driver : ℕ) :
    (DecompositionAtomLoop.cfg phase C source pos out total driver).heads=
      Fin.addCases (m:=179) (n:=1) (bodyHeads pos out.length) (fun _ => driver) := by
  simp only [DecompositionAtomLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,bodyEntry_heads]

theorem atom_run (pre : List Bool) (values : List ℤ) (suffix : List Bool) (C : ℕ)
    (hcap : ∀ z∈values,DecompositionAtom.budget z+1 ≤ C) :
    ∃ r,runFrom machine (budget C values.length)
      (entry C values.length (pre++DecompositionAtomLoop.stream values++suffix) pre.length)=some r ∧
      r.final.tapes 0=pre++DecompositionAtomLoop.stream values++suffix ∧
      r.final.heads 0=pre.length+(DecompositionAtomLoop.stream values).length ∧
      r.final.tapes 176=DecompositionAtomLoop.encoded values ∧ r.final.heads 176=0 ∧
      r.final.tapes 177=List.replicate C true ∧ r.final.heads 177=0 ∧
      r.final.tapes 179=CompareMachine.word values.length ∧ r.final.heads 179=1 ∧
      r.steps ≤ budget C values.length := by
  obtain ⟨p,hp,ph,pt,_⟩ := DecompositionAtomCold.cold_run pre values suffix [] C hcap
  obtain ⟨r,hr,rt,rh,rs⟩ := DecompositionStreamReset.reset_output_run
    DecompositionAtomCold.machine 176 _ _ p hp (by rfl)
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,?_,rs⟩
  · exact (rt 0).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 0).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)
  · exact (rt 176).trans (by rw [pt,cfg_tapes]; rfl)
  · exact rh 176
  · exact (rt 177).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 177).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)
  · exact (rt 179).trans (by rw [pt,cfg_tapes]; rfl)
  · exact (rh 179).trans (by rw [if_neg (by decide),ph,cfg_heads]; rfl)

end NearCubicWires.RepairOrdinary.DecompositionAtomStreamReady
