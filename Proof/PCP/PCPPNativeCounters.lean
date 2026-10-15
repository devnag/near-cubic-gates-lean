import Proof.PCP.PCPPNativeMetadataMass

/-! The measured original metadata supplies separate physical arity copies
for the node emitter and the descriptor header. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeColdCounters
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 75 := ![36,71,72,73]
def ports : Fin 9 → Fin 75 := ![0,32,71,45,48,52,53,57,58]
noncomputable def first := TapeEmbedding.machine 4 PCPPNativeMetadataMass.machine
noncomputable def second := RecoveryFocus.machine slots MatrixDimensionHeader.machine
noncomputable def machine := Composition.machine first second
def input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) : Fin 75 → List Bool :=
  Fin.addCases (m:=71) (n:=4) (motive:=fun _=>List Bool) (PCPPNativeMetadataMass.input oracle p R Q) (fun _=>[])
def heads : Fin 75 → ℕ := Fin.addCases (m:=71) (n:=4) (motive:=fun _=>ℕ) PCPPNativeMetadataMass.heads (fun _=>0)
noncomputable def entry (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) :=
  (⟨machine.start,heads,input oracle p R Q⟩ : Configuration 75 _)
def budget (p : RawProjectionPCP) (R Q s : ℕ) := PCPPNativeMetadataMass.budget p R Q s+1+(2*R+3)

theorem counters_run {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) : ∃ result,
    runFrom machine (budget p R Q oracle.size) (entry (PCPPNative.descriptor oracle) p R Q)=some result ∧
    result.steps≤budget p R Q oracle.size ∧
    (∀ j,result.final.heads (ports j)=0 ∧ result.final.tapes (ports j)=PCPPNativeMetadataMass.values oracle p Q j) ∧
    result.final.heads 72=0 ∧ result.final.tapes 72=List.replicate R true := by
  obtain ⟨a,ha,as,af⟩ := PCPPNativeMetadataMass.metadata_mass_run oracle p Q hR hQ
  let lifted := TapeEmbedding.receipt (fun _ : Fin 4=>0) (fun _=>[]) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeMetadataMass.machine (fun _ : Fin 4=>0) (fun _=>[]) _ _ a ha
  obtain ⟨raw,hr,r1,r2,_,rh,rs⟩ := MatrixRawDimension.raw_run R
  obtain ⟨b,hb,_,bs,bh,bt,baway⟩ := RecoveryFocus.dock slots (by decide) MatrixDimensionHeader.machine _
    lifted.final.heads lifted.final.tapes (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input R))
    (by
      intro i; fin_cases i
      · exact (af 2).1
      all_goals rfl)
    (by
      intro i; fin_cases i
      · exact (af 2).2
      all_goals rfl) raw hr
  have joined := Composition.run_join first second _ _ _ lifted b firstRun hb
  refine ⟨Composition.joinedReceipt lifted b,joined,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget p R Q oracle.size
    rw [bs,rs]
    unfold budget
    omega
  · intro j
    change b.final.heads (ports j)=0 ∧ b.final.tapes (ports j)=PCPPNativeMetadataMass.values oracle p Q j
    fin_cases j
    · exact ⟨(baway 0 (by decide)).1.trans (af 0).1,(baway 0 (by decide)).2.trans (af 0).2⟩
    · exact ⟨(baway 32 (by decide)).1.trans (af 1).1,(baway 32 (by decide)).2.trans (af 1).2⟩
    · exact ⟨(bh 1).trans (by rw [rh]; rfl),(bt 1).trans r1⟩
    · exact ⟨(baway 45 (by decide)).1.trans (af 3).1,(baway 45 (by decide)).2.trans (af 3).2⟩
    · exact ⟨(baway 48 (by decide)).1.trans (af 4).1,(baway 48 (by decide)).2.trans (af 4).2⟩
    · exact ⟨(baway 52 (by decide)).1.trans (af 5).1,(baway 52 (by decide)).2.trans (af 5).2⟩
    · exact ⟨(baway 53 (by decide)).1.trans (af 6).1,(baway 53 (by decide)).2.trans (af 6).2⟩
    · exact ⟨(baway 57 (by decide)).1.trans (af 7).1,(baway 57 (by decide)).2.trans (af 7).2⟩
    · exact ⟨(baway 58 (by decide)).1.trans (af 8).1,(baway 58 (by decide)).2.trans (af 8).2⟩
  · exact (bh 2).trans (by rw [rh]; rfl)
  · exact (bt 2).trans r2

end NearCubicWires.RepairOrdinary.PCPPNativeColdCounters
