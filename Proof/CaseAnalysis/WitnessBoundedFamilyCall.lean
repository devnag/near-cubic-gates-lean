import Proof.CaseAnalysis.WitnessBoundedFamilyLayout

/-! The actual bounded header supplies the cold family's three inputs.
The focused receipt retains the original local receipt, so its family and
query-cache projections refer to this one executed source call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem header_run (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (x bits : List Bool) :
    ∃ scratch, scratch ≤ 3*x.length+2 ∧ ∃ prior,
      run (first source a k D G E) (CompetitorWitnessBounded.budget x)
        (input source a k D G E x bits)=some prior ∧
      prior.final.tapes=HeaderDock.input (workspace source a k D G E)
        (CompetitorWitnessBounded.output x bits scratch) ∧
      prior.final.heads=(fun _=>0) := by
  obtain ⟨scratch,hs,prior,hp,ht,hh,_⟩:=CompetitorWitnessBounded.bounded_run x bits
  let extra:=workspace source a k D G E+1
  let lifted:=TapeEmbedding.receipt (fun _ : Fin extra=>0) (fun _=>[]) prior
  have hr:=TapeEmbedding.run_embed CompetitorWitnessBounded.machine
    (fun _ : Fin extra=>0) (fun _=>[]) (CompetitorWitnessBounded.budget x) _ prior hp
  rw [StreamPrepare.embed_initial] at hr
  refine ⟨scratch,hs,lifted,hr,?_,?_⟩
  · change Fin.addCases (m:=150) (n:=extra) (motive:=fun _=>List Bool) prior.final.tapes (fun _=>[])=_
    rw [ht]
    rfl
  · change Fin.addCases (m:=150) (n:=extra) (motive:=fun _=>ℕ) prior.final.heads (fun _=>0)=_
    rw [show prior.final.heads=(fun _=>0) from funext hh]
    funext i
    refine Fin.addCases (m:=150) (n:=extra) (motive:=fun i=>
      Fin.addCases (m:=150) (n:=extra) (motive:=fun _=>ℕ) (fun _=>0) (fun _=>0) i=0) ?_ ?_ i
    · intro j;rw [Fin.addCases_left]
    · intro j;rw [Fin.addCases_right]

theorem input_data (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool)
    (x bits : List Bool) (scratch : ℕ)
    (hvalid:readTapeBit (CompetitorWitnessBounded.output x bits scratch 147) 0=true)
    (j : Fin (localTapes source a k D G E sym)) :
    HeaderDock.input (workspace source a k D G E) (CompetitorWitnessBounded.output x bits scratch)
      (slots source a k D G E sym j)=
    ColdFamily.input source a k D G (exponent sym) E x
      (BoundedFields.oracle bits) (BoundedFields.family bits) j := by
  have fields:=BoundedFields.fields x bits scratch hvalid
  rw [ColdInput.family_input]
  exact HeaderDock.input_local _ _ _ _ _ _ _ _ _ _ fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1 j

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
