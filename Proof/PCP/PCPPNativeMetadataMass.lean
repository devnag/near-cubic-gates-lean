import Proof.PCP.PCPPNativeMetadataMassLayout

/-! Original oracle/Q/M metadata followed by the two actual source scans.
The retained original bytes and measured unary counters share one run. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeMetadataMass
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem metadata_mass_run {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) : ∃ result,
    runFrom machine (budget p R Q oracle.size) (entry (PCPPNative.descriptor oracle) p R Q)=some result ∧
    result.steps≤budget p R Q oracle.size ∧
    ∀ j,result.final.heads (ports j)=0 ∧ result.final.tapes (ports j)=values oracle p Q j := by
  obtain ⟨a,ha,as,ah,a0,a32,a36,a45,a48,_⟩ := PCPPNativeMetadata.metadata_run oracle Q (Codec.clauses p).length
  let lifted := TapeEmbedding.receipt extraHeads (extras p R Q) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeMetadata.machine extraHeads (extras p R Q) _ _ a ha
  obtain ⟨query,sl,ml,hq,qs,qf⟩ := PCPPNativeMass.query_run p R Q hR hQ
  obtain ⟨b,hb,_,bs,bh,bt,baway⟩ := RecoveryFocus.dock querySlots query_injective PCPSerializerCapacity.MassReady.machine _
    lifted.final.heads lifted.final.tapes
    (PCPSerializerCapacity.MassReady.cfg PCPSerializerCapacity.MassReady.machine.start (queryBytes p R Q) 0 0 (R*Q) 0 0)
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl) query hq
  obtain ⟨clause,hcl,cls,clh4,clt4,clh5,clt5,clh0,clt0⟩ := PCPPNativeOriginalMass.clause_run p
  obtain ⟨c,hc,_,cs,ch,ct,caway⟩ := RecoveryFocus.dock clauseSlots clause_injective PCPPNativeTripleMass.machine _
    b.final.heads b.final.tapes
    (initialConfiguration PCPPNativeTripleMass.machine (PCPPNativeTripleMass.data (DedupBytes.fields p) (Codec.clauses p).length 0))
    (by
      intro i
      fin_cases i
      · change b.final.heads 48=0
        rw [(baway 48 (by decide)).1]
        change a.final.heads 48=0
        rw [ah]; rfl
      all_goals rw [(baway _ (by decide)).1]; rfl)
    (by
      intro i
      fin_cases i
      · change b.final.tapes 48=List.replicate (Codec.clauses p).length true
        rw [(baway 48 (by decide)).2]
        exact a48
      all_goals rw [(baway _ (by decide)).2]; rfl) clause hcl
  have hab := Composition.run_join first second _ _ _ lifted b firstRun hb
  have joined := Composition.run_join (Composition.machine first second) third _ _ _
    (Composition.joinedReceipt lifted b) c hab hc
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt lifted b) c,joined,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps≤budget p R Q oracle.size
    rw [bs,cs]
    unfold budget queryBytes
    omega
  · intro j
    change c.final.heads (ports j)=0 ∧ c.final.tapes (ports j)=values oracle p Q j
    fin_cases j
    · constructor
      · change c.final.heads 0=0
        rw [(caway 0 (by decide)).1,(baway 0 (by decide)).1]
        change a.final.heads 0=0
        rw [ah]; rfl
      · exact (caway 0 (by decide)).2.trans ((baway 0 (by decide)).2.trans a0)
    · constructor
      · change c.final.heads 32=0
        rw [(caway 32 (by decide)).1,(baway 32 (by decide)).1]
        change a.final.heads 32=0
        rw [ah]; rfl
      · exact (caway 32 (by decide)).2.trans ((baway 32 (by decide)).2.trans a32)
    · constructor
      · change c.final.heads 36=0
        rw [(caway 36 (by decide)).1,(baway 36 (by decide)).1]
        change a.final.heads 36=0
        rw [ah]; rfl
      · exact (caway 36 (by decide)).2.trans ((baway 36 (by decide)).2.trans a36)
    · constructor
      · change c.final.heads 45=0
        rw [(caway 45 (by decide)).1,(baway 45 (by decide)).1]
        change a.final.heads 45=0
        rw [ah]; rfl
      · exact (caway 45 (by decide)).2.trans ((baway 45 (by decide)).2.trans a45)
    · exact ⟨(ch 0).trans clh0,(ct 0).trans clt0⟩
    · constructor
      · exact (caway 52 (by decide)).1.trans ((bh 0).trans (by rw [qf]; rfl))
      · exact (caway 52 (by decide)).2.trans ((bt 0).trans (by rw [qf]; rfl))
    · constructor
      · exact (caway 53 (by decide)).1.trans ((bh 1).trans (by rw [qf]; rfl))
      · exact (caway 53 (by decide)).2.trans ((bt 1).trans (by rw [qf]; rfl))
    · exact ⟨(ch 4).trans clh4,(ct 4).trans clt4⟩
    · exact ⟨(ch 5).trans clh5,(ct 5).trans clt5⟩

end NearCubicWires.RepairOrdinary.PCPPNativeMetadataMass
