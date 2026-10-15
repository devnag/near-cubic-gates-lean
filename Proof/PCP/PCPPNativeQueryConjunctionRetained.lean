import Proof.PCP.PCPPNativeQueryConjunction
import Proof.PCP.PCPPNativeResourceQueryRetained

/-! Original oracle and raw size survive the exact query/conjunction
executor, ready for its real original-footer scalar caller. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryConjunction
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem query_conjunction_retained_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit R) (suffix : List Bool) (M Lc : ℕ) :
    let Lq := (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
    let W := PCPPNativeResources.W R Q oracle.size M Lq Lc
    let out := queryBytes p R Q hR hQ x oracle++PCPPNativeConjunctionStart.trueBits
    ∃ result,run machine (budget R Q oracle.size M Lq Lc)
      (input (PCPPNative.descriptor oracle) (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        R Q oracle.size M Lq Lc)=some result ∧ result.steps ≤ budget R Q oracle.size M Lq Lc ∧
      result.final.heads 102=out.length ∧ result.final.tapes 102=out ∧
      result.final.heads 276=0 ∧ result.final.tapes 276=List.replicate (Q*(2*oracle.size+1)+1) true ∧
      result.final.heads 99=0 ∧ result.final.tapes 99=List.replicate (Q*(2*oracle.size+1)) true ∧
      result.final.heads 42=0 ∧ result.final.tapes 42=List.replicate (PCPPNativeCapacityReady.C W) true ∧
      result.final.heads 2=0 ∧ result.final.tapes 2=List.replicate M true ∧
      result.final.heads 6=0 ∧ result.final.tapes 6=UnaryTemplate.tape (PCPPNativeCount.stride oracle.size) ∧
      result.final.heads 14=0 ∧ result.final.tapes 14=List.replicate (PCPPNativeCount.outputIndex Q oracle.size M) true ∧
      result.final.heads 16=0 ∧ result.final.tapes 16=List.replicate (PCPPNativeCount.nativeSize Q oracle.size M) true ∧
      result.final.heads 95=0 ∧ result.final.tapes 95=PCPPNative.descriptor oracle ∧
      result.final.heads 1=0 ∧ result.final.tapes 1=List.replicate oracle.size true := by
  intro Lq W out
  obtain ⟨a,ha,as,af,a2h,a2,a6h,a6,a14h,a14,a16h,a16,a1h,a1⟩ :=
    PCPPNativeResourceQuery.resource_query_with_size_run p R Q hR hQ x oracle suffix M Lc
  let bytes := queryBytes p R Q hR hQ x oracle
  let lifted := TapeEmbedding.receipt (fun _ : Fin 3 => 0) (fun _ => []) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeResourceQuery.machine (fun _ : Fin 3 => 0)
    (fun _ => []) _ _ a ha
  have low (i : Fin 171) : a.final.heads (PCPPNativeResourceQuery.querySlots (PCPPNativeQueryCold.loopSlots (i.castAdd 3)))=
      PCPPNativeQueryReusable.heads bytes i ∧
      a.final.tapes (PCPPNativeResourceQuery.querySlots (PCPPNativeQueryCold.loopSlots (i.castAdd 3)))=
      PCPPNativeQueryReusable.data (PCPPNative.descriptor oracle) [] (Q*(2*oracle.size+1))
        (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W) bytes i := by
    have hl := PCPPNativeQueryLoop.template_lower 3 (PCPPNative.descriptor oracle)
      (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) Lq (Q*(2*oracle.size+1))
      (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W) bytes R Q 1 i
    exact ⟨(af (i.castAdd 3)).1.trans hl.1,(af (i.castAdd 3)).2.trans hl.2⟩
  obtain ⟨b,hb,bs,bh,bt⟩ := PCPPNativeConjunctionStart.start_run (Q*(2*oracle.size+1)) bytes
  obtain ⟨c,hc,_,cs,ch,ct,other⟩ := RecoveryFocus.dock seedSlots seed_injective PCPPNativeConjunctionStart.machine _
    lifted.final.heads lifted.final.tapes (PCPPNativeConjunctionStart.entry (Q*(2*oracle.size+1)) bytes)
    (by intro i; fin_cases i; exact (low 2).1; rfl; rfl; rfl; exact (low 5).1)
    (by intro i; fin_cases i; exact (low 2).2; rfl; rfl; rfl; exact (low 5).2) b hb
  have joined := Composition.run_join first second _ _ _ lifted c firstRun hc
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ => [])
      (initialConfiguration PCPPNativeResourceQuery.machine
        (PCPPNativeResourceQuery.input (PCPPNative.descriptor oracle)
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size M Lq Lc)))=
      initialConfiguration machine (input (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size M Lq Lc) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 275) (n := 3) (fun _ => ?_) (fun _ => ?_) i <;>
        simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [hi] at joined
  have sht (i : Fin 5) : c.final.heads (seedSlots i)=PCPPNativeConjunctionStart.heads out i := by rw [ch,bh]
  have stt (i : Fin 5) : c.final.tapes (seedSlots i)=PCPPNativeConjunctionStart.output (Q*(2*oracle.size+1)) bytes i := by rw [ct,bt]
  refine ⟨Composition.joinedReceipt lifted c,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps ≤ budget R Q oracle.size M Lq Lc
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs
  · change c.final.heads 102=_
    exact sht 4
  · change c.final.tapes 102=_
    exact stt 4
  · change c.final.heads 276=0
    exact sht 2
  · change c.final.tapes 276=_
    exact stt 2
  · change c.final.heads 99=0
    exact sht 0
  · change c.final.tapes 99=_
    exact stt 0
  · change c.final.heads 42=0
    exact (other 42 (by decide)).1.trans (low 4).1
  · change c.final.tapes 42=_
    exact (other 42 (by decide)).2.trans (low 4).2
  · change c.final.heads 2=0
    exact (other 2 (by decide)).1.trans a2h
  · change c.final.tapes 2=_
    exact (other 2 (by decide)).2.trans a2
  · change c.final.heads 6=0
    exact (other 6 (by decide)).1.trans a6h
  · change c.final.tapes 6=_
    exact (other 6 (by decide)).2.trans a6
  · change c.final.heads 14=0
    exact (other 14 (by decide)).1.trans a14h
  · change c.final.tapes 14=_
    exact (other 14 (by decide)).2.trans a14
  · change c.final.heads 16=0
    exact (other 16 (by decide)).1.trans a16h
  · change c.final.tapes 16=_
    exact (other 16 (by decide)).2.trans a16

  · change c.final.heads 95=0
    exact (other 95 (by decide)).1.trans (low 0).1
  · change c.final.tapes 95=_
    exact (other 95 (by decide)).2.trans (low 0).2
  · change c.final.heads 1=0
    exact (other 1 (by decide)).1.trans a1h
  · change c.final.tapes 1=_
    exact (other 1 (by decide)).2.trans a1

end NearCubicWires.RepairOrdinary.PCPPNativeQueryConjunction
