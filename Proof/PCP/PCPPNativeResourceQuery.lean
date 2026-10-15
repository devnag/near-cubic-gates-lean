import Proof.PCP.PCPPNativeResourceQueryLayout

/-! The cold native query executor derives its shared C/F/G and exact
counts physically from the SAME source counts and measured stream masses.
It retains the metadata used by the ensuing clause/header/tail caller. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def output (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width ≤ R) (hQ : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (suffix : List Bool) (W : ℕ) :=
  PCPPNativeQueryLoop.templateConfiguration 3 (PCPPNative.descriptor oracle)
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
    (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length (Q*(2*oracle.size+1))
    (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W)
    ((PCPPNative.queryNodesPrefix 0 oracle ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap
      PCPPRequestNodeSchema.native) R Q 1

theorem resource_query_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit R) (suffix : List Bool) (M Lc : ℕ) :
    let Lq := (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
    let W := PCPPNativeResources.W R Q oracle.size M Lq Lc
    ∃ result,run machine (budget R Q oracle.size M Lq Lc)
      (input (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size M Lq Lc)=some result ∧
      result.steps ≤ budget R Q oracle.size M Lq Lc ∧
      (∀ i : Fin 174,result.final.heads (querySlots (PCPPNativeQueryCold.loopSlots i))=
        (output p R Q hR hQ x oracle suffix W).heads i ∧
        result.final.tapes (querySlots (PCPPNativeQueryCold.loopSlots i))=
        (output p R Q hR hQ x oracle suffix W).tapes i) ∧
      result.final.heads 2=0 ∧ result.final.tapes 2=List.replicate M true ∧
      result.final.heads 6=0 ∧ result.final.tapes 6=UnaryTemplate.tape (PCPPNativeCount.stride oracle.size) ∧
      result.final.heads 14=0 ∧ result.final.tapes 14=List.replicate (PCPPNativeCount.outputIndex Q oracle.size M) true ∧
      result.final.heads 16=0 ∧ result.final.tapes 16=List.replicate (PCPPNativeCount.nativeSize Q oracle.size M) true := by
  intro Lq W
  let bits := PCPPNative.descriptor oracle
  let fields := QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix
  obtain ⟨caps,hcaps,_,hC,hF,hG,hQr,_,hM,hRr,_,_,hstride,_,hindex,hsize⟩ :=
    PCPPNativeResources.resource_run R Q oracle.size M Lq Lc
  obtain ⟨a,ha,adata,ah,asteps⟩ := hcaps.focus resourceSlots resource_injective
    (input bits fields R Q oracle.size M Lq Lc) (resource_input bits fields R Q oracle.size M Lq Lc)
  obtain ⟨h4,hRW,_,hNW,_,hLqW,_⟩ := PCPPNativeResources.bounds R Q oracle.size M Lq Lc
  obtain ⟨hCW,hFW,hGW⟩ := PCPPNativeCapacityReady.scalar_bounds W
  have hpos : Q*(2*oracle.size+1) ≤ W := by
    change PCPPNativeCount.nativeSize Q oracle.size M ≤ W at hNW
    unfold PCPPNativeCount.nativeSize PCPPNativeCount.outputIndex PCPPNativeCount.queryEnd PCPPNativeCount.stride at hNW
    omega
  have hCW' : 4096*(W+1)^2 ≤ PCPPNativeCapacityReady.C W := by nlinarith
  obtain ⟨b,hb,bs,bfields⟩ := PCPPNativeQueryCold.query_run p R Q hR hQ x suffix W
    (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W)
    oracle h4 hRW hLqW hpos hCW' hFW hGW
  have ht (i : Fin 178) : a.final.tapes (querySlots i)=PCPPNativeQueryCold.data bits fields R Q
      (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W) 0 i := by
    rw [adata]
    exact query_input bits fields R Q oracle.size M Lq Lc _ _ _ caps hC hF hG hQr hRr i
  obtain ⟨c,hc,_,cs,ch,ct,other⟩ := RecoveryFocus.dock querySlots query_injective PCPPNativeQueryCold.queryMachine _
    a.final.heads a.final.tapes
    (⟨PCPPNativeQueryCold.queryMachine.start,(fun _ => 0),PCPPNativeQueryCold.data bits fields R Q
      (PCPPNativeCapacityReady.C W) (PCPPNativeCapacityReady.F W) (PCPPNativeCapacityReady.G W) 0⟩)
    (fun i => ah (querySlots i)) ht b hb
  have joined := Composition.run_join first second _ _ _ a c ha hc
  refine ⟨Composition.joinedReceipt a c,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps ≤ budget R Q oracle.size M Lq Lc
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right asteps 1) bs
  · intro i
    change c.final.heads (querySlots (PCPPNativeQueryCold.loopSlots i))=_ ∧
      c.final.tapes (querySlots (PCPPNativeQueryCold.loopSlots i))=_
    rw [ch,ct]
    exact bfields i
  · change c.final.heads 2=0
    exact (other 2 (by decide)).1.trans (ah 2)
  · change c.final.tapes 2=_
    rw [(other 2 (by decide)).2,adata]
    exact (prepared_low bits fields R Q oracle.size M Lq Lc caps 2).trans hM
  · change c.final.heads 6=0
    exact (other 6 (by decide)).1.trans (ah 6)
  · change c.final.tapes 6=_
    rw [(other 6 (by decide)).2,adata]
    exact (prepared_low bits fields R Q oracle.size M Lq Lc caps 6).trans hstride
  · change c.final.heads 14=0
    exact (other 14 (by decide)).1.trans (ah 14)
  · change c.final.tapes 14=_
    rw [(other 14 (by decide)).2,adata]
    exact (prepared_low bits fields R Q oracle.size M Lq Lc caps 14).trans hindex
  · change c.final.heads 16=0
    exact (other 16 (by decide)).1.trans (ah 16)
  · change c.final.tapes 16=_
    rw [(other 16 (by decide)).2,adata]
    exact (prepared_low bits fields R Q oracle.size M Lq Lc caps 16).trans hsize

end NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
