import Proof.PCP.PCPPNativeQuery
import Proof.PCP.PCPPNativeCapacityBank

/-! The actual normalized Q-loop consumes the physically allocated cold
bank and physically generated sentinel drivers. It returns its actual
source cursor, node counter, and emitted native query bytes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def queryMachine := Composition.machine machine
  (RecoveryFocus.machine loopSlots PCPPNativeQueryLoop.machine)
def queryBudget (R Q G : ℕ) := budget R Q G+1+(Q*(6*G+9)+3)

theorem query_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) {n : ℕ} (x : BitInput n)
    (suffix : List Bool) (W C F G : ℕ) (oracle : BooleanCircuit R)
    (hW : 4 ≤ W) (hwidth : R ≤ W)
    (hstream : (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length ≤ W)
    (hpos : Q*(2*oracle.size+1) ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) (hG : 64*(W+1)*(F+1) ≤ G) :
    ∃ result,run queryMachine (queryBudget R Q G)
      (data (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q C F G 0)=some result ∧
      result.steps ≤ queryBudget R Q G ∧
      (∀ i : Fin 174,result.final.heads (loopSlots i)=
        (PCPPNativeQueryLoop.templateConfiguration 3 (PCPPNative.descriptor oracle)
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
          (Q*(2*oracle.size+1)) C F G
          ((PCPPNative.queryNodesPrefix 0 oracle
            ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap PCPPRequestNodeSchema.native) R Q 1).heads i ∧
        result.final.tapes (loopSlots i)=
        (PCPPNativeQueryLoop.templateConfiguration 3 (PCPPNative.descriptor oracle)
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
          (Q*(2*oracle.size+1)) C F G
          ((PCPPNative.queryNodesPrefix 0 oracle
            ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap PCPPRequestNodeSchema.native) R Q 1).tapes i) := by
  let bits := PCPPNative.descriptor oracle
  let fields := QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix
  obtain ⟨a,ha,as,af⟩ := cold_run bits fields R Q C F G
  obtain ⟨b,hb,bs,bf⟩ := PCPPNativeCapacity.normalized_run p R Q hR hQ x [] suffix 0 W C F G oracle []
    hW hwidth hstream (by simpa only [Nat.zero_add] using hpos) hC hF hG
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hb bf
  obtain ⟨c,hc,_,cs,ch,ct,_⟩ := RecoveryFocus.dock loopSlots loop_injective
    PCPPNativeQueryLoop.machine _ a.final.heads a.final.tapes (target bits fields R Q C F G)
    (fun i => (af i).1) (fun i => (af i).2) b hb
  have he : Composition.restart a.final (RecoveryFocus.machine loopSlots PCPPNativeQueryLoop.machine).start=
      (⟨(target bits fields R Q C F G).control,a.final.heads,a.final.tapes⟩) := by rfl
  rw [←he] at hc
  have joined := Composition.run_join machine (RecoveryFocus.machine loopSlots PCPPNativeQueryLoop.machine)
    _ _ _ a c ha hc
  refine ⟨Composition.joinedReceipt a c,joined,?_,?_⟩
  · change a.steps+1+c.steps ≤ queryBudget R Q G
    rw [cs]
    unfold queryBudget
    omega
  · intro i
    change c.final.heads (loopSlots i)=_ ∧ c.final.tapes (loopSlots i)=_
    rw [ch,ct,bf]
    exact ⟨rfl,rfl⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQueryCold
