import Proof.PCP.PCPPNativeCapacityQuery

/-! Apply common capacities to the SAME normalized hierarchy Q-loop.
Only its total actual query bytes and final node count are measured. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacity
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bank_requirements {n r : ℕ} (oracle : BooleanCircuit n)
    (rows : List (Fin n → ProjectedRandomBit r)) (base index W C F G : ℕ)
    (hW : 4 ≤ W) (hn : n ≤ W) (hr : r ≤ W)
    (hstream : (PCPPNativeQueryLoop.stream rows).length ≤ W)
    (hp : base+(index+rows.length)*(2*oracle.size+1) ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) (hG : 64*(W+1)*(F+1) ≤ G) :
    PCPPNativeQueryLoop.requirements base index C F G oracle rows := by
  induction rows generalizing index with
  | nil => trivial
  | cons row rows ih =>
    have hs : (rowCache row).length+(PCPPNativeQueryLoop.stream rows).length ≤ W := by
      simpa only [PCPPNativeQueryLoop.stream,List.flatMap_cons,List.length_append] using hstream
    have hp' : base+(index+1+rows.length)*(2*oracle.size+1) ≤ W := by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp
    have hpos : base+index*(2*oracle.size+1)+2*oracle.size+1 ≤ W := by
      have hnon : 0 ≤ rows.length*(2*oracle.size+1) := Nat.zero_le _
      nlinarith
    exact ⟨(query_capacity oracle row (base+index*(2*oracle.size+1)) W C F G
      hW hn hr (by omega) hpos hC hF hG).2.2,ih (index+1) (by omega) hp'⟩

theorem normalized_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) {n : ℕ} (x : BitInput n)
    (pre suffix : List Bool) (base W C F G : ℕ) (oracle : BooleanCircuit R) (out : List Bool)
    (hW : 4 ≤ W) (hwidth : R ≤ W)
    (hstream : (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length ≤ W)
    (hpos : base+Q*(2*oracle.size+1) ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) (hG : 64*(W+1)*(F+1) ≤ G) :
    ∃ result,runFrom PCPPNativeQueryLoop.machine (Q*(6*G+9)+3)
      (PCPPNativeQueryLoop.templateConfiguration 0 (PCPPNative.descriptor oracle)
        (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) pre.length
        base C F G out R Q 1)=some result ∧ result.steps ≤ Q*(6*G+9)+3 ∧
      result.final=PCPPNativeQueryLoop.templateConfiguration 3 (PCPPNative.descriptor oracle)
        (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        (pre.length+(QueryBytes.framedCodes (normalizedRows p R Q).flatten).length)
        (base+Q*(2*oracle.size+1)) C F G
        (out++(PCPPNative.queryNodesPrefix base oracle
          ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap PCPPRequestNodeSchema.native) R Q 1 := by
  have hl := linear W C hC
  have hfg : F+1 ≤ 64*(W+1)*(F+1) := by nlinarith
  let projections : Fin Q → Fin R → ProjectedRandomBit R :=
    (p.normalized R Q hR hQ).queryAddressBits x
  have hbytes : (PCPPNativeQueryLoop.stream (List.ofFn projections)).length ≤ W := by
    have he : PCPPNativeQueryLoop.stream (List.ofFn projections)=
        QueryBytes.framedCodes (normalizedRows p R Q).flatten :=
      PCPPNativeQueryLoop.normalized_stream p R Q hR hQ x
    rw [he]
    exact hstream
  have hend : base+(0+(List.ofFn projections).length)*(2*oracle.size+1) ≤ W := by
    simpa only [List.length_ofFn,Nat.zero_add] using hpos
  have hreq := bank_requirements oracle (List.ofFn projections) base 0 W C F G
    hW hwidth hwidth hbytes hend hC hF hG
  exact PCPPNativeQueryLoop.normalized_bank_run p R Q hR hQ x pre suffix base C F G oracle out
    (by omega) (by omega) hreq

end NearCubicWires.RepairOrdinary.PCPPNativeCapacity
