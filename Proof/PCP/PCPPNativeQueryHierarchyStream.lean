import Proof.PCP.PCPPNativeQueryBank
import Proof.Hierarchy.HierarchyStreamReady

/-! The physical query-bank source is exactly the retained normalized
hierarchy field stream. There is no second projection codec or row order. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine RepairSource
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_framed {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) :
    rowCache projection=QueryBytes.framedCodes (List.ofFn fun i => projectionCode (projection i)) := by
  simp only [rowCache,rowFields,QueryBytes.framedCodes,List.map_ofFn,Function.comp_def]
theorem stream_framed_rows {n r : ℕ} (rows : List (Fin n → ProjectedRandomBit r)) :
    stream rows=QueryBytes.framedCodes ((rows.map fun projection => List.ofFn fun i => projectionCode (projection i)).flatten) := by
  induction rows with
  | nil => rfl
  | cons projection rows ih =>
    change rowCache projection++stream rows=QueryBytes.framedCodes
      ((List.ofFn fun i => projectionCode (projection i))++(rows.map fun row => List.ofFn fun i => projectionCode (row i)).flatten)
    rw [QueryBytes.framed_append,←row_framed,←ih]
theorem stream_framed {n r q : ℕ} (projections : Fin q → Fin n → ProjectedRandomBit r) :
    stream (List.ofFn projections)=QueryBytes.framedCodes
      (List.ofFn fun j => List.ofFn fun i => projectionCode (projections j i)).flatten := by
  rw [stream_framed_rows]
  simp only [List.map_ofFn,Function.comp_def]
theorem normalized_stream (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width ≤ R) (hQ : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) :
    stream (List.ofFn ((p.normalized R Q hR hQ).queryAddressBits x))=
      QueryBytes.framedCodes (normalizedRows p R Q).flatten := by
  rw [stream_framed]
  exact congrArg (fun rows => QueryBytes.framedCodes rows.flatten) (normalized_rows p R Q hR hQ x)

theorem normalized_bank_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width ≤ R) (hQ : p.queries ≤ Q) {n : ℕ} (x : BitInput n)
    (pre suffix : List Bool) (base C F G : ℕ) (oracle : BooleanCircuit R) (out : List Bool)
    (hCF : C+1 ≤ F) (hFG : F+1 ≤ G)
    (hreq : requirements base 0 C F G oracle
      (List.ofFn ((p.normalized R Q hR hQ).queryAddressBits x))) :
    ∃ result,runFrom machine (Q*(6*G+9)+3)
      (templateConfiguration 0 (PCPPNative.descriptor oracle)
        (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) pre.length
        base C F G out R Q 1)=some result ∧ result.steps ≤ Q*(6*G+9)+3 ∧
      result.final=templateConfiguration 3 (PCPPNative.descriptor oracle)
        (pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        (pre.length+(QueryBytes.framedCodes (normalizedRows p R Q).flatten).length)
        (base+Q*(2*oracle.size+1)) C F G
        (out++(PCPPNative.queryNodesPrefix base oracle
          ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap PCPPRequestNodeSchema.native) R Q 1 := by
  let projections : Fin Q → Fin R → ProjectedRandomBit R :=
    (p.normalized R Q hR hQ).queryAddressBits x
  have result := bank_run (n := R) (r := R) (q := Q) pre suffix base C F G oracle
    projections out hCF hFG hreq
  have hs : stream (List.ofFn projections)=QueryBytes.framedCodes (normalizedRows p R Q).flatten :=
    normalized_stream p R Q hR hQ x
  have hsource : source pre suffix (List.ofFn projections)=
      pre++QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix :=
    congrArg (fun bits => pre++bits++suffix) hs
  rw [hsource,hs] at result
  exact result

end NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
