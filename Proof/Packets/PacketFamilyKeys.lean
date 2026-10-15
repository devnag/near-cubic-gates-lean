import Proof.CaseAnalysis.FiveRowKeys

/-! # Row keys in the exact `F.rows` order, for the packet family loop.

Paper: "One external row. It fixes one child tuple g, prime p, walk seed e,
and scalar residue f" (`paper.tex:1193-1196`); "All external rows ... are
multiplied by q^{h_D} exactly once" (`:1204-1206`). Consumer:
`Request.raw selector a r = F.rows.flatMap (rawWord a F g)`
(`Proof/Assembly/Production.lean`), which the family loop must
emit row by row in exactly `F.rows` order, duplicates kept. Budget: none
(this module is definitions and one order equation).

`RowKeys a` is the interface the parent consumes: a key type per request, the
key list, its decoding, and the order equation `keys.map decode = F.rows`.
`rcFiveKeys a` SUPPLIES it from the checked closeout keys
(`Proof/CaseAnalysis/FiveRowKeys.lean`: `sym_rows_eq` `:40`, `thr_rows_eq` `:81`). The terminal
sentinel has no rows and an empty key type. Nothing physical is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketFamilyParent
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open FixedLivePackets PacketProduction
noncomputable section

/-- A row key per request, its list in emission order, and the proved
decoding into the actual family rows. The machine never materializes `keys`;
it is the mathematical list the cursor's order theorem is stated against. -/
structure RowKeys (a : DecompositionAlgorithm) where
  Key : Request → Type
  keys : ∀ r : Request, List (Key r)
  decode : ∀ r : Request, Key r → Packets.Row (r.family a).occurrences r.liveScale
  keys_eq : ∀ r : Request, (keys r).map (decode r) = (r.family a).rows

/-- The number of loop iterations is the number of family rows. -/
theorem RowKeys.length_eq {a : DecompositionAlgorithm} (K : RowKeys a) (r : Request) :
    (K.keys r).length = (r.family a).rows.length := by
  rw [← K.keys_eq r, List.length_map]

/-- The packet stream in key order is the consumer's `Request.raw`. -/
theorem RowKeys.raw_eq {a : DecompositionAlgorithm} (selector : CyclicChoice.Laws)
    (K : RowKeys a) (r : Request) :
    (K.keys r).flatMap (fun k => ExternalRowFamily.rawWord a (r.family a)
      (Packets.geometry selector (r.family a)) (K.decode r k)) = Request.raw selector a r := by
  have h := congrArg (fun rows => rows.flatMap (ExternalRowFamily.rawWord a (r.family a)
    (Packets.geometry selector (r.family a)))) (K.keys_eq r)
  simp only [List.flatMap_map] at h
  exact h

/-! ## The supplied instance: the checked closeout keys -/

/-- SYM: seed then offset tuple; THR: selection, prime, seed, residue < prime. -/
def rcKey (a : DecompositionAlgorithm) : Request → Type
  | .terminal => PEmpty
  | .sym r _ L target => RCFive.RowKeys.SymKey r L target
  | .thr r _ L target => RCFive.RowKeys.ThrKey a r L target

def rcKeys (a : DecompositionAlgorithm) : ∀ r : Request, List (rcKey a r)
  | .terminal => []
  | .sym r _ L target => RCFive.RowKeys.symKeys r L target
  | .thr r _ L target => RCFive.RowKeys.thrKeys a r L target

def rcDecode (a : DecompositionAlgorithm) :
    ∀ r : Request, rcKey a r → Packets.Row (r.family a).occurrences r.liveScale
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k => RCFive.RowKeys.symRow r L target k
  | .thr r _ L target, k => RCFive.RowKeys.thrRow a r L target k

theorem rc_keys_eq (a : DecompositionAlgorithm) (r : Request) :
    (rcKeys a r).map (rcDecode a r) = (r.family a).rows := by
  cases r with
  | terminal => rfl
  | sym r four L target => exact RCFive.RowKeys.sym_rows_eq r L target
  | thr r four L target => exact RCFive.RowKeys.thr_rows_eq a r L target

/-- SUPPLIED: the row-key order field, from `RCFiveRowKeys`. -/
def rcFiveKeys (a : DecompositionAlgorithm) : RowKeys a where
  Key := rcKey a
  keys := rcKeys a
  decode := rcDecode a
  keys_eq := rc_keys_eq a

end
end NearCubicWires.PacketFamilyParent
