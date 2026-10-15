import Proof.SourceAssembly.SLoadPoolReady

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RowInput
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

variable {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} {privateWork : Nat} {r : Request}

/-! ### The two public metadata ports are above the header block -/

theorem requestPort_val (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowRequestPort printer privateWork).val
      = 440 + (P1TopDownPaidPayload.tapes printer + 2) := rfl

theorem capsPort_val (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowCapsPort printer privateWork).val
      = 440 + (P1TopDownPaidPayload.tapes printer + 2) + 1 := rfl

theorem requestPort_ne_zero (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowRequestPort printer privateWork).val ≠ 0 := by
  rw [requestPort_val]; omega

theorem requestPort_ne_262 (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowRequestPort printer privateWork).val ≠ 262 := by
  rw [requestPort_val]; omega

theorem capsPort_ne_zero (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowCapsPort printer privateWork).val ≠ 0 := by
  rw [capsPort_val]; omega

theorem capsPort_ne_262 (printer : WilliamsAlgorithm) (privateWork : Nat) :
    (rowCapsPort printer privateWork).val ≠ 262 := by
  rw [capsPort_val]; omega

theorem capsPort_ne_requestPort (printer : WilliamsAlgorithm) (privateWork : Nat) :
    rowCapsPort printer privateWork ≠ rowRequestPort printer privateWork := by
  intro h
  have hv : (rowCapsPort printer privateWork).val
      = (rowRequestPort printer privateWork).val := congrArg Fin.val h
  rw [capsPort_val, requestPort_val] at hv
  omega

/-! ### `rowPublicInput` is blank away from four tapes -/

theorem row_pool (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (i : Fin (rowTapes printer privateWork + 1)) (h : i.val = 0) :
    rowPublicInput selector a printer privateWork r layout caps i
      = exactListWord (Packets.pool a (r.family a) (geometryOf selector a r)) := by
  simp only [rowPublicInput, if_pos h]

theorem row_raw (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (i : Fin (rowTapes printer privateWork + 1))
    (h0 : i.val ≠ 0) (h : i.val = 262) :
    rowPublicInput selector a printer privateWork r layout caps i = r.raw selector a := by
  simp only [rowPublicInput, if_neg h0, if_pos h]

theorem row_request (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) :
    rowPublicInput selector a printer privateWork r layout caps
        (rowRequestPort printer privateWork) = frame (r.input a) := by
  unfold rowPublicInput
  rw [if_neg (requestPort_ne_zero printer privateWork),
    if_neg (requestPort_ne_262 printer privateWork), if_pos rfl]

theorem row_caps (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) :
    rowPublicInput selector a printer privateWork r layout caps
        (rowCapsPort printer privateWork)
      = rowMetadataWord layout.w layout.degree layout.C caps := by
  unfold rowPublicInput
  rw [if_neg (capsPort_ne_zero printer privateWork),
    if_neg (capsPort_ne_262 printer privateWork),
    if_neg (capsPort_ne_requestPort printer privateWork), if_pos rfl]

theorem row_blank (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (caps : RowCaps) (i : Fin (rowTapes printer privateWork + 1))
    (h0 : i.val ≠ 0) (h262 : i.val ≠ 262)
    (hq : i ≠ rowRequestPort printer privateWork)
    (hc : i ≠ rowCapsPort printer privateWork) :
    rowPublicInput selector a printer privateWork r layout caps i = [] := by
  simp only [rowPublicInput, if_neg h0, if_neg h262, if_neg hq, if_neg hc]

/-! ### The two aliases are free -/

/-- The cold run leaves the family's tape-`0` word on pool tape `34`, which
`MaskFamilyCode.poolAlias` identifies with the family header tape `0`. -/
theorem pool_alias_word {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) :
    BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a F) 34
      = exactListWord (Packets.pool a F g) :=
  CachedFamilyLoader.cache_word a F g

/-- Both alias targets carry `Fin.val` equal to the index `rowPublicInput`
tests, so no transport is needed at either. -/
theorem header_val (printer : WilliamsAlgorithm) (work : Nat) (i : Fin 440) :
    ((SharedRowLayout.headerSlots printer work i).castAdd 1).val = i.val := rfl

/-! ### Residency -/

/-- The whole `setupLoad` target bank reduces to two aliased words, two
produced words and a zero backing everywhere else. -/
theorem residency {U : Nat} (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (A : Fin U → List Bool) (reserve : Fin (rowTapes printer privateWork + 1) → Nat)
    (hpool : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 0 →
      A (familySlots i) = ZeroPadding.pad (reserve i)
        (exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))))
    (hraw : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 262 →
      A (familySlots i) = ZeroPadding.pad (reserve i) (r.raw selector a))
    (hreq : A (familySlots (rowRequestPort printer privateWork))
      = ZeroPadding.pad (reserve (rowRequestPort printer privateWork)) (frame (r.input a)))
    (hcap : A (familySlots (rowCapsPort printer privateWork))
      = ZeroPadding.pad (reserve (rowCapsPort printer privateWork))
        (rowMetadataWord layout.w layout.degree layout.C caps))
    (hblank : ∀ i : Fin (rowTapes printer privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      i ≠ rowRequestPort printer privateWork → i ≠ rowCapsPort printer privateWork →
      A (familySlots i) = List.replicate (reserve i) false) :
    ∀ i, A (familySlots i) = ZeroPadding.pad (reserve i)
      (rowPublicInput selector a printer privateWork r layout caps i) := by
  intro i
  by_cases h0 : i.val = 0
  · rw [hpool i h0, row_pool layout caps i h0]
  by_cases h262 : i.val = 262
  · rw [hraw i h262, row_raw layout caps i h0 h262]
  by_cases hq : i = rowRequestPort printer privateWork
  · subst hq; rw [hreq, row_request layout caps]
  by_cases hc : i = rowCapsPort printer privateWork
  · subst hc; rw [hcap, row_caps layout caps]
  rw [hblank i h0 h262 hq hc, row_blank layout caps i h0 h262 hq hc, Words.pad_nil]

/-- Consequently the `setupLoad` exit bank IS the ambient bank: `install` at a
family slot family that is already resident is the identity, and injectivity of
`familySlots` is not needed for it. -/
theorem install_row {U : Nat} (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (A : Fin U → List Bool) (reserve : Fin (rowTapes printer privateWork + 1) → Nat)
    (h : ∀ i, A (familySlots i) = ZeroPadding.pad (reserve i)
      (rowPublicInput selector a printer privateWork r layout caps i)) :
    install familySlots A (fun i => ZeroPadding.pad (reserve i)
      (rowPublicInput selector a printer privateWork r layout caps i)) = A :=
  install_existing familySlots A _ h

end
end SLoad.RowInput
