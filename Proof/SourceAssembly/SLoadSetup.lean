import Proof.SourceAssembly.SLoadRowInput

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Setup
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- The setup loader: two paid framings on one ambient layout. -/
noncomputable def machine {U : Nat} (s1 d1 t1 l1 s2 d2 t2 l2 : Fin U) :=
  Composition.machine (MaskFrame.machine s1 d1 t1 l1) (MaskFrame.machine s2 d2 t2 l2)

/-- Fuel for the setup loader, in the two physical word lengths. -/
def cost (n1 n2 : Nat) : Nat := (4 * n1 + 4) + 1 + (4 * n2 + 4)

/-- Two independent framings, sequenced. -/
theorem setup_frames {U : Nat} (s1 d1 t1 l1 s2 d2 t2 l2 : Fin U)
    (h1 : s1 ≠ d1) (h2 : s1 ≠ t1) (h3 : s1 ≠ l1)
    (h4 : d1 ≠ t1) (h5 : d1 ≠ l1) (h6 : t1 ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ t2) (k3 : s2 ≠ l2)
    (k4 : d2 ≠ t2) (k5 : d2 ≠ l2) (k6 : t2 ≠ l2)
    (m1 : t1 ≠ s2) (m2 : t1 ≠ d2) (m3 : t1 ≠ t2) (m4 : t1 ≠ l2)
    (capS1 capD1 cap1 capL1 capS2 capD2 cap2 capL2 : Nat) (w1 w2 : List Bool)
    (hl1 : 2 * w1.length + 1 ≤ capL1) (hl2 : 2 * w2.length + 1 ≤ capL2)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH1s : H s1 = 0) (hH1d : H d1 = 0) (hH1t : H t1 = 0) (hH1l : H l1 = 0)
    (hH2s : H s2 = 0) (hH2d : H d2 = 0) (hH2t : H t2 = 0) (hH2l : H l2 = 0)
    (hA1s : A s1 = ZeroPadding.pad capS1 w1)
    (hA1d : A d1 = ZeroPadding.pad capD1 (List.replicate w1.length true))
    (hA1t : A t1 = List.replicate cap1 false) (hA1l : A l1 = List.replicate capL1 false)
    (hA2s : A s2 = ZeroPadding.pad capS2 w2)
    (hA2d : A d2 = ZeroPadding.pad capD2 (List.replicate w2.length true))
    (hA2t : A t2 = List.replicate cap2 false) (hA2l : A l2 = List.replicate capL2 false) :
    Step (machine s1 d1 t1 l1 s2 d2 t2 l2) (cost w1.length w2.length) H A H
      (Function.update (Function.update A t1 (ZeroPadding.pad cap1 (frame w1))) t2
        (ZeroPadding.pad cap2 (frame w2))) := by
  have e1 := MaskFrame.mask_frame_step s1 d1 t1 l1 h1 h2 h3 h4 h5 h6
    capS1 capD1 cap1 capL1 w1 hl1 H A hH1s hH1d hH1t hH1l hA1s hA1d hA1t hA1l
  have e2 := MaskFrame.mask_frame_step s2 d2 t2 l2 k1 k2 k3 k4 k5 k6
    capS2 capD2 cap2 capL2 w2 hl2 H
    (Function.update A t1 (ZeroPadding.pad cap1 (frame w1))) hH2s hH2d hH2t hH2l
    (by rw [Function.update_of_ne (Ne.symm m1)]; exact hA2s)
    (by rw [Function.update_of_ne (Ne.symm m2)]; exact hA2d)
    (by rw [Function.update_of_ne (Ne.symm m3)]; exact hA2t)
    (by rw [Function.update_of_ne (Ne.symm m4)]; exact hA2l)
  exact e1.seq e2

/-- The bare metadata bits the caps port's word frames. -/
def metaBits (w degree C : Nat) (caps : RowCaps) : List Bool :=
  natListWord [w, degree, C] ++ caps.word

theorem meta_frame (w degree C : Nat) (caps : RowCaps) :
    rowMetadataWord w degree C caps = frame (metaBits w degree C caps) := rfl

/-- The second conjunct of `MaskFamilyCode.Prepared`, for the setup loader. -/
theorem setup_load_step {U : Nat} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {privateWork : Nat} {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (familySlots : Fin (rowTapes printer privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (familyReserve : Fin (rowTapes printer privateWork + 1) → Nat)
    (s1 d1 l1 s2 d2 l2 : Fin U)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (capS1 capD1 capL1 capS2 capD2 capL2 : Nat)
    (hl1 : 2 * (r.input a).length + 1 ≤ capL1)
    (hl2 : 2 * (metaBits layout.w layout.degree layout.C caps).length + 1 ≤ capL2)
    -- the entry side: the cold run's output bank sits at the pool slots
    (hpH : ∀ i, H (poolSlots i) = 0)
    (hpA : ∀ i, A (poolSlots i) = ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i))
    -- every family slot is at head zero
    (hfH : ∀ i, H (familySlots i) = 0)
    -- the two framer scratch families are fresh from each other
    (h1 : s1 ≠ d1) (h2 : s1 ≠ familySlots (rowRequestPort printer privateWork))
    (h3 : s1 ≠ l1) (h4 : d1 ≠ familySlots (rowRequestPort printer privateWork))
    (h5 : d1 ≠ l1) (h6 : familySlots (rowRequestPort printer privateWork) ≠ l1)
    (k1 : s2 ≠ d2) (k2 : s2 ≠ familySlots (rowCapsPort printer privateWork))
    (k3 : s2 ≠ l2) (k4 : d2 ≠ familySlots (rowCapsPort printer privateWork))
    (k5 : d2 ≠ l2) (k6 : familySlots (rowCapsPort printer privateWork) ≠ l2)
    (m1 : familySlots (rowRequestPort printer privateWork) ≠ s2)
    (m2 : familySlots (rowRequestPort printer privateWork) ≠ d2)
    (m4 : familySlots (rowRequestPort printer privateWork) ≠ l2)
    -- the framer resources
    (hH1s : H s1 = 0) (hH1d : H d1 = 0) (hH1l : H l1 = 0)
    (hH2s : H s2 = 0) (hH2d : H d2 = 0) (hH2l : H l2 = 0)
    (hA1s : A s1 = ZeroPadding.pad capS1 (r.input a))
    (hA1d : A d1 = ZeroPadding.pad capD1 (List.replicate (r.input a).length true))
    (hA1l : A l1 = List.replicate capL1 false)
    (hA2s : A s2 = ZeroPadding.pad capS2 (metaBits layout.w layout.degree layout.C caps))
    (hA2d : A d2 = ZeroPadding.pad capD2 (List.replicate (metaBits layout.w layout.degree layout.C caps).length true))
    (hA2l : A l2 = List.replicate capL2 false)
    -- the two destination slots start zero-backed
    (hA1t : A (familySlots (rowRequestPort printer privateWork))
      = List.replicate (familyReserve (rowRequestPort printer privateWork)) false)
    (hA2t : A (familySlots (rowCapsPort printer privateWork))
      = List.replicate (familyReserve (rowCapsPort printer privateWork)) false)
    -- the two aliases, and the zero backing on every other family tape
    (hfam0 : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 0 →
      A (familySlots i) = ZeroPadding.pad (familyReserve i)
        (exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))))
    (hfam262 : ∀ i : Fin (rowTapes printer privateWork + 1), i.val = 262 →
      A (familySlots i) = ZeroPadding.pad (familyReserve i) (r.raw selector a))
    (hfamBlank : ∀ i : Fin (rowTapes printer privateWork + 1), i.val ≠ 0 → i.val ≠ 262 →
      i ≠ rowRequestPort printer privateWork → i ≠ rowCapsPort printer privateWork →
      A (familySlots i) = List.replicate (familyReserve i) false) :
    ∃ ambientA : Fin U → List Bool,
      Step (machine s1 d1 (familySlots (rowRequestPort printer privateWork)) l1
              s2 d2 (familySlots (rowCapsPort printer privateWork)) l2)
        (cost (r.input a).length (metaBits layout.w layout.degree layout.C caps).length)
        (dockH poolSlots H (fun _ => 0))
        (install poolSlots A (fun i => ZeroPadding.pad (poolReserve i)
          (BinaryCacheColdRun.output (CachedFamilyLoader.cacheArgs a (r.family a)) i)))
        (dockH familySlots H (fun _ => 0))
        (install familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
          (rowPublicInput selector a printer privateWork r layout caps i))) := by
  classical
  have hne : familySlots (rowRequestPort printer privateWork)
      ≠ familySlots (rowCapsPort printer privateWork) := fun h =>
    (RowInput.capsPort_ne_requestPort printer privateWork) (hfinj h).symm
  set A' : Fin U → List Bool :=
    Function.update (Function.update A (familySlots (rowRequestPort printer privateWork))
      (ZeroPadding.pad (familyReserve (rowRequestPort printer privateWork))
        (frame (r.input a))))
      (familySlots (rowCapsPort printer privateWork))
      (ZeroPadding.pad (familyReserve (rowCapsPort printer privateWork))
        (frame (metaBits layout.w layout.degree layout.C caps))) with hA'
  have step := setup_frames s1 d1 (familySlots (rowRequestPort printer privateWork)) l1
    s2 d2 (familySlots (rowCapsPort printer privateWork)) l2
    h1 h2 h3 h4 h5 h6 k1 k2 k3 k4 k5 k6 m1 m2 hne m4
    capS1 capD1 (familyReserve (rowRequestPort printer privateWork)) capL1
    capS2 capD2 (familyReserve (rowCapsPort printer privateWork)) capL2
    (r.input a) (metaBits layout.w layout.degree layout.C caps) hl1 hl2 H A
    hH1s hH1d (hfH _) hH1l hH2s hH2d (hfH _) hH2l
    hA1s hA1d hA1t hA1l hA2s hA2d hA2t hA2l
  -- the exit bank is resident at every family slot
  have hres : ∀ i, A' (familySlots i) = ZeroPadding.pad (familyReserve i)
      (rowPublicInput selector a printer privateWork r layout caps i) := by
    refine RowInput.residency familySlots layout caps A' familyReserve ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) := by
        intro h
        exact RowInput.requestPort_ne_zero printer privateWork (by rw [← hfinj h]; exact hi)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) := by
        intro h
        exact RowInput.capsPort_ne_zero printer privateWork (by rw [← hfinj h]; exact hi)
      rw [hA', Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfam0 i hi
    · intro i hi
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) := by
        intro h
        exact RowInput.requestPort_ne_262 printer privateWork (by rw [← hfinj h]; exact hi)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) := by
        intro h
        exact RowInput.capsPort_ne_262 printer privateWork (by rw [← hfinj h]; exact hi)
      rw [hA', Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfam262 i hi
    · rw [hA', Function.update_of_ne hne, Function.update_self]
    · rw [hA', Function.update_self, meta_frame]
    · intro i h0 h262 hq hc
      have e1 : familySlots i ≠ familySlots (rowRequestPort printer privateWork) :=
        fun h => hq (hfinj h)
      have e2 : familySlots i ≠ familySlots (rowCapsPort printer privateWork) :=
        fun h => hc (hfinj h)
      rw [hA', Function.update_of_ne e2, Function.update_of_ne e1]
      exact hfamBlank i h0 h262 hq hc
  refine ⟨A', ?_⟩
  rw [SLoad.dockH_existing poolSlots H (fun _ => 0) hpH,
    install_existing poolSlots A _ hpA,
    SLoad.dockH_existing familySlots H (fun _ => 0) hfH,
    RowInput.install_row familySlots layout caps A' familyReserve hres]
  exact step

/-! ### Two of `Prepared`'s remaining obligations are already clauses of
`RowCaps.Good` — citations, not work. -/

/-- The third conjunct of `MaskFamilyCode.Prepared`, `pos ≤ rewindCap`, with
`rewindCap := caps.descriptorReserve`. -/
theorem descriptor_fits {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps) :
    (CachedFamilyLoader.descriptorWord printer
        (dataList a (r.family a) (geometryOf selector a r) layout facts)).length
      ≤ caps.descriptorReserve :=
  good.2.2.2

/-- The raw reserve the loader's tail needs is likewise a clause of `Good`. -/
theorem raw_fits {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {r : Request}
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (good : RowCaps.Good selector a printer r layout facts caps) :
    (r.raw selector a).length ≤ caps.rawReserve :=
  good.2.2.1

end
end SLoad.Setup
