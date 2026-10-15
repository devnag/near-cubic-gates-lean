import Proof.MachineModel.OrdinarySourceSATLiftMoves

/-! The enclosing physical query-kernel prefix: erase, four constant
prints and a preserved-source query copy. All inputs to the pair bank are
now produced by actual calls inside the same fixed controller. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def printed (cap : ℕ) (source : List Bool) : Fin 156 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (cleared cap source)
    (oneSlot 0) (ZeroPadding.pad cap (frame [true]))) (oneSlot 1) (ZeroPadding.pad cap (frame [true])))
    (oneSlot 2) (ZeroPadding.pad cap (frame [true]))) (oneSlot 3) (ZeroPadding.pad cap (frame [true]))

noncomputable def prepared (cap : ℕ) (source bits : List Bool) : Fin 156 → List Bool :=
  Function.update (printed cap source) (bank 0 3) (ZeroPadding.pad cap (frame bits))

theorem prepared_source (cap : ℕ) (source bits : List Bool) : prepared cap source bits 0 = source := by
  simp [prepared,printed,cleared,Function.update,oneSlot,bank]
theorem prepared_driver (cap : ℕ) (source bits : List Bool) :
    prepared cap source bits 1 = List.replicate cap true := by
  simp [prepared,printed,cleared,Function.update,oneSlot,bank]
theorem prepared_log (cap : ℕ) (source bits : List Bool) :
    prepared cap source bits 2 = List.replicate (cap+1) false := by
  simp [prepared,printed,cleared,Function.update,oneSlot,bank]

theorem prepare_path (cap log : ℕ) (ambient : Fin 156 → List Bool) (bits padding : List Bool)
    (hb : Bounded cap ambient) (hd : ambient 1 = List.replicate cap true)
    (hl : ambient 2 = List.replicate log false) (hz : log ≤ cap+1)
    (hc : 3 ≤ cap) (hw : (frame bits).length ≤ cap)
    (hsource : ambient 0 = frame bits ++ padding) :
    Path 0 6 (2*cap+4*bits.length+46) ambient (prepared cap (ambient 0) bits) := by
  classical
  let a := cleared cap (ambient 0)
  let b := Function.update a (oneSlot 0) (ZeroPadding.pad cap (frame [true]))
  let c := Function.update b (oneSlot 1) (ZeroPadding.pad cap (frame [true]))
  let d := Function.update c (oneSlot 2) (ZeroPadding.pad cap (frame [true]))
  let e := Function.update d (oneSlot 3) (ZeroPadding.pad cap (frame [true]))
  have hclear : ClockJoin.ReadyRun (call 0).2 (2*cap+4) ambient a := by
    obtain ⟨r,hr,ht,hh,hs⟩ := clear_run cap log ambient hb hd hl hz
    exact ⟨r,hr,ht,hh,hs.le⟩
  have h0 := ready_path 0 1 (call 0) rfl _ ambient a hclear (by intro q scanned; rfl)
  have p1 := printer_run 0 cap a hc
    (by simp [a,cleared,oneSlot,bank]) (by simp [a,cleared])
  have h1 := ready_path 1 2 _ rfl 8 a b p1 (by intro q scanned; rfl)
  have p2 := printer_run 1 cap b hc
    (by simp [b,a,cleared,oneSlot,bank])
    (by simp [b,a,cleared,oneSlot,bank])
  have h2 := ready_path 2 3 _ rfl 8 b c p2 (by intro q scanned; rfl)
  have p3 := printer_run 2 cap c hc
    (by simp [c,b,a,cleared,Function.update,oneSlot,bank])
    (by simp [c,b,a,cleared,Function.update,oneSlot,bank])
  have h3 := ready_path 3 4 _ rfl 8 c d p3 (by intro q scanned; rfl)
  have p4 := printer_run 3 cap d hc
    (by simp [d,c,b,a,cleared,Function.update,oneSlot,bank])
    (by simp [d,c,b,a,cleared,Function.update,oneSlot,bank])
  have h4 := ready_path 4 5 _ rfl 8 d e p4 (by intro q scanned; rfl)
  have cp := copy_run cap bits padding e hw
    (by simpa [e,d,c,b,a,cleared,Function.update,oneSlot,bank] using hsource)
    (by simp [e,d,c,b,a,cleared,Function.update,oneSlot,bank])
    (by simp [e,d,c,b,a,cleared,Function.update,oneSlot,bank])
  have h5 := ready_path 5 6 (call 5) rfl (4*bits.length+4) e _ cp (by intro q scanned; rfl)
  have whole := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  convert whole using 1 <;> first | rfl | omega

theorem prepared_bounded (cap : ℕ) (source bits : List Bool)
    (hc : 3 ≤ cap) (hw : (frame bits).length ≤ cap) : Bounded cap (prepared cap source bits) := by
  classical
  have h1 : (ZeroPadding.pad cap (frame [true])).length ≤ cap := by
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl hc
  have h2 : (ZeroPadding.pad cap (frame bits)).length ≤ cap := by
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl hw
  exact updated_bounded _ _ _ _
    (updated_bounded _ _ _ _ (updated_bounded _ _ _ _ (updated_bounded _ _ _ _
      (updated_bounded _ _ _ _ (cleared_bounded cap source) h1) h1) h1) h1) h2

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
