import Proof.MachineModel.OrdinarySourceSATLiftClear

/-! Paid printing and copying into the cleared query banks. The same
allocated zero log is reused; its full capacity remains part of the state. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
open LocalBitMultitape RepairOrdinary RecoveryRootRound
open private install_first from Proof.MachineModel.OrdinaryOracleComposeHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem install_pair {t : ℕ} (slot : Fin 2 → Fin t) (hi : Function.Injective slot)
    (ambient : Fin t → List Bool) (out : List Bool) :
    install slot ambient ![out,ambient (slot 1)] = Function.update ambient (slot 0) out := by
  classical
  have h01 : slot 0 ≠ slot 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hi h)
  funext i
  by_cases h0 : i = slot 0
  · subst i; simp [install_slot slot hi]
  by_cases h1 : i = slot 1
  · subst i; simp [install_slot slot hi,h01.symm]
  rw [install_other slot ambient _ i (by intro j; fin_cases j <;> exact Ne.symm (by assumption))]
  simp [Function.update,h0]

theorem printer_run (k : Fin 4) (cap : ℕ) (ambient : Fin 156 → List Bool)
    (hc : 3 ≤ cap) (hw : ambient (oneSlot k) = List.replicate cap false)
    (hl : ambient 155 = List.replicate cap false) :
    ClockJoin.ReadyRun (RecoveryFocus.machine (printerSlots k)
      (HierarchyFixedWord.machine (frame [true]))) 8 ambient
      (Function.update ambient (oneSlot k) (ZeroPadding.pad cap (frame [true]))) := by
  classical
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (frame [true])
  have hbase : ClockJoin.ReadyRun (HierarchyFixedWord.machine (frame [true])) 8 (fun _ => [])
      ![frame [true],List.replicate 3 false] := ⟨r,hr,ht,hh,hs.le⟩
  have hpad := PCPPairReusable.padded_ready _ _ _ hbase (fun _ => cap)
  have hout : (fun i : Fin 2 => ZeroPadding.pad cap (![frame [true],List.replicate 3 false] i)) =
      ![ZeroPadding.pad cap (frame [true]),List.replicate cap false] := by
    funext i
    fin_cases i
    · rfl
    · change ZeroPadding.pad cap (List.replicate 3 false) = List.replicate cap false
      simp only [ZeroPadding.pad,List.length_replicate,← List.replicate_add]
      congr 1
      omega
  rw [hout] at hpad
  have hfocus := hpad.focus (printerSlots k) (printer_injective k) ambient (by
    intro j; fin_cases j <;> simpa [printerSlots,ZeroPadding.pad] using (by assumption))
  have he : install (printerSlots k) ambient
      ![ZeroPadding.pad cap (frame [true]),List.replicate cap false] =
      Function.update ambient (oneSlot k) (ZeroPadding.pad cap (frame [true])) := by
    rw [← hl]
    exact install_pair _ (printer_injective k) ambient _
  rw [he] at hfocus
  exact hfocus

theorem copy_run (cap : ℕ) (bits padding : List Bool) (ambient : Fin 156 → List Bool)
    (hc : (frame bits).length ≤ cap) (hs : ambient 0 = frame bits ++ padding)
    (hb : ambient (bank 0 3) = List.replicate cap false)
    (hl : ambient 155 = List.replicate cap false) :
    ClockJoin.ReadyRun (call 5).2 (4*bits.length+4) ambient
      (Function.update ambient (bank 0 3) (ZeroPadding.pad cap (frame bits))) := by
  classical
  have hc' : 2*bits.length+1 ≤ cap := by simpa using hc
  have h := (PCPFieldMoves.ready_run bits padding cap cap).focus queryCopySlots copy_injective ambient (by
    intro j; fin_cases j <;> simpa [queryCopySlots] using (by assumption))
  have hout : PCPFieldMoves.output [] bits padding cap cap =
      ![ambient 0,ZeroPadding.pad cap (frame bits),ambient 155] := by
    funext j; fin_cases j <;> simp [PCPFieldMoves.output,hs,hl,max_eq_left hc']
  rw [hout] at h
  have he : install queryCopySlots ambient ![ambient 0,ZeroPadding.pad cap (frame bits),ambient 155] =
      Function.update ambient (bank 0 3) (ZeroPadding.pad cap (frame bits)) := by
    have hi := install_first queryCopySlots copy_injective ambient
      (ZeroPadding.pad cap (frame bits)) (ambient 155)
    change install queryCopySlots ambient ![ambient 0,ZeroPadding.pad cap (frame bits),ambient 155] = Function.update
      (Function.update ambient (bank 0 3) (ZeroPadding.pad cap (frame bits))) 155 (ambient 155) at hi
    rw [hi]
    apply Function.update_eq_self_iff.mpr
    simp [Function.update,bank]
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hsteps⟩ := h
  exact ⟨r,hr,ht,hh,hsteps.le⟩

theorem updated_bounded (cap : ℕ) (ambient : Fin 156 → List Bool)
    (i : Fin 156) (bits : List Bool) (ha : Bounded cap ambient) (hb : bits.length ≤ cap) :
    Bounded cap (Function.update ambient i bits) := by
  classical
  intro j hj
  by_cases h : j = i
  · subst j; simpa using hb
  · simpa [Function.update,h] using ha j hj

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Kernel
