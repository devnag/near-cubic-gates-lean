import Proof.PCP.PCPTraversalResult

/-! Ambient-cursor transport for actual calls in the fixed traversal. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def installedHeads {t : ℕ} (slot : Fin t → Fin 128)
    (ambient : Fin 128 → ℕ) (localHeads : Fin t → ℕ) : Fin 128 → ℕ :=
  fun i => match RecoveryFocus.pick slot i with
    | some j => localHeads j
    | none => ambient i

theorem installedHeads_existing {t : ℕ} (slot : Fin t → Fin 128)
    (ambient : Fin 128 → ℕ) (localHeads : Fin t → ℕ)
    (hh : ∀ j,ambient (slot j)=localHeads j) : installedHeads slot ambient localHeads=ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp only [installedHeads,hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simpa only [installedHeads,hp] using (hh j).symm.trans (congrArg ambient he)

theorem focused_run_at {t s fuel : ℕ} (p : Machine t s)
    (slot : Fin t → Fin 128) (hi : Function.Injective slot)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (source : Configuration t s) (base : ExecutionReceipt t s)
    (hr : runFrom p fuel source=some base) (hq : source.control=p.start)
    (hh : ∀ j,heads (slot j)=source.heads j)
    (ht : ∀ j,ambient (slot j)=source.tapes j) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) fuel ⟨p.start,heads,ambient⟩=some r ∧
      r.final.control=base.final.control ∧
      r.final.heads=installedHeads slot heads base.final.heads ∧
      r.final.tapes=install slot ambient base.final.tapes ∧ r.steps=base.steps := by
  obtain ⟨r,hrun,hf,hs⟩ := RecoveryFocus.run_config slot hi p heads ambient fuel source base hr
  have he : RecoveryFocus.config slot heads ambient source=
      (⟨p.start,heads,ambient⟩ : Configuration 128 s) := by
    apply configuration_ext
    · exact hq
    · exact installedHeads_existing slot heads source.heads hh
    · exact install_existing slot ambient source.tapes ht
  rw [he] at hrun
  exact ⟨r,hrun,by rw [hf]; rfl,by rw [hf]; rfl,by rw [hf]; rfl,hs⟩

theorem packed_moving_path (j k : Fin 39) (p : Packed) (hp : call j=p)
    (fuel : ℕ) (beforeHeads afterHeads : Fin 128 → ℕ)
    (ambient out : Fin 128 → List Bool)
    (hrun : ∃ r,runFrom p.2 fuel ⟨p.2.start,beforeHeads,ambient⟩=some r ∧
      r.final.heads=afterHeads ∧ r.final.tapes=out)
    (hn : ∀ q scanned,next j q scanned=some k) :
    Path j k (fuel+1) beforeHeads ambient afterHeads out := by
  subst p
  obtain ⟨r,hr,hh,ht⟩ := hrun
  obtain ⟨n,hbound,hpath⟩ := call_receipt sizes programs 37 next j k fuel
    (RecoveryCalls.restarted (programs j) beforeHeads ambient) r hr (hn _ _)
  rw [hh,ht] at hpath
  exact ⟨n,hbound,hpath⟩

def advanceSlots : Fin 3 → Fin 128 := ![0,84,90]
theorem advanceSlots_injective : Function.Injective advanceSlots := by decide

theorem advance_leaf_path (pre bits suffix : List Bool) (cap : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hsource : ambient 0=pre++frame bits++suffix)
    (hout : ambient 84=List.replicate cap false)
    (hlog : ambient 90=List.replicate cap false)
    (hhsource : heads 0=pre.length) (hhout : heads 84=0) (hhlog : heads 90=0) :
    Path 4 5 (4*bits.length+5) heads ambient
      (installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0])
      (install advanceSlots ambient (PCPFieldMoves.output pre bits suffix cap cap)) := by
  obtain ⟨base,hr,ht,hh,_⟩ := PCPFieldMoves.advance_run pre bits suffix cap cap
  obtain ⟨r,hrun,_,hrh,hrt,_⟩ := focused_run_at PCPFieldMoves.advanceMachine advanceSlots
    advanceSlots_injective heads ambient _ base hr rfl
    (by intro i; fin_cases i; exact hhsource; exact hhout; exact hhlog)
    (by intro i; fin_cases i
        · change ambient 0=ZeroPadding.pad 0 (pre++frame bits++suffix)
          simpa only [ZeroPadding.pad_zero] using hsource
        · exact hout
        · exact hlog)
  rw [hh] at hrh
  rw [ht] at hrt
  have h := packed_moving_path 4 5 (focused advanceSlots PCPFieldMoves.advanceMachine) rfl
    (4*bits.length+4) heads _ ambient _ ⟨r,hrun,hrh,hrt⟩
    (by intro q scanned; simp [next])
  exact h

end NearCubicWires.RepairOrdinary.PCPTraversal
