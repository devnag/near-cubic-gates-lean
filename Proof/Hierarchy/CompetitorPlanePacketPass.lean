import Proof.Hierarchy.CompetitorPlanePacketDock

/-! The actual serialized packet is consumed by the reusable signed-plane
pass. Physical fields come from the paid packet dock; only the retained
matrix dimensions and old P/N bank are supplied at this boundary. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketPass
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding CompetitorPlaneStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 32) : Fin 34 := i.castAdd 2
def localTape (i : Fin 30) : Fin 34 := i.castAdd 4
def capacity := CompetitorPlaneReusable.capacity
structure Context (b w : ℕ) (xs : List Cell) (ambient : Fin 34 → List Bool) : Prop where
  old : ambient 19=ZeroPadding.pad (capacity w xs.length) (oldWords w xs)
  width : ambient 9=ZeroPadding.pad (capacity w xs.length) (List.replicate w true)
  nativeWidth : ambient 20=ZeroPadding.pad (capacity w xs.length) (List.replicate b true)
  erase : ambient 21=ZeroPadding.pad (capacity w xs.length) (List.replicate (CompetitorPlane.capacity w) true)
  count : ambient 27=ZeroPadding.pad (capacity w xs.length) (CompareMachine.word xs.length)
  byteCount : ambient 33=List.replicate (countWords b xs).length true
  driver : ambient 30=List.replicate (capacity w xs.length) true
  reset : ambient 31=List.replicate (capacity w xs.length+1) false
  support : ∀ i,(ambient (localTape i)).length≤capacity w xs.length
noncomputable def callProgram := RecoveryFocus.machine native CompetitorPlaneReusable.machine
noncomputable def machine := Composition.machine CompetitorPlanePacketDock.machine callProgram
def budget (b w : ℕ) (bits : List Bool) (xs : List Cell) :=
  CompetitorPlanePacketDock.budget (capacity w xs.length) bits (countWords b xs)+1+
    CompetitorPlaneReusable.budget w xs.length

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 34 => a.val) h)
theorem native_avoids (i : Fin 32) : native i≠32 ∧ native i≠33 := by
  constructor
  · intro h; have hv:=congrArg (fun a : Fin 34 => a.val) h; change i.val=32 at hv; omega
  · intro h; have hv:=congrArg (fun a : Fin 34 => a.val) h; change i.val=33 at hv; omega

theorem packet_pass_run (pre suffix bits : List Bool) (sign : Bool) (b w : ℕ) (xs : List Cell)
    (ambient : Fin 34 → List Bool) (h : Context b w xs ambient)
    (hsource : ambient 32=pre++CompetitorPlanePacketLoad.packet sign bits (countWords b xs)++suffix)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ r,runFrom machine (budget b w bits xs)
      (CompetitorPlanePacketDock.cfg machine.start pre.length ambient)=some r ∧
      r.final.heads=CompetitorPlanePacketDock.heads
        (pre.length+(CompetitorPlanePacketLoad.packet sign bits (countWords b xs)).length) ∧
      r.final.tapes 17=ZeroPadding.pad (capacity w xs.length) (newWords sign w bits xs) ∧
      r.final.tapes 32=ambient 32 ∧ Context b w xs r.final.tapes ∧ r.steps≤budget b w bits xs := by
  let D := capacity w xs.length
  have hf : 2*bits.length+1≤D := by
    have hh := CompetitorPlanePaddedEntry.input_support sign b w bits xs hb hbits 0
    change (frame bits).length≤D at hh
    simpa using hh
  have hc : (countWords b xs).length≤D := by
    exact CompetitorPlanePaddedEntry.input_support sign b w bits xs hb hbits 18
  have hsupp : ∀ j,(ambient (CompetitorPlanePacketDock.targets j)).length≤D := by
    intro j
    fin_cases j
    · exact h.support 29
    · exact h.support 0
    · exact h.support 18
    · exact h.support 1
  obtain ⟨dock,hdock,hdh,hd29,hd0,hd18,hd1,hdkeep,hds⟩ := CompetitorPlanePacketDock.dock_run pre suffix bits
    (countWords b xs) sign D ambient hsource h.byteCount h.driver h.reset hsupp hf hc
  let middle := fun i : Fin 32 => dock.final.tapes (native i)
  have hcompatible : CompetitorPlaneReusable.Compatible sign b w bits xs middle := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i hi
      fin_cases i <;> simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native] at hi
      all_goals change dock.final.tapes _=_
      all_goals first | exact hd0 | exact hd18 | exact hd29 | skip
      all_goals first
        | exact (hdkeep 9 (by decide) (by decide) (by decide) (by decide)).trans h.width
        | exact (hdkeep 19 (by decide) (by decide) (by decide) (by decide)).trans h.old
        | exact (hdkeep 20 (by decide) (by decide) (by decide) (by decide)).trans h.nativeWidth
        | exact (hdkeep 21 (by decide) (by decide) (by decide) (by decide)).trans h.erase
        | exact (hdkeep 27 (by decide) (by decide) (by decide) (by decide)).trans h.count
    · intro j
      have hbefore := h.support ⟨(CompetitorPlaneReusable.workSlot j).val,by fin_cases j <;> decide⟩
      fin_cases j
      · change (dock.final.tapes 1).length≤D
        rw [hd1]
        simp
      all_goals
        change (dock.final.tapes _).length≤D
        rw [hdkeep _ (by decide) (by decide) (by decide) (by decide)]
        exact hbefore
    · exact (hdkeep 30 (by decide) (by decide) (by decide) (by decide)).trans h.driver
    · exact (hdkeep 31 (by decide) (by decide) (by decide) (by decide)).trans h.reset
  obtain ⟨produced,ready,h17,hretain,hsupport,h30,h31⟩ := CompetitorPlaneReusable.reusable_plane_run
    sign b w bits xs middle hcompatible hb hbits hv
  obtain ⟨called,hcalled,hch,hct,hcs⟩ := CompetitorReusableDecision.bounded_focused_run native native_injective
    CompetitorPlaneReusable.machine _ _ ready dock.final.heads dock.final.tapes (by
      intro i
      rw [hdh]
      simp [CompetitorPlanePacketDock.heads, (native_avoids i).1]) (by intro i; rfl)
  have hcalled' : runFrom callProgram (CompetitorPlaneReusable.budget w xs.length)
      (Composition.restart dock.final callProgram.start)=some called := hcalled
  have joined := Composition.run_join CompetitorPlanePacketDock.machine callProgram _ _ _ dock called hdock hcalled'
  have hout (i : Fin 32) : called.final.tapes (native i)=produced i := by
    rw [hct]
    exact install_slot native native_injective _ _ i
  have hprotected (i : Fin 30) (hi : CompetitorPlaneReusable.retained (CompetitorPlaneReusable.native i)) :
      called.final.tapes (localTape i)=dock.final.tapes (localTape i) :=
    (hout (CompetitorPlaneReusable.native i)).trans (hretain i hi)
  have hkeep32 : called.final.tapes 32=ambient 32 := by
    rw [hct]
    exact (install_other native _ _ 32 (fun i => (native_avoids i).1)).trans
      (hdkeep 32 (by decide) (by decide) (by decide) (by decide))
  have hkeep33 : called.final.tapes 33=ambient 33 := by
    rw [hct]
    exact (install_other native _ _ 33 (fun i => (native_avoids i).2)).trans
      (hdkeep 33 (by decide) (by decide) (by decide) (by decide))
  refine ⟨Composition.joinedReceipt dock called,joined,?_,?_,hkeep32,?_,?_⟩
  · change called.final.heads=_
    exact hch.trans hdh
  · change called.final.tapes 17=_
    exact (hout 17).trans h17
  · change Context b w xs called.final.tapes
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (hprotected 19 (by simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native])).trans
        ((hdkeep 19 (by decide) (by decide) (by decide) (by decide)).trans h.old)
    · exact (hprotected 9 (by simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native])).trans
        ((hdkeep 9 (by decide) (by decide) (by decide) (by decide)).trans h.width)
    · exact (hprotected 20 (by simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native])).trans
        ((hdkeep 20 (by decide) (by decide) (by decide) (by decide)).trans h.nativeWidth)
    · exact (hprotected 21 (by simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native])).trans
        ((hdkeep 21 (by decide) (by decide) (by decide) (by decide)).trans h.erase)
    · exact (hprotected 27 (by simp [CompetitorPlaneReusable.retained,CompetitorPlaneReusable.native])).trans
        ((hdkeep 27 (by decide) (by decide) (by decide) (by decide)).trans h.count)
    · exact hkeep33.trans h.byteCount
    · exact (hout 30).trans (h30.trans hcompatible.driver)
    · exact (hout 31).trans (h31.trans hcompatible.reset)
    · intro i
      change (called.final.tapes (native (CompetitorPlaneReusable.native i))).length≤D
      rw [hout]
      exact (hsupport i).le
  · change dock.steps+1+called.steps≤budget b w bits xs
    unfold budget
    change dock.steps=CompetitorPlanePacketDock.budget (capacity w xs.length) bits (countWords b xs) at hds
    omega

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketPass
