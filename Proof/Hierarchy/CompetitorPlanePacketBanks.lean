import Proof.Hierarchy.CompetitorPlanePacketPass

/-! Fixed tape-label permutation for the second packet in each positive/
negative pair. The output bank of the first call is the actual input bank
of the second call; this compiles different labels and moves no tape data. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketBanks
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream CompetitorPlanePacketPass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 34 ≃ Fin 34 := Equiv.swap 17 19
def nativeLayout : Fin 30 ≃ Fin 30 := Equiv.swap 17 19
def exchanged (ambient : Fin 34 → List Bool) : Fin 34 → List Bool := ambient ∘ layout
noncomputable def machine := TapeRenaming.machine layout CompetitorPlanePacketPass.machine
def nextCells (sign : Bool) (bits : List Bool) (xs : List Cell) := xs.map (fun a =>
  (⟨a.count,CompetitorPlane.nextPositive sign a.positive a.count bits,
    CompetitorPlane.nextNegative sign a.negative a.count bits⟩ : Cell))

@[simp] theorem next_length (sign : Bool) (bits : List Bool) (xs : List Cell) :
    (nextCells sign bits xs).length=xs.length := by simp [nextCells]
theorem next_word (sign : Bool) (w : ℕ) (bits : List Bool) (xs : List Cell) :
    oldWords w (nextCells sign bits xs)=newWords sign w bits xs := by
  simp only [oldWords,newWords,nextCells,List.flatMap_map]
  rfl
theorem layout_symm : (layout.symm : Fin 34 → Fin 34)=layout := rfl
theorem layout_native (i : Fin 30) : layout (localTape i)=localTape (nativeLayout i) := by
  fin_cases i <;> decide
theorem layout_keep (i : Fin 34) (h17 : i≠17) (h19 : i≠19) : layout i=i :=
  Equiv.swap_apply_of_ne_of_ne h17 h19
theorem exchanged_keep (ambient : Fin 34 → List Bool) (i : Fin 34) (h17 : i≠17) (h19 : i≠19) :
    exchanged ambient i=ambient i := by simp only [exchanged,Function.comp_apply,layout_keep i h17 h19]
theorem layout_source (i : Fin 34) : layout.symm i=32 ↔ i=32 := by
  have hfix : layout 32=32 := by decide
  constructor
  · intro h
    have he := congrArg layout h
    simpa only [Equiv.apply_symm_apply,hfix] using he
  · intro h
    subst i
    decide

theorem context_exchange (b w : ℕ) (xs ys : List Cell) (ambient : Fin 34 → List Bool)
    (h : Context b w xs ambient) (hlen : ys.length=xs.length)
    (hout : ambient 17=ZeroPadding.pad (capacity w xs.length) (oldWords w ys)) :
    Context b w ys (exchanged ambient) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [exchanged,Function.comp_apply,layout,Equiv.swap_apply_right,hlen] using hout
  · simpa only [exchanged_keep ambient 9 (by decide) (by decide),hlen] using h.width
  · simpa only [exchanged_keep ambient 20 (by decide) (by decide),hlen] using h.nativeWidth
  · simpa only [exchanged_keep ambient 21 (by decide) (by decide),hlen] using h.erase
  · simpa only [exchanged_keep ambient 27 (by decide) (by decide),hlen] using h.count
  · simpa only [exchanged_keep ambient 33 (by decide) (by decide),CompetitorPlanePaddedEntry.count_length,hlen] using h.byteCount
  · simpa only [exchanged_keep ambient 30 (by decide) (by decide),hlen] using h.driver
  · simpa only [exchanged_keep ambient 31 (by decide) (by decide),hlen] using h.reset
  · intro i
    simpa only [exchanged,Function.comp_apply,layout_native,hlen] using h.support (nativeLayout i)

theorem renamed_entry {s : ℕ} (q : Fin s) (pos : ℕ) (ambient : Fin 34 → List Bool) :
    TapeRenaming.config layout (CompetitorPlanePacketDock.cfg q pos (exchanged ambient))=
      CompetitorPlanePacketDock.cfg q pos ambient := by
  apply configuration_ext
  · rfl
  · funext i
    change CompetitorPlanePacketDock.heads pos (layout.symm i)=CompetitorPlanePacketDock.heads pos i
    simp only [CompetitorPlanePacketDock.heads,layout_source]
  · funext i
    simp [TapeRenaming.config,CompetitorPlanePacketDock.cfg,exchanged]

theorem reversed_pass_run (pre suffix bits : List Bool) (sign : Bool) (b w : ℕ) (xs : List Cell)
    (ambient : Fin 34 → List Bool) (h : Context b w xs (exchanged ambient))
    (hsource : ambient 32=pre++CompetitorPlanePacketLoad.packet sign bits (countWords b xs)++suffix)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ r,runFrom machine (CompetitorPlanePacketPass.budget b w bits xs)
      (CompetitorPlanePacketDock.cfg machine.start pre.length ambient)=some r ∧
      r.final.heads=CompetitorPlanePacketDock.heads
        (pre.length+(CompetitorPlanePacketLoad.packet sign bits (countWords b xs)).length) ∧
      r.final.tapes 19=ZeroPadding.pad (capacity w xs.length) (newWords sign w bits xs) ∧
      r.final.tapes 32=ambient 32 ∧ Context b w (nextCells sign bits xs) r.final.tapes ∧
      r.steps≤CompetitorPlanePacketPass.budget b w bits xs := by
  have hsrc : exchanged ambient 32=pre++CompetitorPlanePacketLoad.packet sign bits (countWords b xs)++suffix :=
    (exchanged_keep ambient 32 (by decide) (by decide)).trans hsource
  obtain ⟨base,hr,hh,h17,h32,hcontext,hs⟩ := CompetitorPlanePacketPass.packet_pass_run pre suffix bits sign b w xs
    (exchanged ambient) h hsrc hb hbits hv
  have renamed := TapeRenaming.run_rename layout CompetitorPlanePacketPass.machine _ _ base hr
  rw [renamed_entry] at renamed
  let out := TapeRenaming.receipt layout base
  refine ⟨out,renamed,?_,?_,?_,?_,hs⟩
  · change base.final.heads ∘ layout.symm=_
    rw [hh]
    funext i
    simp only [CompetitorPlanePacketDock.heads,Function.comp_apply,layout_source]
  · change base.final.tapes (layout.symm 19)=_
    rw [show layout.symm 19=17 by decide]
    exact h17
  · change base.final.tapes (layout.symm 32)=_
    simpa only [layout_symm,layout_keep 32 (by decide) (by decide),
      exchanged_keep ambient 32 (by decide) (by decide)] using h32
  · have hc := context_exchange b w xs (nextCells sign bits xs) base.final.tapes hcontext
      (next_length sign bits xs) (by rw [next_word]; exact h17)
    simpa only [out,TapeRenaming.receipt,TapeRenaming.config,layout_symm,exchanged] using hc

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketBanks
