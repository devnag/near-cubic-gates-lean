import Proof.Hierarchy.CompetitorThresholdAmbient

/-! The computed accumulator and the physically printed fixed constants
are wired into the literal rational comparison after the paid native clear.
The retained zero padding differs between accumulated and fresh fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decisionSlots (lower : Bool) (i : Fin 67) : Fin 110 :=
  if h : i.val<7 then
    (if lower then ![0,1,96,101,4,106,6] else ![96,101,0,1,106,4,6]) ⟨i.val,h⟩
  else ⟨i.val,by omega⟩
def pads (lower : Bool) (b : ℕ) (i : Fin 67) :=
  if 95 ≤ (decisionSlots lower i).val ∨ i.val=6 then 0 else capacity b
noncomputable def decisionProgram (lower : Bool) :=
  RecoveryFocus.machine (decisionSlots lower) CompetitorRationalDecision.machine

theorem decision_injective (lower : Bool) : Function.Injective (decisionSlots lower) := by
  cases lower <;> decide

theorem decision_input (lower : Bool) (b : ℕ) (q : ℚ) (a : CompetitorValidity.Estimate)
    (source : List Bool) (ambient : Fin 110 → List Bool)
    (hstore : Store b a source (project ambient))
    (hqnum : ambient 96=frame (binary (width b) (CompetitorThresholdDecision.numerator q)))
    (hqzero : ambient 101=frame (binary (width b) 0))
    (hqden : ambient 106=frame (binary b q.den)) (i : Fin 67) :
    cleaned b ambient (decisionSlots lower i)=
      CompetitorMixedThreshold.input lower b a.positive a.negative a.denominator q (pads lower b) i := by
  have h0 : cleaned b ambient 0=ZeroPadding.pad (capacity b) (frame (binary (width b) a.positive)) := by
    exact (cleaned_native b ambient 0).trans
      ((clear_keep _ _ _ 0 (fun j => (work_range j).2.1)).trans hstore.positive)
  have h1 : cleaned b ambient 1=ZeroPadding.pad (capacity b) (frame (binary (width b) a.negative)) := by
    exact (cleaned_native b ambient 1).trans
      ((clear_keep _ _ _ 1 (fun j => (work_range j).2.2.1)).trans hstore.negative)
  have h4 : cleaned b ambient 4=ZeroPadding.pad (capacity b) (frame (binary b a.denominator)) := by
    exact (cleaned_native b ambient 4).trans
      ((clear_keep _ _ _ 4 (fun j => (work_range j).2.2.2.1)).trans hstore.denominator)
  have h6 : cleaned b ambient 6=List.replicate (width b) true := by
    exact (cleaned_native b ambient 6).trans
      ((clear_keep _ _ _ 6 (fun j => (work_range j).2.2.2.2.1)).trans hstore.wideWidth)
  have h96 := (cleaned_other b ambient 96 (by decide)).trans hqnum
  have h101 := (cleaned_other b ambient 101 (by decide)).trans hqzero
  have h106 := (cleaned_other b ambient 106 (by decide)).trans hqden
  have hz (j : Fin 67) (hj : 7 ≤ j.val) :
      cleaned b ambient ⟨j.val,by omega⟩=ZeroPadding.pad (capacity b) [] := by
    have hi : ∃ k,workSlot k=(⟨j.val,by omega⟩ : Fin 94) := by
      exact work_image ⟨j.val,by omega⟩ (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
        (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
    exact (cleaned_native b ambient ⟨j.val,by omega⟩).trans ((clear_cell _ _ _ _ hi).trans (by simp [ZeroPadding.pad]))
  by_cases hi : i.val<7
  · have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by
      simp only [Fin.ext_iff]
      omega
    rcases hc with hc | hc | hc | hc | hc | hc | hc <;> subst i <;> cases lower
    · change cleaned b ambient 96=ZeroPadding.pad 0 (frame (binary (width b) (CompetitorThresholdDecision.numerator q)))
      rw [ZeroPadding.pad_zero]
      exact h96
    · exact h0
    · change cleaned b ambient 101=ZeroPadding.pad 0 (frame (binary (width b) 0))
      rw [ZeroPadding.pad_zero]
      exact h101
    · exact h1
    · exact h0
    · change cleaned b ambient 96=ZeroPadding.pad 0 (frame (binary (width b) (CompetitorThresholdDecision.numerator q)))
      rw [ZeroPadding.pad_zero]
      exact h96
    · exact h1
    · change cleaned b ambient 101=ZeroPadding.pad 0 (frame (binary (width b) 0))
      rw [ZeroPadding.pad_zero]
      exact h101
    · change cleaned b ambient 106=ZeroPadding.pad 0 (frame (binary b q.den))
      rw [ZeroPadding.pad_zero]
      exact h106
    · exact h4
    · exact h4
    · change cleaned b ambient 106=ZeroPadding.pad 0 (frame (binary b q.den))
      rw [ZeroPadding.pad_zero]
      exact h106
    · change cleaned b ambient 6=ZeroPadding.pad 0 (List.replicate (width b) true)
      rw [ZeroPadding.pad_zero]
      exact h6
    · change cleaned b ambient 6=ZeroPadding.pad 0 (List.replicate (width b) true)
      rw [ZeroPadding.pad_zero]
      exact h6
  · have hslot : decisionSlots lower i=⟨i.val,by omega⟩ := by simp [decisionSlots,hi]
    have hpads : pads lower b i=capacity b := by
      simp [pads,hslot,show ¬95 ≤ i.val by omega,show i.val≠6 by omega]
    have hraw : CompetitorThresholdDecision.input lower b a.positive a.negative a.denominator q i=[] := by
      simp [CompetitorThresholdDecision.input,CompetitorRationalProducts.input,
        show ¬i.val<4 by omega,show i.val≠4 by omega,show i.val≠5 by omega,show i.val≠6 by omega]
    rw [CompetitorMixedThreshold.input,hpads,hraw,hslot]
    exact hz i (by omega)

theorem decision_run (lower : Bool) (b pos : ℕ) (q : ℚ) (a : CompetitorValidity.Estimate)
    (source : List Bool) (hs : Fin 110 → ℕ) (ambient : Fin 110 → List Bool)
    (hstore : Store b a source (project ambient))
    (hheads : ∀ i,hs (native i)=heads pos i)
    (hfreshHeads : ∀ i : Fin 110,95 ≤ i.val → hs i=0)
    (hnum : ambient 96=frame (binary (width b) (CompetitorThresholdDecision.numerator q)))
    (hzero : ambient 101=frame (binary (width b) 0)) (hden : ambient 106=frame (binary b q.den))
    (ha : a.Valid b) (hq : 0≤q)
    (hqnum : CompetitorThresholdDecision.numerator q<2^b) (hqden : q.den<2^b) :
    ∃ r,runFrom (decisionProgram lower) (2000*(b+1)^2)
        (RecoveryCalls.restarted (decisionProgram lower) hs (cleaned b ambient))=some r ∧
      r.steps≤2000*(b+1)^2 ∧ r.final.heads=hs ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔
        CompetitorThresholdDecision.passes lower a.positive a.negative a.denominator q) := by
  obtain ⟨out,hr,hflag⟩ := CompetitorMixedThreshold.threshold_run lower b a.positive a.negative a.denominator q
    (pads lower b) ha.positive ha.negative ha.denominator ha.denominatorPositive hq hqnum hqden
  have hh : ∀ i,hs (decisionSlots lower i)=0 := by
    intro i
    by_cases hi : i.val<7
    · have h0 : hs 0=0 := hheads 0
      have h1 : hs 1=0 := hheads 1
      have h4 : hs 4=0 := hheads 4
      have h6 : hs 6=0 := hheads 6
      have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by
        simp only [Fin.ext_iff]
        omega
      rcases hc with hc | hc | hc | hc | hc | hc | hc <;> subst i <;> cases lower
      all_goals first | exact h0 | exact h1 | exact h4 | exact h6 | exact hfreshHeads _ (by decide)
    · have hslot : decisionSlots lower i=native ⟨i.val,by omega⟩ := by simp [decisionSlots,hi,native]
      rw [hslot,hheads]
      simp [heads,show i.val≠88 by omega]
  obtain ⟨r,hrun,hrh,hrt,hrs⟩ := bounded_focused_run (decisionSlots lower) (decision_injective lower) _ _ _ hr
    hs (cleaned b ambient) hh (decision_input lower b q a source ambient hstore hnum hzero hden)
  refine ⟨r,hrun,hrs,hrh,?_⟩
  have ht65 : r.final.tapes 65=out 65 := by
    rw [hrt]
    exact install_slot (decisionSlots lower) (decision_injective lower) _ _ 65
  simpa only [ht65] using hflag

end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
