import Proof.PCP.ProjectionDimensionsInputABI

/-! One actual hierarchy→framed padded input→clock→dimension execution.
Every supplier starts from the preceding physical endpoint and blank work. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyPrefix
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (k p q : ℕ) := HierarchyFramedInput.tapes k+DimensionsFromInput.tapes p q
def old (k p q : ℕ) (i : Fin (HierarchyFramedInput.tapes k)) : Fin (tapes k p q) := i.castAdd (DimensionsFromInput.tapes p q)
def dimensionSlots (k p q : ℕ) : Fin (DimensionsFromInput.tapes p q) → Fin (tapes k p q) :=
  fun i => if i.val=12 then old k p q (HierarchyFramedInput.fresh k 0)
    else i.natAdd (HierarchyFramedInput.tapes k)
theorem old_injective (k p q : ℕ) : Function.Injective (old k p q) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes k p q) => i.val) h)
theorem dimension_injective (k p q : ℕ) : Function.Injective (dimensionSlots k p q) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  have hbound := (HierarchyFramedInput.fresh k 0).isLt
  dsimp [dimensionSlots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (k p q : ℕ) (x : List Bool) : Fin (tapes k p q) → List Bool :=
  fun i => if i.val=2 then frame x else []
noncomputable def hierarchyProgram (k CH Cpad p q : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (old k p q) (HierarchyFramedInput.machine k CH Cpad code)
noncomputable def dimensionProgram (k p q C : ℕ) :=
  RecoveryFocus.machine (dimensionSlots k p q) (DimensionsFromInput.machine p q C)
noncomputable def machine (k CH Cpad p q C : ℕ) (code : List Bool) :=
  Composition.machine (hierarchyProgram k CH Cpad p q code) (dimensionProgram k p q C)
def budget (k CH Cpad p q C : ℕ) (code x : List Bool) :=
  HierarchyFramedInput.budget k CH Cpad code x+1+
    DimensionsFromInput.budget p q C (HierarchyPadding.rawInput k CH Cpad code x)

theorem prefix_run (k CH Cpad : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad)
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) : ∃ out,
    ClockJoin.ReadyRun (machine k CH Cpad source.degrees.proofLog source.degrees.queries source.coefficient code)
      (budget k CH Cpad source.degrees.proofLog source.degrees.queries source.coefficient code x)
      (input k source.degrees.proofLog source.degrees.queries x) out ∧
      out (old k source.degrees.proofLog source.degrees.queries
        (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))=frame x ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.old source.degrees.proofLog source.degrees.queries 12))=
          frame (HierarchyPadding.rawInput k CH Cpad code x) ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.old source.degrees.proofLog source.degrees.queries 29))=
          frame (UWhole.time (HierarchyPadding.rawInput k CH Cpad code x).length).bits ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries))=
          List.replicate (Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length) true ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.bitsR source.degrees.proofLog source.degrees.queries))=
          frame (Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length).bits ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.rawQ source.degrees.proofLog source.degrees.queries))=
          List.replicate (Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length) true ∧
      out (dimensionSlots k source.degrees.proofLog source.degrees.queries
        (DimensionsFromInput.bitsQ source.degrees.proofLog source.degrees.queries))=
          frame (Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length).bits := by
  let p := source.degrees.proofLog
  let q := source.degrees.queries
  let y := HierarchyPadding.rawInput k CH Cpad code x
  obtain ⟨hout,hh,hy,hx⟩ := HierarchyFramedInput.framed_run k CH Cpad code x hpad
  have hhierarchy := hh.focus (old k p q) (old_injective k p q) (input k p q x) (by intro i; rfl)
  let middle := install (old k p q) (input k p q x) hout
  have hi : ∀ i,middle (dimensionSlots k p q i)=DimensionsFromInput.input p q y i := by
    intro i
    rw [DimensionsFromInput.input_eq]
    change middle (dimensionSlots k p q i) = if i.val=12 then frame y else []
    by_cases hi : i.val=12
    · simp only [hi,dimensionSlots]
      change install (old k p q) (input k p q x) hout (old k p q (HierarchyFramedInput.fresh k 0))=_
      rw [install_slot _ (old_injective k p q)]
      exact hy
    · rw [if_neg hi]
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp only [dimensionSlots,hi,if_false,old,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      have ht : 3 ≤ HierarchyFramedInput.tapes k := by
        have hb := HierarchyReduction.base_lower k
        dsimp [HierarchyFramedInput.tapes,HierarchyReduction.tapes]; omega
      simp [input,dimensionSlots,hi,show HierarchyFramedInput.tapes k+i.val≠2 by omega]
  obtain ⟨dout,hd,hy',ht,hR,hbitsR,hQ,hbitsQ⟩ := DimensionsFromInput.source_run source y
  have hdim := hd.focus (dimensionSlots k p q) (dimension_injective k p q) middle hi
  have ho (i : Fin (DimensionsFromInput.tapes p q)) :
      install (dimensionSlots k p q) middle dout (dimensionSlots k p q i)=dout i :=
    install_slot _ (dimension_injective k p q) _ _ i
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hhierarchy hdim,?_,
    (ho _).trans hy',(ho _).trans ht,(ho _).trans hR,(ho _).trans hbitsR,(ho _).trans hQ,(ho _).trans hbitsQ⟩
  rw [install_other _ _ _ _ (by
    intro i hi; have hv := congrArg Fin.val hi
    have hb := HierarchyReduction.base_lower k
    dsimp [dimensionSlots,old] at hv
    split_ifs at hv
    · simp [HierarchyFramedInput.fresh,HierarchyFramedInput.old,HierarchyReduction.xTape,
        HierarchyReduction.low,HierarchyFromInput.field,HierarchyReduction.tapes] at hv
    · have hxbound := (HierarchyFramedInput.old k (HierarchyReduction.xTape k)).isLt
      dsimp at hv
      omega)]
  change install (old k p q) (input k p q x) hout (old k p q (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))=_
  rw [install_slot _ (old_injective k p q)]
  exact hx

end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyPrefix
