import Proof.PCP.ProjectionDimensions
import Proof.PCP.ProjectionDimensionCanonical

/-! The dimension program consumes the actual input-driven clock endpoint.
All dimension scratch starts blank; framed input and binary T remain intact. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
open LocalBitMultitape RepairOrdinary RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p q : ℕ) := 34+DimensionProducer.tapes p q
def old (p q : ℕ) (i : Fin 34) : Fin (tapes p q) := i.castAdd (DimensionProducer.tapes p q)
def dimensionSlots (p q : ℕ) : Fin (DimensionProducer.tapes p q) → Fin (tapes p q) :=
  fun i => if i.val=0 then old p q 27
    else ⟨34+(i.val-1),by dsimp [tapes]; have := i.isLt; omega⟩
theorem old_injective (p q : ℕ) : Function.Injective (old p q) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes p q) => i.val) h)
theorem dimension_injective (p q : ℕ) : Function.Injective (dimensionSlots p q) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [dimensionSlots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (p q : ℕ) (bits : List Bool) : Fin (tapes p q) → List Bool :=
  Fin.addCases (motive := fun _ : Fin (34+DimensionProducer.tapes p q) => List Bool)
    (ClockFromInput.input bits) (fun _ => [])
noncomputable def clockProgram (p q : ℕ) := RecoveryFocus.machine (old p q) (ClockTotal.machine 23 5)
noncomputable def dimensionProgram (p q C : ℕ) := RecoveryFocus.machine (dimensionSlots p q) (DimensionProducer.machine p q C)
noncomputable def machine (p q C : ℕ) := Composition.machine (clockProgram p q) (dimensionProgram p q C)
def budget (p q C : ℕ) (bits : List Bool) := ClockTotal.budget 23 5 bits+1+
  DimensionProducer.budget p q C (ClockEnvelope.exponent 23 5 bits.length)
def rawR (p q : ℕ) := dimensionSlots p q (DimensionProducer.rawR p q)
def bitsR (p q : ℕ) := dimensionSlots p q (DimensionProducer.bitsR p q)
def rawQ (p q : ℕ) := dimensionSlots p q (DimensionProducer.rawQ p q)
def bitsQ (p q : ℕ) := dimensionSlots p q (DimensionProducer.bitsQ p q)

theorem input_run (p q C : ℕ) (hc : 0<C) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine p q C) (budget p q C bits) (input p q bits) out ∧
      out (old p q 12)=frame bits ∧
      out (old p q 29)=frame (UAggregateClock.time bits.length).bits ∧
      out (rawR p q)=List.replicate (DimensionProducer.R p C (ClockEnvelope.exponent 23 5 bits.length)) true ∧
      out (bitsR p q)=frame (DimensionProducer.R p C (ClockEnvelope.exponent 23 5 bits.length)).bits ∧
      out (rawQ p q)=List.replicate (DimensionProducer.Q p q C (ClockEnvelope.exponent 23 5 bits.length)) true ∧
      out (bitsQ p q)=frame (DimensionProducer.Q p q C (ClockEnvelope.exponent 23 5 bits.length)).bits := by
  let e := ClockEnvelope.exponent 23 5 bits.length
  obtain ⟨r,hr,ht,he,hx,hh,hs⟩ := ClockTotal.canonical_run 23 5 bits
  have hb : ClockJoin.ReadyRun (ClockTotal.machine 23 5) (ClockTotal.budget 23 5 bits)
      (ClockFromInput.input bits) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hclock := hb.focus (old p q) (old_injective p q) (input p q bits) (by intro i; simp [input,old])
  let middle := install (old p q) (input p q bits) r.final.tapes
  have hinput : ∀ i,middle (dimensionSlots p q i)=DimensionProducer.input p q e i := by
    intro i
    by_cases hi : i.val=0
    · have heq : i=⟨0,by simp [DimensionProducer.tapes,DimensionWidth.tapes,DimensionWidth.base,DimensionPolynomial.tapes]⟩ := Fin.ext hi
      subst i
      change install (old p q) (input p q bits) r.final.tapes (old p q 27)=_
      rw [install_slot _ (old_injective p q)]
      exact he
    · dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp only [dimensionSlots,hi,if_false,old,Fin.val_castAdd] at hv
        omega)]
      rw [DimensionProducer.input,if_neg hi]
      have hj : dimensionSlots p q i=(⟨i.val-1,by omega⟩ : Fin (DimensionProducer.tapes p q)).natAdd 34 := by
        apply Fin.ext
        simp [dimensionSlots,hi]
      rw [hj]
      simp only [input,Fin.addCases_right]
  obtain ⟨out,hd,hR,hbR,hQ,hbQ⟩ := DimensionProducer.dimensions_run p q C e hc
  have hdim := hd.focus (dimensionSlots p q) (dimension_injective p q) middle hinput
  have hRpos : 0<DimensionProducer.R p C e := by
    dsimp [DimensionProducer.R,DimensionWidth.amount,natBitLength]; omega
  have hQpos : 0<DimensionProducer.Q p q C e := by
    dsimp [DimensionProducer.Q,DimensionPolynomial.value]; positivity
  rw [DimensionProducer.binary_bits _ hRpos] at hbR
  rw [DimensionProducer.binary_bits _ hQpos] at hbQ
  have preserved (i : Fin 34) (hi : i.val≠27) :
      install (dimensionSlots p q) middle out (old p q i)=r.final.tapes i := by
    rw [install_other _ _ _ _ (by
      intro j hj; have hv := congrArg Fin.val hj
      dsimp [dimensionSlots,old] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    exact install_slot _ (old_injective p q) _ _ i
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hclock hdim,
    (preserved 12 (by decide)).trans hx,(preserved 29 (by decide)).trans ht,?_,?_,?_,?_⟩
  · rw [rawR,install_slot _ (dimension_injective p q)]; exact hR
  · rw [bitsR,install_slot _ (dimension_injective p q)]; exact hbR
  · rw [rawQ,install_slot _ (dimension_injective p q)]; exact hQ
  · rw [bitsQ,install_slot _ (dimension_injective p q)]; exact hbQ

theorem source_run (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (bits : List Bool) :
    ∃ out,ClockJoin.ReadyRun
      (machine source.degrees.proofLog source.degrees.queries source.coefficient)
      (budget source.degrees.proofLog source.degrees.queries source.coefficient bits)
      (input source.degrees.proofLog source.degrees.queries bits) out ∧
      out (old source.degrees.proofLog source.degrees.queries 12)=frame bits ∧
      out (old source.degrees.proofLog source.degrees.queries 29)=frame (UWhole.time bits.length).bits ∧
      out (rawR source.degrees.proofLog source.degrees.queries)=List.replicate (Dimensions.width source bits.length) true ∧
      out (bitsR source.degrees.proofLog source.degrees.queries)=frame (Dimensions.width source bits.length).bits ∧
      out (rawQ source.degrees.proofLog source.degrees.queries)=List.replicate (Dimensions.queries source bits.length) true ∧
      out (bitsQ source.degrees.proofLog source.degrees.queries)=frame (Dimensions.queries source bits.length).bits := by
  have hr : DimensionProducer.R source.degrees.proofLog source.coefficient (ClockEnvelope.exponent 23 5 bits.length)=
      Dimensions.width source bits.length := (DimensionDyadic.width_eq source bits.length).symm
  have hq : DimensionProducer.Q source.degrees.proofLog source.degrees.queries source.coefficient
      (ClockEnvelope.exponent 23 5 bits.length)=Dimensions.queries source bits.length := by
    unfold DimensionProducer.Q DimensionPolynomial.value
    rw [hr]
    rfl
  simpa only [hr,hq,UWhole.time] using input_run source.degrees.proofLog source.degrees.queries source.coefficient
    source.coefficientPositive bits

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionsFromInput
