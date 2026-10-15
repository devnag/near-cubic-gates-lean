import Proof.Hierarchy.CompetitorRationalNumerators

/-! One exact rational addition on the fixed global scalar width. Its actual
ordinary program pays for both cross-numerators, widening the denominator,
the denominator product, and restoring that product to the reusable width.
The small-width fit is a fold invariant, not a change to the source theorem. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalSum
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts CompetitorRationalDecision CompetitorRationalNumerators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (j : Fin 67) : Fin 88 := j.castAdd 21
def wideSlots : Fin 5 → Fin 88 := ![6,4,67,68,69]
def multiplySlots (j : Fin 14) : Fin 88 :=
  if j.val=0 then 5 else if j.val=8 then 67 else if j.val=9 then 6
  else ⟨70+j.val,by omega⟩
def cropSlots : Fin 5 → Fin 88 := ![84,73,85,86,87]
noncomputable def numeratorProgram := RecoveryFocus.machine nativeSlots CompetitorRationalDecision.machine
noncomputable def wideProgram := RecoveryFocus.machine wideSlots ClockNormalize.machine
noncomputable def multiplyProgram := RecoveryFocus.machine multiplySlots HierarchyMultiplyEntry.machine
noncomputable def cropProgram := RecoveryFocus.machine cropSlots ClockNormalize.machine
noncomputable def machine := Composition.machine numeratorProgram
  (Composition.machine wideProgram (Composition.machine multiplyProgram cropProgram))
def input (b : ℕ) (a c : CompetitorValidity.Estimate) : Fin 88 → List Bool := fun i =>
  if h : i.val<67 then CompetitorRationalProducts.input (width b) b (operands a c)
    a.denominator c.denominator ⟨i.val,h⟩
  else if i.val=84 then List.replicate b true else []
def time (b : ℕ) := 2000*(b+1)^2+1+((4*width b+4)+1+(128*(width b+1)*(b+1)+1+(4*b+4)))

theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  have hv := congrArg (fun k : Fin 88 => k.val) h
  exact Fin.ext hv

theorem native_input (b : ℕ) (a c : CompetitorValidity.Estimate) (j : Fin 67) :
    input b a c (nativeSlots j)=CompetitorRationalProducts.input (width b) b (operands a c)
      a.denominator c.denominator j := by
  simp only [input,nativeSlots,Fin.val_castAdd,j.isLt,↓reduceDIte]

theorem outside_native (ambient : Fin 88 → List Bool) (out : Fin 67 → List Bool)
    (i : Fin 88) (hi : 67 ≤ i.val) : install nativeSlots ambient out i=ambient i := by
  apply install_other
  intro j he
  have hv := congrArg Fin.val he
  simp only [nativeSlots,Fin.val_castAdd] at hv
  omega

theorem resize_prefix (b w x : ℕ) (h : b≤w) :
    ClockNormalize.resize b (binary w x)=binary b x := by
  induction b generalizing w x with
  | zero => rfl
  | succ b ih =>
    cases w with
    | zero => omega
    | succ w => simp only [binary,ClockNormalize.resize]; rw [ih w (x/2) (by omega)]

theorem time_bound (b : ℕ) : time b≤3000*(b+1)^2 := by
  unfold time width
  nlinarith

theorem rational_sum_run (b : ℕ) (a c : CompetitorValidity.Estimate)
    (ha : a.Valid b) (hc : c.Valid b) :
    ∃ out,ClockJoin.ReadyRun machine (3000*(b+1)^2) (input b a c) out ∧
      out 63=frame (binary (width b) (add a c).positive) ∧
      out 64=frame (binary (width b) (add a c).negative) ∧
      out 85=frame (binary b (add a c).denominator) ∧
      out 6=List.replicate (width b) true ∧ out 84=List.replicate b true := by
  have hn : ∀ i,operands a c i<2^b := by
    intro i
    fin_cases i
    · exact ha.positive
    · exact ha.negative
    · exact hc.negative
    · exact hc.positive
  obtain ⟨base,hbase,hshared,hpositive,hnegative⟩ :=
    numerators_run b (operands a c) a.denominator c.denominator hn ha.denominator hc.denominator
  let middle := install nativeSlots (input b a c) base
  have hm := bounded_focus nativeSlots native_injective _ _ _ hbase (input b a c) (native_input b a c)
  have hshared' (j : Fin 7) : middle (nativeSlots (shared j))=
      CompetitorRationalProducts.input (width b) b (operands a c) a.denominator c.denominator (shared j) :=
    (install_slot nativeSlots native_injective _ base (shared j)).trans (hshared j)
  have h4 : middle 4=frame (binary b a.denominator) := hshared' 4
  have h5 : middle 5=frame (binary b c.denominator) := hshared' 5
  have h6 : middle 6=List.replicate (width b) true := hshared' 6
  have h63 : middle 63=frame (binary (width b) (add a c).positive) :=
    (install_slot nativeSlots native_injective _ base 63).trans hpositive
  have h64 : middle 64=frame (binary (width b) (add a c).negative) :=
    (install_slot nativeSlots native_injective _ base 64).trans hnegative
  have hextra (i : Fin 88) (hi : 67 ≤ i.val) : middle i=
      if i.val=84 then List.replicate b true else [] := by
    change install nativeSlots (input b a c) base i=_
    rw [outside_native _ _ i hi]
    simp only [input,show ¬i.val<67 by omega,↓reduceDIte]
  obtain ⟨wide,hw,hw0,_,hw2,_,_,hwh,hws⟩ := ClockScalarFields.scalar_run (width b)
    (binary b a.denominator) (by simp only [binary_length,width]; omega)
  have wideReady : ClockJoin.ReadyRun ClockNormalize.machine (4*width b+4)
      (ClockNormalize.input (width b) (binary b a.denominator)) wide.final.tapes :=
    ⟨wide,hw,rfl,hwh,hws.le⟩
  have wideInput : ∀ j,middle (wideSlots j)=ClockNormalize.input (width b) (binary b a.denominator) j := by
    intro j
    fin_cases j
    · exact h6
    · exact h4
    · exact hextra 67 (by decide)
    · exact hextra 68 (by decide)
    · exact hextra 69 (by decide)
  let widened := install wideSlots middle wide.final.tapes
  have hwide := bounded_focus wideSlots (by decide) _ _ _ wideReady middle wideInput
  have wd : widened 67=frame (binary (width b) a.denominator) := by
    change install wideSlots middle wide.final.tapes (wideSlots 2)=_
    simpa only [binary_value b a.denominator ha.denominator] using
      (install_slot wideSlots (by decide) middle wide.final.tapes 2).trans hw2
  have we : widened 5=frame (binary b c.denominator) :=
    (install_other wideSlots _ _ 5 (by decide)).trans h5
  have ww : widened 6=List.replicate (width b) true :=
    (install_slot wideSlots (by decide) _ wide.final.tapes 0).trans hw0
  have wextra (i : Fin 88) (hi : 70 ≤ i.val) : widened i=
      if i.val=84 then List.replicate b true else [] := by
    have hnone : ∀ j,wideSlots j≠i := by
      intro j he
      have hv := congrArg Fin.val he
      fin_cases j <;> simp [wideSlots] at hv <;> omega
    exact (install_other wideSlots _ _ i hnone).trans (hextra i (by omega))
  obtain ⟨product,hp,hp3,_,_,hp9,_,hph,hps⟩ := HierarchyMultiplyEntry.multiply_run (width b)
    a.denominator (binary b c.denominator) (by simpa using scalar_fit b a.denominator ha.denominator)
  have productReady : ClockJoin.ReadyRun HierarchyMultiplyEntry.machine (128*(width b+1)*(b+1))
      (HierarchyMultiplyEntry.input14 (width b) a.denominator (binary b c.denominator)) product.final.tapes :=
    ⟨product,by simpa [HierarchyMultiplyEntry.budget] using hp,rfl,hph,
      by simpa [HierarchyMultiplyEntry.budget] using hps⟩
  have productInput : ∀ j,widened (multiplySlots j)=
      HierarchyMultiplyEntry.input14 (width b) a.denominator (binary b c.denominator) j := by
    intro j
    rw [input14_cases]
    by_cases h0 : j.val=0
    · have hj : j=0 := Fin.ext h0
      subst j
      exact we
    · by_cases h8 : j.val=8
      · have hj : j=8 := Fin.ext h8
        subst j
        exact wd
      · by_cases h9 : j.val=9
        · have hj : j=9 := Fin.ext h9
          subst j
          exact ww
        · simp only [multiplySlots,h0,h8,h9,if_false]
          have hh := wextra ⟨70+j.val,by omega⟩ (by simp)
          simpa [show ¬70+j.val=84 by omega] using hh
  let multiplied := install multiplySlots widened product.final.tapes
  have hproduct := bounded_focus multiplySlots (by decide) _ _ _ productReady widened productInput
  have pd : multiplied 73=frame (binary (width b) (a.denominator*c.denominator)) := by
    change install multiplySlots widened product.final.tapes (multiplySlots 3)=_
    simpa only [binary_value b c.denominator hc.denominator] using
      (install_slot multiplySlots (by decide) widened product.final.tapes 3).trans hp3
  have pextra (i : Fin 88) (hi : 84 ≤ i.val) : multiplied i=
      if i.val=84 then List.replicate b true else [] := by
    have hnone : ∀ j,multiplySlots j≠i := by
      intro j he
      have hv := congrArg Fin.val he
      simp only [multiplySlots] at hv
      split_ifs at hv <;> (try simp only at hv) <;> omega
    exact (install_other multiplySlots _ _ i hnone).trans (wextra i (by omega))
  obtain ⟨cropped,hcrop,hcrop0,_,hcrop2,_,_,hch,hcs⟩ :=
    ClockNormalize.normalize_run b (binary (width b) (a.denominator*c.denominator))
  have cropReady : ClockJoin.ReadyRun ClockNormalize.machine (4*b+4)
      (ClockNormalize.input b (binary (width b) (a.denominator*c.denominator))) cropped.final.tapes :=
    ⟨cropped,hcrop,rfl,hch,hcs.le⟩
  have cropInput : ∀ j,multiplied (cropSlots j)=
      ClockNormalize.input b (binary (width b) (a.denominator*c.denominator)) j := by
    intro j
    fin_cases j
    · exact pextra 84 (by decide)
    · exact pd
    · exact pextra 85 (by decide)
    · exact pextra 86 (by decide)
    · exact pextra 87 (by decide)
  let out := install cropSlots multiplied cropped.final.tapes
  have hcrop' := bounded_focus cropSlots (by decide) _ _ _ cropReady multiplied cropInput
  have htail := ClockJoin.join multiplyProgram cropProgram _ _ _ _ _ hproduct hcrop'
  have htail' := ClockJoin.join wideProgram (Composition.machine multiplyProgram cropProgram) _ _ _ _ _ hwide htail
  have hall : ClockJoin.ReadyRun machine (time b) (input b a c) out :=
    ClockJoin.join numeratorProgram _ _ _ _ _ _ hm htail'
  refine ⟨out,ClockJoin.enlarge machine _ _ _ _ hall (time_bound b),?_,?_,?_,?_,?_⟩
  · exact (install_other cropSlots _ _ 63 (by decide)).trans
      ((install_other multiplySlots _ _ 63 (by decide)).trans
        ((install_other wideSlots _ _ 63 (by decide)).trans h63))
  · exact (install_other cropSlots _ _ 64 (by decide)).trans
      ((install_other multiplySlots _ _ 64 (by decide)).trans
        ((install_other wideSlots _ _ 64 (by decide)).trans h64))
  · change install cropSlots multiplied cropped.final.tapes (cropSlots 2)=
      frame (binary b (a.denominator*c.denominator))
    simpa only [resize_prefix b (width b) _ (by unfold width; omega)] using
      (install_slot cropSlots (by decide) multiplied cropped.final.tapes 2).trans hcrop2
  · exact (install_other cropSlots _ _ 6 (by decide)).trans
      ((install_slot multiplySlots (by decide) widened product.final.tapes 9).trans hp9)
  · exact (install_slot cropSlots (by decide) multiplied cropped.final.tapes 0).trans hcrop0

end NearCubicWires.RepairOrdinary.CompetitorRationalSum
