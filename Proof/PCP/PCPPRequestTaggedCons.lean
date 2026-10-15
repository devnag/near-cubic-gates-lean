import Proof.PCP.PCPPRequestPair

/-! One actual tagged-list cons: total inner pair, paid tag1 print, and
the same positive outer pair. All copies/retained fields are physical. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestTaggedCons
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def innerSlots (j : Fin 38) : Fin 76 := ⟨j.val,by omega⟩
def printSlots : Fin 2 → Fin 76 := ![40,41]
def outerSlots (j : Fin 38) : Fin 76 := if j=3 then 26 else ⟨j.val+38,by omega⟩
theorem inner_injective : Function.Injective innerSlots := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 76 => x.val) h)
theorem print_injective : Function.Injective printSlots := by decide
theorem outer_injective : Function.Injective outerSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [outerSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega

def tag : List Bool := frame (1 : ℕ).bits
noncomputable def inner := RecoveryFocus.machine innerSlots PCPPRequestPair.machine
noncomputable def printer := RecoveryFocus.machine printSlots (HierarchyFixedWord.machine tag)
noncomputable def outer := RecoveryFocus.machine outerSlots PCPPairCanonical.machine
noncomputable def machine := Composition.machine (Composition.machine inner printer) outer
def input (a b : ℕ) : Fin 76 → List Bool := fun i =>
  if h : i.val<38 then PCPPRequestPair.input a b ⟨i.val,h⟩ else []
def budget (a b : ℕ) := PCPPRequestPair.budget a b+10+
  PCPPairCanonical.budget (1 : ℕ).bits (Nat.pair a b).bits

theorem cons_run (a b : ℕ) :
    ∃ out,ClockJoin.ReadyRun machine (budget a b) (input a b) out ∧
      (∃ padding,out 64=frame (Nat.pair 1 (Nat.pair a b)).bits++List.replicate padding false) ∧
      out 74=(Nat.pair 1 (Nat.pair a b)).bits := by
  obtain ⟨first,hfirst,⟨padding,hfield⟩,hraw⟩ := PCPPRequestPair.pair_run a b
  have h1 := CompetitorRationalProducts.bounded_focus innerSlots inner_injective _ _ _ hfirst
    (input a b) (by intro j; simp [input,innerSlots,j.isLt])
  let paired := install innerSlots (input a b) first
  have fresh (i : Fin 76) (hi : 38 ≤ i.val) : paired i=[] := by
    rw [show paired i=input a b i from install_other innerSlots _ _ i (by
      intro j he; have hv := congrArg Fin.val he; simp only [innerSlots] at hv; have hj := j.isLt; omega)]
    simp [input,show ¬i.val<38 by omega]
  have hprint : ClockJoin.ReadyRun (HierarchyFixedWord.machine tag) 8 (fun _ => [])
      ![tag,List.replicate tag.length false] := by
    obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready tag
    exact ⟨r,hr,ht,hh,hs.le⟩
  have h2 := CompetitorRationalProducts.bounded_focus printSlots print_injective _ _ _ hprint paired
    (by intro j; fin_cases j <;> exact fresh _ (by decide))
  let printed := install printSlots paired ![tag,List.replicate tag.length false]
  let middle := (Nat.pair a b).bits
  let caps : Fin 38 → ℕ := fun j => if j=3 then (frame middle).length+padding else 0
  obtain ⟨second,hsecond,hfield2,hraw2⟩ := PCPPairCanonical.pair_run (1 : ℕ).bits middle (by
    rw [CanonicalPositiveOutput.nat_bits_value]
    have h := Nat.left_le_pair 1 (value middle)
    omega)
  have padded := PCPPairReusable.padded_ready _ _ _ hsecond caps
  have hin (j : Fin 38) : printed (outerSlots j)=
      ZeroPadding.pad (caps j) (PCPPairCanonical.input (1 : ℕ).bits middle j) := by
    by_cases h3 : j=3
    · subst j
      have hkeep : printed (outerSlots 3)=paired 26 := install_other printSlots _ _ 26 (by decide)
      rw [hkeep]
      have hinner : paired 26=first 26 := install_slot innerSlots inner_injective _ _ 26
      rw [hinner,hfield]
      simp [caps,PCPPairCanonical.input,ZeroPadding.pad,middle]
    by_cases h2 : j=2
    · subst j
      have hp : printed (outerSlots 2)=tag := install_slot printSlots print_injective _ _ 0
      rw [hp]
      simp [caps,PCPPairCanonical.input,ZeroPadding.pad,tag]
    have hkeep : printed (outerSlots j)=paired (outerSlots j) := install_other printSlots _ _ _ (by
      intro k he
      have hv := congrArg Fin.val he
      have hs : (outerSlots j).val=j.val+38 := by simp [outerSlots,h3]
      rw [hs] at hv
      fin_cases k
      · change 40=j.val+38 at hv
        have hj : j.val≠2 := fun hh => h2 (Fin.ext hh)
        omega
      · change 41=j.val+38 at hv
        have hj : j.val≠3 := fun hh => h3 (Fin.ext hh)
        omega)
    rw [hkeep,fresh _ (by simp only [outerSlots,h3,ite_false]; omega)]
    have hj2 : j.val≠2 := fun hh => h2 (Fin.ext hh)
    have hj3 : j.val≠3 := fun hh => h3 (Fin.ext hh)
    simp [caps,h3,PCPPairCanonical.input,hj2,hj3,ZeroPadding.pad]
  have h3 := CompetitorRationalProducts.bounded_focus outerSlots outer_injective _ _ _ padded printed hin
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ h1 h2) h3
  refine ⟨install outerSlots printed (fun j => ZeroPadding.pad (caps j) (second j)),?_,?_,?_⟩
  · exact ClockJoin.enlarge _ _ _ _ _ hwhole (by unfold budget; dsimp only [middle]; omega)
  · have ho := install_slot outerSlots outer_injective printed
      (fun j => ZeroPadding.pad (caps j) (second j)) 26
    change install outerSlots printed (fun j => ZeroPadding.pad (caps j) (second j)) 64=_ at ho
    rw [hfield2] at ho
    simp only [caps,show (26 : Fin 38)≠3 by decide,ite_false,ZeroPadding.pad_zero,
      CanonicalPositiveOutput.nat_bits_value] at ho
    rw [show value middle=Nat.pair a b from CanonicalPositiveOutput.nat_bits_value _] at ho
    exact ⟨_,by simpa only [ZeroPadding.pad] using ho⟩
  · have ho := install_slot outerSlots outer_injective printed
      (fun j => ZeroPadding.pad (caps j) (second j)) 36
    change install outerSlots printed (fun j => ZeroPadding.pad (caps j) (second j)) 74=_ at ho
    rw [hraw2] at ho
    rw [show value middle=Nat.pair a b from CanonicalPositiveOutput.nat_bits_value _] at ho
    simpa only [caps,show (36 : Fin 38)≠3 by decide,ite_false,ZeroPadding.pad_zero,
      CanonicalPositiveOutput.nat_bits_value] using ho

end NearCubicWires.RepairOrdinary.PCPPRequestTaggedCons
