import Proof.Hierarchy.CompetitorValidityFields

/-! The actual six-field scalar record consumed by all validity comparisons.
Four signed numerator parts precede the two exact denominators. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Comparison where
  nums : Fin 4 → ℕ
  leftDenominator : ℕ
  rightDenominator : ℕ
def Comparison.fields (a : Comparison) (b : ℕ) (j : Fin 6) : List Bool :=
  if h : j.val<4 then binary (width b) (a.nums ⟨j.val,h⟩)
  else if j.val=4 then binary b a.leftDenominator else binary b a.rightDenominator
def targets : List (Fin 6) := [0,1,2,3,4,5]
def Comparison.word (a : Comparison) (b : ℕ) := fieldStream (a.fields b) targets
def Comparison.passes (a : Comparison) : Prop :=
  ((a.nums 2 : ℚ)-a.nums 3)/a.rightDenominator≤((a.nums 0 : ℚ)-a.nums 1)/a.leftDenominator
structure Comparison.Valid (a : Comparison) (b : ℕ) : Prop where
  nums : ∀ i,a.nums i<2^b
  left : a.leftDenominator<2^b
  right : a.rightDenominator<2^b
  leftPositive : 0<a.leftDenominator
  rightPositive : 0<a.rightDenominator
def loadedRecord (b : ℕ) (source : List Bool) (a : Comparison) :=
  placed b (a.fields b) targets (erased b source)
def nativeSlots (i : Fin 67) : Fin 71 := i.castAdd 4
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlots CompetitorRationalDecision.machine

theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 71 => k.val) h

theorem placed_other (b : ℕ) (fields : Fin 6 → List Bool) (js : List (Fin 6))
    (ambient : Fin 71 → List Bool) (i : Fin 71) (hi : ∀ j∈js,target j≠i) :
    placed b fields js ambient i=ambient i := by
  induction js generalizing ambient with
  | nil => rfl
  | cons j js ih =>
    rw [placed,ih _ (fun k hk => hi k (by simp [hk]))]
    exact Function.update_of_ne (hi j (by simp)).symm _ _

theorem record_other (b : ℕ) (source : List Bool) (a : Comparison) (i : Fin 71)
    (hi : 6 ≤ i.val) : loadedRecord b source a i=erased b source i := by
  apply placed_other
  intro j _ hj
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem record_native (b : ℕ) (source : List Bool) (a : Comparison) (i : Fin 67) :
    loadedRecord b source a (nativeSlots i)=paddedInput b a.nums a.leftDenominator a.rightDenominator i := by
  by_cases hi : i.val<6
  · have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by
      omega
    rcases hcases with h|h|h|h|h|h <;> subst i
    all_goals simp [loadedRecord,placed,targets,loaded,Comparison.fields,target,nativeSlots,
      paddedInput,padding,CompetitorRationalProducts.input]
  · rw [record_other b source a (nativeSlots i) (by exact Nat.le_of_not_gt hi)]
    by_cases h6 : i.val=6
    · have heq : i=6 := Fin.ext h6
      subst i
      simp [erased,data,nativeSlots,paddedInput,padding,CompetitorRationalProducts.input,ZeroPadding.pad]
    · simp [erased,data,nativeSlots,paddedInput,padding,CompetitorRationalProducts.input,
        show ¬i.val<4 by omega,show i.val≠4 by omega,show i.val≠5 by omega,hi,h6,i.isLt,ZeroPadding.pad]

theorem field_capacity (b : ℕ) (a : Comparison) (j : Fin 6) :
    2*(a.fields b j).length+1≤capacity b := by
  have hw : 2*width b+1≤capacity b := by unfold width capacity; nlinarith
  have hb : 2*b+1≤capacity b := by unfold capacity; nlinarith
  unfold Comparison.fields
  split
  · simpa using hw
  · split <;> simpa using hb

theorem record_cost (b : ℕ) (a : Comparison) : fieldCost (a.fields b) targets=40*b+56 := by
  simp [fieldCost,targets,Comparison.fields,width]
  omega
theorem record_length (b : ℕ) (a : Comparison) : (a.word b).length=20*b+22 := by
  simp [Comparison.word,fieldStream,targets,Comparison.fields,width]
  omega

theorem record_fields_run (b : ℕ) (a : Comparison) (pre suffix : List Bool) :
    ∃ r : ExecutionReceipt 71 (fieldStates targets),
      runFrom (fieldsProgram targets) (40*b+56)
        (cfg (fieldsProgram targets).start pre.length (erased b (pre++a.word b++suffix)))=some r ∧
      r.final.heads=heads (pre.length+20*b+22) ∧
      r.final.tapes=loadedRecord b (pre++a.word b++suffix) a ∧ r.steps=40*b+56 := by
  have hb : ∀ j∈targets,erased b (pre++a.word b++suffix) (target j)=List.replicate (capacity b) false := by
    intro j _
    simp [erased,data,target,j.isLt]
  obtain ⟨r,hr,hh,ht,hs⟩ := fields_run b (a.fields b) targets (by decide) pre suffix
    (erased b (pre++a.word b++suffix)) rfl hb rfl (fun j _ => field_capacity b a j)
  rw [record_cost] at hr hs
  refine ⟨r,hr,?_,ht,hs⟩
  change r.final.heads=heads (pre.length+(a.word b).length) at hh
  rw [record_length] at hh
  simpa only [Nat.add_assoc] using hh

end NearCubicWires.RepairOrdinary.CompetitorValidity
