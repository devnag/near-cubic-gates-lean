import Proof.Assembly.RowsPoolMinimumLoop
import Proof.CaseAnalysis.FinalSupplierRowInput

/-! Positive half of the signed frozen score, read from actual native weights.
The native reader already produces both halves. Swapping its two output tapes
feeds the existing masked accumulator with the positive half; its paid read,
advance and scratch erase remain unchanged. The physical selection mask is an
explicit input until the membership/assignment mask writer is connected.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireScore

open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation CloseoutRowsPoolMinimum
open CloseoutRowsPoolWeight (Item word mask)
open RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def swapSlots (i : Fin 20) : Fin 20 := if i = 10 then 11 else if i = 11 then 10 else i
theorem swap_injective : Function.Injective swapSlots := by decide
theorem swap_twice (i : Fin 20) : swapSlots (swapSlots i) = i := by fin_cases i <;> rfl
def swapped (A : Fin 20 → List Bool) : Fin 20 → List Bool := fun i => A (swapSlots i)

theorem install_swap (A B : Fin 20 → List Bool) : install swapSlots A B = swapped B := by
  funext i
  have h := install_slot swapSlots swap_injective A B (swapSlots i)
  simpa only [swap_twice, swapped] using h

theorem swap_heads (pos mpos : ℕ) : dockH swapSlots (heads pos mpos) (heads pos mpos) = heads pos mpos := by
  apply dockH_existing
  intro i; fin_cases i <;> rfl

theorem swap_data (source membership : List Bool) (w C a : ℕ) :
    swapped (data source membership w C a) = data source membership w C a := by
  funext i; fin_cases i <;> rfl

noncomputable def reader := RecoveryFocus.machine swapSlots CloseoutRowsPoolMinimum.reader
noncomputable def body := Composition.machine
  (Composition.machine (Composition.machine reader choice) advance) erase

theorem positive_read (pre tail membership : List Bool) (mpos w C a : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w + 1 ≤ C) :
    Step reader (CloseoutRowsPoolMagnitude.budget z w) (heads pre.length mpos)
      (data (pre ++ intWord z ++ tail) membership w C a)
      (heads (pre.length + (intWord z).length) mpos)
      (swapped (parsed (pre ++ intWord z ++ tail) membership
        (pre.length + (intWord z).length) w C a z)) := by
  have actual := (read_run pre tail membership mpos w C a z hC).focus swapSlots swap_injective
    (heads pre.length mpos) (data (pre ++ intWord z ++ tail) membership w C a)
  have hh : dockH swapSlots (heads pre.length mpos)
      (heads (pre.length + (intWord z).length) mpos) =
      heads (pre.length + (intWord z).length) mpos := by
    funext i
    have h := dockH_slot swapSlots swap_injective (heads pre.length mpos)
      (heads (pre.length + (intWord z).length) mpos) (swapSlots i)
    rw [swap_twice] at h
    exact h.trans (by fin_cases i <;> rfl)
  exact (actual.congr_in (swap_heads _ _) ((install_swap _ _).trans (swap_data _ _ _ _ _))).congr hh
    (install_swap _ _)

theorem positive_input (source membership : List Bool) (pos w C a : ℕ) (z : ℤ)
    (hw : natBitLength z.natAbs ≤ w) (j : Fin 5) :
    swapped (parsed source membership pos w C a z) (addSlots j) = addInput C w z.toNat a j := by
  fin_cases j
  · exact (CloseoutRowsPoolMagnitude.parts source pos w C z hw).1
  all_goals rfl

theorem positive_support (pre tail membership : List Bool) (w C a : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w + 1 ≤ C) (j : Fin 14) :
    (swapped (parsed (pre ++ intWord z ++ tail) membership
      (pre.length + (intWord z).length) w C a z) (workSlots j)).length ≤ C := by
  have hs : swapSlots (workSlots j) = workSlots ((Equiv.swap (8 : Fin 14) 9) j) := by
    fin_cases j <;> decide
  change (parsed _ _ _ _ _ _ _ (swapSlots (workSlots j))).length ≤ C
  rw [hs]
  exact parsed_support pre tail membership w C a z hC _

theorem positive_cleared (source membership : List Bool) (pos w C a : ℕ) (z : ℤ) (selected : Bool) :
    cleared C (added C w z.toNat a selected (swapped (parsed source membership pos w C a z))) =
      data source membership w C (a + if selected then z.toNat else 0) := by
  let A := swapped (parsed source membership pos w C a z)
  funext i
  fin_cases i
  · exact (cleared_live C _ 0 (by simp)).trans
      ((added_other C w z.toNat a selected A 0 (by decide)).trans
        (CloseoutRowsPoolMagnitude.source source pos w C z))
  · exact cleared_work C _ 0
  · exact cleared_work C _ 1
  · exact cleared_work C _ 2
  · exact cleared_work C _ 3
  · exact cleared_work C _ 4
  · exact cleared_work C _ 5
  · exact cleared_work C _ 6
  · exact cleared_work C _ 7
  · exact (cleared_live C _ 9 (by simp)).trans
      ((added_other C w z.toNat a selected A 9 (by decide)).trans
        (CloseoutRowsPoolMagnitude.width source pos w C z))
  · exact cleared_work C _ 8
  · exact cleared_work C _ 9
  · exact cleared_work C _ 10
  · exact (cleared_live C _ 13 (by simp)).trans (added_other C w z.toNat a selected A 13 (by decide))
  · exact (cleared_live C _ 14 (by simp)).trans (added_accumulator C w z.toNat a selected A rfl)
  · exact cleared_work C _ 11
  · exact cleared_work C _ 12
  · exact cleared_work C _ 13
  · exact (cleared_driver C _).1
  · exact (cleared_driver C _).2

/-- One actual signed field contributes its positive half under the current
physical mask bit. Source and mask advance, and the same scratch is reusable. -/
theorem body_run (pre tail mpre mtail : List Bool) (z : ℤ) (selected : Bool) (w C a : ℕ)
    (hw : natBitLength z.natAbs ≤ w) (hc : 8 * w + 12 ≤ C) (hf : z.toNat + a < 2 ^ w) :
    Step body (bodyBudget z w C) (heads pre.length mpre.length)
      (data (pre ++ intWord z ++ tail) (mpre ++ selected :: mtail) w C a)
      (heads (pre.length + (intWord z).length) (mpre.length + 1))
      (data (pre ++ intWord z ++ tail) (mpre ++ selected :: mtail) w C
        (a + if selected then z.toNat else 0)) := by
  have hC : RowPowerNativeReset.rawTime z w + 1 ≤ C := by
    unfold RowPowerNativeReset.rawTime
    omega
  let source := pre ++ intWord z ++ tail
  let membership := mpre ++ selected :: mtail
  let pos := pre.length + (intWord z).length
  let A := swapped (parsed source membership pos w C a z)
  let B := added C w z.toNat a selected A
  have read := positive_read pre tail membership mpre.length w C a z hC
  have add := choice_run C w z.toNat a (heads pos mpre.length) A selected (by omega) hf
    (by intro j; fin_cases j <;> rfl) (positive_input source membership pos w C a z hw)
    (Streaming.read_append mpre mtail selected)
  have joined := (read.seq add).seq (advance_run B pos mpre.length)
  have erasing := clear_run C (heads pos (mpre.length + 1)) B
    (by intro j; fin_cases j <;> rfl)
    (added_support C w z.toNat a selected A (by omega)
      (positive_support pre tail membership w C a z hC))
    (by exact (added_other C w z.toNat a selected A 18 (by decide)).trans rfl)
    (by exact (added_other C w z.toNat a selected A 19 (by decide)).trans rfl)
  have complete := joined.seq erasing
  have ht : ((CloseoutRowsPoolMagnitude.budget z w + 1 + CloseoutRowsPoolMinimum.budget w) + 1 + 1) + 1 +
      (2 * C + 4) = bodyBudget z w C := by
    unfold CloseoutRowsPoolMagnitude.budget RowPowerNativeReset.rawTime CloseoutRowsPoolMinimum.budget bodyBudget
    omega
  rw [ht] at complete
  exact complete.congr rfl (positive_cleared source membership pos w C a z selected)

def positiveSum (xs : List Item):=(xs.map (fun x=>x.1.toNat)).sum
def selectedSum (xs : List Item):=(xs.map (fun x=>if x.2 then x.1.toNat else 0)).sum
noncomputable def loop:=RepeatMachine.machine body (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (membership : List Bool) (mpos w C a total driver : ℕ):=
  RepeatMachine.cfg phase (⟨body.start,heads pos mpos,data source membership w C a⟩) total driver

theorem remaining (xs : List Item) (pre tail mpre mtail : List Bool)
    (w C a total pos : ℕ) (hn : pos+xs.length=total)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hf : a+positiveSum xs<2^w) :
    ∃ time≤xs.length*(uniformBudget w C+2)+total+3,Timed loop time
      (cfg 0 (pre++word xs++tail) pre.length (mpre++mask xs++mtail) mpre.length w C a total (pos+1))
      (cfg 3 (pre++word xs++tail) (pre.length+(word xs).length)
        (mpre++mask xs++mtail) (mpre.length+xs.length) w C (a+selectedSum xs) total 1):=by
  induction xs generalizing pre mpre a pos with
  | nil=>
    have he:pos=total:=by simpa using hn
    subst pos
    refine ⟨total+3,by simp,?_⟩
    simpa [cfg,loop,word,mask,selectedSum] using RepeatMachine.exhaust body (fun _ _=>true)
      (⟨body.start,heads pre.length mpre.length,data (pre++tail) (mpre++mtail) w C a⟩) total
  | cons x xs ih=>
    have hx:=hw x (by simp)
    have htail:∀ y∈xs,natBitLength y.1.natAbs≤w:=fun y hy=>hw y (by simp [hy])
    have hf':a+(x.1.toNat+positiveSum xs)<2^w:=by
      simpa only [positiveSum,List.map_cons,List.sum_cons] using hf
    have hpiece:(if x.2 then x.1.toNat else 0)≤x.1.toNat:=by
      cases x.2 <;> simp
    obtain ⟨r,hr,rh,rt,rs⟩:=body_run pre (word xs++tail) mpre (mask xs++mtail)
      x.1 x.2 w C a hx hc (by omega)
    have one:=RepeatMachine.iteration body (fun _ _=>true)
      ⟨body.start,heads pre.length mpre.length,
        data (pre++intWord x.1++(word xs++tail)) (mpre++x.2::(mask xs++mtail)) w C a⟩
      total pos r rfl (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at one
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (⟨body.start,heads (pre.length+(intWord x.1).length) (mpre.length+1),
        data (pre++intWord x.1++(word xs++tail)) (mpre++x.2::(mask xs++mtail)) w C
          (a+if x.2 then x.1.toNat else 0)⟩) total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩:=ih (pre++intWord x.1) (mpre++[x.2])
      (a+if x.2 then x.1.toNat else 0) (pos+1)
      (by simp only [List.length_cons] at hn;omega) htail (by omega)
    have hp:(pre++intWord x.1).length=pre.length+(intWord x.1).length:=List.length_append
    have hm:(mpre++[x.2]).length=mpre.length+1:=by simp
    simp only [cfg,List.append_assoc,List.singleton_append,hp,hm,show pos+1+1=pos+2 by omega] at rest
    simp only [List.append_assoc,List.cons_append] at one rest
    have all:=one.trans rest
    refine ⟨r.steps+2+t,?_,?_⟩
    · have hb:=rs.trans (body_bound x.1 w C hx)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [loop,cfg,word,mask,selectedSum,List.flatMap_cons,List.map_cons,List.sum_cons,
        List.length_append,List.length_cons,List.append_assoc,List.cons_append,Nat.add_assoc,
        Nat.add_comm 1 xs.length] using all

def loopBudget (xs : List Item) (w C : ℕ):=xs.length*(uniformBudget w C+3)+3

theorem score_run (xs : List Item) (pre tail mpre mtail : List Bool) (w C a : ℕ)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C) (hf : a+positiveSum xs<2^w) :
    ∃ r,runFrom loop (loopBudget xs w C)
      (cfg 0 (pre++word xs++tail) pre.length (mpre++mask xs++mtail) mpre.length w C a xs.length 1)=some r ∧
      r.final=cfg 3 (pre++word xs++tail) (pre.length+(word xs).length)
        (mpre++mask xs++mtail) (mpre.length+xs.length) w C (a+selectedSum xs) xs.length 1 ∧
      r.steps≤loopBudget xs w C:=by
  obtain ⟨t,ht,h⟩:=remaining xs pre tail mpre mtail w C a xs.length 0 (by omega) hw hc hf
  obtain ⟨r,hr,hfinal,hs⟩:=h.run (by simp [loop,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  have hb:t≤loopBudget xs w C:=by
    unfold loopBudget
    have he:xs.length*(uniformBudget w C+2)+xs.length+3=
        xs.length*(uniformBudget w C+3)+3:=by ring
    omega
  have more:=runFrom_moreFuel loop t (loopBudget xs w C-t) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,hfinal,hs.le.trans hb⟩

def signedSum (xs : List Item) : ℤ := (xs.map (fun x => if x.2 then x.1 else 0)).sum

/-- The positive result and existing negative result are the two natural
halves of the exact frozen signed score. -/
theorem selected_difference (xs : List Item) :
    (selectedSum xs : ℤ) - (CloseoutRowsPoolMinimum.liveSum xs : ℤ) = signedSum xs := by
  induction xs with
  | nil => simp [selectedSum, CloseoutRowsPoolMinimum.liveSum, signedSum]
  | cons x xs ih =>
    have hpart := Int.toNat_sub_toNat_neg x.1
    cases hx : x.2 <;>
      simp [selectedSum, CloseoutRowsPoolMinimum.liveSum, signedSum, hx] at ih ⊢ <;> omega

open SupplierPipeline SupplierEstimator ThresholdCompiler
open scoped BigOperators

noncomputable def frozenMask {q : ℕ} (live : Finset (Fin q)) (y : BitInput live.card) : BitInput q :=
  C10SupplierRowInput.joinInput live y (fun _ => false)

noncomputable def items {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) : List Item := List.ofFn (fun i => (g.weight i, frozenMask live y i))

theorem items_word {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) : word (items live g y) = (List.ofFn g.weight).flatMap intWord := by
  change (List.ofFn (fun i => (g.weight i, frozenMask live y i))).flatMap (fun x => intWord x.1) = _
  rw [← List.flatMap_map, List.map_ofFn]
  rfl

theorem items_mask {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) : mask (items live g y) = List.ofFn (frozenMask live y) := by
  simp [mask, items, List.map_ofFn, Function.comp_def]

theorem items_score {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) : signedSum (items live g y) =
      ∑ j : Fin live.card, g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) *
        (if y j then 1 else 0) := by
  simp only [signedSum, items, List.map_ofFn, List.sum_ofFn]
  change (∑ i : Fin q, if frozenMask live y i then g.weight i else 0) = _
  rw [← Equiv.sum_comp (normalizedLiveExternalCoordinateEquiv live)
    (fun i => if frozenMask live y i then g.weight i else (0 : ℤ)), Fintype.sum_sum_type]
  simp [frozenMask, C10SupplierRowInput.joinInput_coord, mul_ite]

/-- The exact child target uses these two computed halves. Producing its
signed serialization still requires a paid subtract/add writer. -/
theorem hardwire_target_parts {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) : (C10SupplierRowInput.hardwire live g y).target =
      g.target - (selectedSum (items live g y) : ℤ) +
        (CloseoutRowsPoolMinimum.liveSum (items live g y) : ℤ) := by
  change g.target - _ = _
  rw [← items_score, ← selected_difference]
  ring

end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireScore
