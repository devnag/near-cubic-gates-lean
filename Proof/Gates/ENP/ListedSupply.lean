import Proof.Gates.ENP.ListedCount
import Proof.CaseAnalysis.RecoveryCapacityDrivers
import Proof.CaseAnalysis.RecoveryProjectionRun
import Proof.CaseAnalysis.RecoveryFullBound
import Proof.CaseAnalysis.RecoveryPreparedLayout
import Proof.Amplification.RecoveryReadyCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP.USupply

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.CanonicalRecoveryLanguage

/-- The number of tapes. -/
def uTapes (d : ℕ) : ℕ := 342 + RecoveryFullBound.tapes d

def old (d : ℕ) (i : Fin 158) : Fin (uTapes d) := ⟨i.val, by unfold uTapes; omega⟩
def at_ (d n : ℕ) (h : n < 342) : Fin (uTapes d) := ⟨n, by unfold uTapes; omega⟩

theorem old_injective (d : ℕ) : Function.Injective (old d) := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

/-- The count stage's tape `j` (24 tapes: streams at `0` and `2..7`, cell `1`, registers `8..23`). -/
def countVal (n : ℕ) : ℕ :=
  if n = 0 then 158 else if n = 1 then 162 else if n = 2 then 159 else if n = 3 then 106 else if n = 4 then 70
  else if n = 5 then 157 else if n = 6 then 160 else if n = 7 then 161 else 155 + n

theorem countVal_lt (n : ℕ) (h : n < 24) : countVal n < 179 := by
  unfold countVal; split_ifs <;> omega

theorem countVal_inj : ∀ a < 24, ∀ b < 24, countVal a = countVal b → a = b := by decide

def countSlot (d : ℕ) (j : Fin 24) : Fin (uTapes d) :=
  ⟨countVal j.val, by have := countVal_lt j.val j.isLt; unfold uTapes; omega⟩

theorem countSlot_injective (d : ℕ) : Function.Injective (countSlot d) := by
  intro a b h
  exact Fin.ext (countVal_inj a.val a.isLt b.val b.isLt (congrArg Fin.val h))

/-- The capacity worker's tape `j`. -/
def capVal (n : ℕ) : ℕ :=
  if n = 0 then 179 else if n = 7 then 154 else if n = 45 then 76 else if n = 48 then 77 else 180 + n

def capSlot (d : ℕ) (j : Fin 49) : Fin (uTapes d) :=
  ⟨capVal j.val, by have := j.isLt; unfold capVal uTapes; split_ifs <;> omega⟩

theorem capSlot_injective (d : ℕ) : Function.Injective (capSlot d) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  simp only [capSlot, capVal] at hv
  split_ifs at hv <;> omega

/-- The projection worker's tape `j`. -/
def projVal (n : ℕ) : ℕ :=
  if n < 37 then 78 + n else if n = 37 then 160 else if n = 65 then 161 else if n = 104 then 76
  else if n = 106 then 115 else if n = 109 then 153 else if n = 111 then 156 else 229 + n

def projSlot (d : ℕ) (j : Fin 113) : Fin (uTapes d) :=
  ⟨projVal j.val, by have := j.isLt; unfold projVal uTapes; split_ifs <;> omega⟩

theorem projSlot_injective (d : ℕ) : Function.Injective (projSlot d) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  simp only [projSlot, projVal] at hv
  split_ifs at hv <;> omega

/-- The full-bound worker's tape `j`. -/
def fullSlot (d : ℕ) (j : Fin (RecoveryFullBound.tapes d)) : Fin (uTapes d) :=
  if j = RecoveryFullBound.sourceSlot d then old d 153
  else if j = RecoveryFullBound.rawSlot d then old d 155
  else if j = RecoveryFullBound.compareSlot d then old d 152
  else ⟨342 + j.val, by unfold uTapes; omega⟩

theorem fullSlot_injective (d : ℕ) : Function.Injective (fullSlot d) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [fullSlot, old] at hv
  split_ifs at hv <;> dsimp at hv <;> subst_vars <;> omega

theorem fullSlot_source (d : ℕ) : fullSlot d (RecoveryFullBound.sourceSlot d) = old d 153 := by
  simp only [fullSlot, if_pos]
theorem fullSlot_raw (d : ℕ) : fullSlot d (RecoveryFullBound.rawSlot d) = old d 155 := by
  have hn : RecoveryFullBound.rawSlot d ≠ RecoveryFullBound.sourceSlot d := RecoveryFullBound.copy_away_source d 1
  simp only [fullSlot, if_neg hn, if_pos]
theorem fullSlot_compare (d : ℕ) : fullSlot d (RecoveryFullBound.compareSlot d) = old d 152 := by
  have hn : RecoveryFullBound.compareSlot d ≠ RecoveryFullBound.rawSlot d :=
    RecoveryFullBound.old_away d 0 (DimensionPolynomial.rawSlot (RecoveryFullBound.exponent d))
  have hs : RecoveryFullBound.compareSlot d ≠ RecoveryFullBound.sourceSlot d := RecoveryFullBound.copy_away_source d 0
  simp only [fullSlot, if_neg hs, if_neg hn, if_pos]

/-- The entry bank: the listed table on `158`, `R` in unary on `159`, `W` in unary on `179`. -/
def input (d : ℕ) (table : List Bool) (R W : ℕ) (i : Fin (uTapes d)) : List Bool :=
  if i.val = 158 then table else if i.val = 159 then List.replicate R true
  else if i.val = 179 then List.replicate W true else []

/-- The supplier: count stage, capacity, projection, full bound. -/
noncomputable def machine (d : ℕ) :=
  Composition.machine (RecoveryFocus.machine (countSlot d) UCount.prog.compile)
    (Composition.machine (RecoveryFocus.machine (capSlot d) RecoveryCapacityDrivers.machine)
      (Composition.machine (RecoveryFocus.machine (projSlot d) RecoveryProjectionCold.machine)
        (RecoveryFocus.machine (fullSlot d) (RecoveryFullBound.machine d))))

/-- The supplier's budget. -/
def budget (d R M W : ℕ) : ℕ :=
  UCount.progCost R M + 1 + (RecoveryCapacityDrivers.budget W + 1 +
    (RecoveryProjectionCold.budget R M (RecoveryCapacityDrivers.capacityB W) + 1 + RecoveryFullBound.budget d R))

/-! ## Which tapes each stage touches -/

theorem count_other (d : ℕ) (A : Fin (uTapes d) → List Bool) (O : Fin 24 → List Bool) (i : Fin (uTapes d))
    (h106 : i.val ≠ 106) (h70 : i.val ≠ 70) (h157 : i.val ≠ 157) (hr : i.val < 158 ∨ 179 ≤ i.val) :
    install (countSlot d) A O i = A i := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  have hjl := j.isLt
  simp only [countSlot, countVal] at hv
  split_ifs at hv <;> omega

theorem cap_other (d : ℕ) (A : Fin (uTapes d) → List Bool) (O : Fin 49 → List Bool) (i : Fin (uTapes d))
    (h179 : i.val ≠ 179) (h154 : i.val ≠ 154) (h76 : i.val ≠ 76) (h77 : i.val ≠ 77)
    (hr : i.val < 180 ∨ 229 ≤ i.val) : install (capSlot d) A O i = A i := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  have hjl := j.isLt
  simp only [capSlot, capVal] at hv
  split_ifs at hv <;> omega

theorem proj_other (d : ℕ) (A : Fin (uTapes d) → List Bool) (O : Fin 113 → List Bool) (i : Fin (uTapes d))
    (hb : i.val < 78 ∨ 115 ≤ i.val) (h160 : i.val ≠ 160) (h161 : i.val ≠ 161) (h76 : i.val ≠ 76)
    (h115 : i.val ≠ 115) (h153 : i.val ≠ 153) (h156 : i.val ≠ 156) (hr : i.val < 229 ∨ 342 ≤ i.val) :
    install (projSlot d) A O i = A i := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  have hjl := j.isLt
  simp only [projSlot, projVal] at hv
  split_ifs at hv <;> omega

theorem full_other (d : ℕ) (A : Fin (uTapes d) → List Bool) (O : Fin (RecoveryFullBound.tapes d) → List Bool)
    (i : Fin (uTapes d)) (h153 : i.val ≠ 153) (h155 : i.val ≠ 155) (h152 : i.val ≠ 152) (hr : i.val < 342) :
    install (fullSlot d) A O i = A i := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  dsimp only [fullSlot, old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

/-! ## The stage inputs -/

theorem count_input (d : ℕ) (vals post : List Bool) (R W : ℕ) (j : Fin 24) :
    input d (RepairOrdinary.frame vals ++ post) R W (countSlot d j) =
      CheckedPCPP.coldBank (UCount.start vals post R) j := by
  fin_cases j <;> simp [input, countSlot, countVal, CheckedPCPP.coldBank, role, UCount.start]

theorem cap_input (d : ℕ) (A : Fin (uTapes d) → List Bool) (W : ℕ)
    (hW : A (at_ d 179 (by omega)) = List.replicate W true)
    (hblank : ∀ i : Fin (uTapes d), i.val ≠ 179 → (i.val = 154 ∨ i.val = 76 ∨ i.val = 77 ∨ 180 ≤ i.val) →
      i.val < 229 → A i = []) (j : Fin 49) :
    A (capSlot d j) = RecoveryCapacityDrivers.input W j := by
  have hj := j.isLt
  unfold RecoveryCapacityDrivers.input
  by_cases h0 : j.val = 0
  · rw [if_pos h0]
    have : capSlot d j = at_ d 179 (by omega) := Fin.ext (by simp [capSlot, capVal, at_, h0])
    rw [this, hW]
  · rw [if_neg h0]
    apply hblank
    · simp only [capSlot, capVal]; split_ifs <;> omega
    · simp only [capSlot, capVal]; split_ifs <;> omega
    · simp only [capSlot, capVal]; split_ifs <;> omega

/-- The clause count of the listed-pairs PCP is its number of pairs. -/
theorem unit_clauses_length (w : ℕ) (vals : List Bool) : (Codec.clauses (unitPCP w vals)).length = vals.length := by
  unfold Codec.clauses
  rw [List.Nodup.dedup (unit_clauses_nodup w vals)]
  simp [unitPCP]

/-- The prepared bank of the listed-pairs PCP at oracle width `R` and workspace `W`. -/
noncomputable def prepared (d w R W : ℕ) (vals : List Bool) : Fin 158 → List Bool :=
  RecoveryBoundedColdPrepared.input R (oracleSizeBound d R) (RecoveryCapacityDrivers.capacityC W) vals.length
    vals.length (RecoveryCapacityDrivers.capacityB W)
    (RecoveryBoundedRowProjection.bank (unitPCP w vals) R vals.length (bitInputOfCode R 0)
      (RecoveryCapacityDrivers.capacityB W)) (DedupBytes.fields (unitPCP w vals))

set_option maxHeartbeats 1000000 in

theorem supply_ready (d : ℕ) (vals post : List Bool) (w R W : ℕ) (hlen : vals.length = 2 ^ w) (hw : w ≤ R) :
    ∃ out, ClockJoin.ReadyRun (machine d) (budget d R vals.length W)
      (input d (RepairOrdinary.frame vals ++ post) R W) out ∧
      (∀ i : Fin 158, out (old d i) = prepared d w R W vals i) ∧
      out (at_ d 158 (by omega)) = RepairOrdinary.frame vals ++ post ∧
      out (at_ d 179 (by omega)) = List.replicate W true := by
  set M := vals.length with hM
  set p := unitPCP w vals with hp
  set A0 := input d (RepairOrdinary.frame vals ++ post) R W with hA0
  -- count
  obtain ⟨cOut, hc, hcs⟩ := UCount.prog_ready vals post R
  have h1 := hc.focus (countSlot d) (countSlot_injective d) A0 (count_input d vals post R W)
  set A1 := install (countSlot d) A0 cOut with hA1
  have hc3 : cOut 3 = qStream R M := hcs 2
  have hc4 : cOut 4 = cStream vals M := hcs 3
  have hc5 : cOut 5 = List.replicate M true := hcs 4
  have hc6 : cOut 6 = RepairOrdinary.frame R.bits := hcs 5
  have hc7 : cOut 7 = RepairOrdinary.frame M.bits := hcs 6
  have hc0 : cOut 0 = RepairOrdinary.frame vals ++ post := hcs 0
  have e106 : old d 106 = countSlot d 3 := Fin.ext rfl
  have e70 : old d 70 = countSlot d 4 := Fin.ext rfl
  have e157 : old d 157 = countSlot d 5 := Fin.ext rfl
  have e160 : at_ d 160 (by omega) = countSlot d 6 := Fin.ext rfl
  have e161 : at_ d 161 (by omega) = countSlot d 7 := Fin.ext rfl
  have e158 : at_ d 158 (by omega) = countSlot d 0 := Fin.ext rfl
  have hA1_106 : A1 (old d 106) = qStream R M := by rw [e106, hA1, install_slot _ (countSlot_injective d), hc3]
  have hA1_70 : A1 (old d 70) = cStream vals M := by rw [e70, hA1, install_slot _ (countSlot_injective d), hc4]
  have hA1_157 : A1 (old d 157) = List.replicate M true := by
    rw [e157, hA1, install_slot _ (countSlot_injective d), hc5]
  have hA1_160 : A1 (at_ d 160 (by omega)) = RepairOrdinary.frame R.bits := by
    rw [e160, hA1, install_slot _ (countSlot_injective d), hc6]
  have hA1_161 : A1 (at_ d 161 (by omega)) = RepairOrdinary.frame M.bits := by
    rw [e161, hA1, install_slot _ (countSlot_injective d), hc7]
  have hA1_158 : A1 (at_ d 158 (by omega)) = RepairOrdinary.frame vals ++ post := by
    rw [e158, hA1, install_slot _ (countSlot_injective d), hc0]
  have hA1_other : ∀ i : Fin (uTapes d), i.val ≠ 106 → i.val ≠ 70 → i.val ≠ 157 → (i.val < 158 ∨ 179 ≤ i.val) →
      A1 i = A0 i := fun i a b c e => count_other d A0 cOut i a b c e
  -- capacity
  obtain ⟨C, hC, hCW, hCc, hCb, _, hClog⟩ := RecoveryCapacityDrivers.run W
  have h2 := hC.focus (capSlot d) (capSlot_injective d) A1 (cap_input d A1 W
    (by rw [hA1_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inr (by simp [at_, old]))]; simp [A0, input, at_])
    (by
      intro i h179 hi hlt
      rw [hA1_other i (by omega) (by omega) (by omega) (by omega)]
      simp only [A0, input]
      rw [if_neg (by omega), if_neg (by omega), if_neg h179]))
  set A2 := install (capSlot d) A1 C with hA2
  have hA2_other : ∀ i : Fin (uTapes d), i.val ≠ 179 → i.val ≠ 154 → i.val ≠ 76 → i.val ≠ 77 →
      (i.val < 180 ∨ 229 ≤ i.val) → A2 i = A1 i := fun i a b c e f => cap_other d A1 C i a b c e f
  have hA2_76 : A2 (old d 76) = List.replicate (RecoveryCapacityDrivers.capacityB W) true := by
    rw [show old d 76 = capSlot d 45 from Fin.ext rfl, hA2, install_slot _ (capSlot_injective d)]; exact hCb
  have hA2_77 : A2 (old d 77) = List.replicate (RecoveryCapacityDrivers.capacityB W + 1) false := by
    rw [show old d 77 = capSlot d 48 from Fin.ext rfl, hA2, install_slot _ (capSlot_injective d)]; exact hClog
  have hA2_154 : A2 (old d 154) = List.replicate (RecoveryCapacityDrivers.capacityC W) true := by
    rw [show old d 154 = capSlot d 7 from Fin.ext rfl, hA2, install_slot _ (capSlot_injective d)]; exact hCc
  have hA2_179 : A2 (at_ d 179 (by omega)) = List.replicate W true := by
    rw [show at_ d 179 (by omega) = capSlot d 0 from Fin.ext rfl, hA2, install_slot _ (capSlot_injective d), hCW]
  -- projection
  set B := RecoveryCapacityDrivers.capacityB W with hB
  obtain ⟨P, hP, hbank, _h103, h106, h109, h111, h104⟩ := RecoveryProjectionCold.original_ready p R M B
  have hq := qStream_eq w R vals hlen hw
  have hin3 : ∀ j, A2 (projSlot d j) =
      RecoveryProjectionCold.input R M B (QueryBytes.framedCodes (normalizedRows p R M).flatten) j := by
    intro j
    have hjl := j.isLt
    unfold RecoveryProjectionCold.input
    by_cases h37 : j = 37
    · subst h37
      rw [if_pos rfl, show projSlot d 37 = at_ d 160 (by omega) from Fin.ext rfl,
        hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old])), hA1_160]
    rw [if_neg h37]
    by_cases h65 : j = 65
    · subst h65
      rw [if_pos rfl, show projSlot d 65 = at_ d 161 (by omega) from Fin.ext rfl,
        hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old])), hA1_161]
    rw [if_neg h65]
    by_cases h28 : j = 28
    · subst h28
      rw [if_pos rfl, show projSlot d 28 = old d 106 from Fin.ext rfl,
        hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old])), hA1_106, hq]
    rw [if_neg h28]
    by_cases h104' : j = 104
    · subst h104'
      rw [if_pos rfl, show projSlot d 104 = old d 76 from Fin.ext rfl, hA2_76]
    rw [if_neg h104']
    have hv37 : j.val ≠ 37 := fun h => h37 (Fin.ext h)
    have hv65 : j.val ≠ 65 := fun h => h65 (Fin.ext h)
    have hv28 : j.val ≠ 28 := fun h => h28 (Fin.ext h)
    have hv104 : j.val ≠ 104 := fun h => h104' (Fin.ext h)
    have hval := (projSlot d j).isLt
    have hpv : (projSlot d j).val = projVal j.val := rfl
    rw [hA2_other _ (by rw [hpv]; unfold projVal; split_ifs <;> omega)
      (by rw [hpv]; unfold projVal; split_ifs <;> omega) (by rw [hpv]; unfold projVal; split_ifs <;> omega)
      (by rw [hpv]; unfold projVal; split_ifs <;> omega) (by rw [hpv]; unfold projVal; split_ifs <;> omega)]
    rw [hA1_other _ (by rw [hpv]; unfold projVal; split_ifs <;> omega)
      (by rw [hpv]; unfold projVal; split_ifs <;> omega) (by rw [hpv]; unfold projVal; split_ifs <;> omega)
      (by rw [hpv]; unfold projVal; split_ifs <;> omega)]
    simp only [A0, input]
    rw [if_neg (by rw [hpv]; unfold projVal; split_ifs <;> omega), if_neg (by rw [hpv]; unfold projVal; split_ifs <;> omega),
      if_neg (by rw [hpv]; unfold projVal; split_ifs <;> omega)]
  have h3 := hP.focus (projSlot d) (projSlot_injective d) A2 hin3
  set A3 := install (projSlot d) A2 P with hA3
  have hA3_other : ∀ i : Fin (uTapes d), (i.val < 78 ∨ 115 ≤ i.val) → i.val ≠ 160 → i.val ≠ 161 → i.val ≠ 76 →
      i.val ≠ 115 → i.val ≠ 153 → i.val ≠ 156 → (i.val < 229 ∨ 342 ≤ i.val) → A3 i = A2 i :=
    fun i a b c e f g h k => proj_other d A2 P i a b c e f g h k
  have hA3_153 : A3 (old d 153) = List.replicate R true := by
    rw [show old d 153 = projSlot d 109 from Fin.ext rfl, hA3, install_slot _ (projSlot_injective d), h109]
  -- full bound
  obtain ⟨F, hF, hFs, hFr, hFc⟩ := RecoveryFullBound.cold_run d R
  have hin4 : ∀ j, A3 (fullSlot d j) = RecoveryFullBound.input d R j := by
    intro j
    unfold RecoveryFullBound.input
    by_cases hs : j = RecoveryFullBound.sourceSlot d
    · subst hs
      rw [fullSlot_source, hA3_153]
      simp [RecoveryFullBound.sourceSlot, RecoveryFullBound.old]
    have hj0 : j.val ≠ 0 := fun he => hs (Fin.ext (by
      rw [he]; simp [RecoveryFullBound.sourceSlot, RecoveryFullBound.old]))
    rw [if_neg hj0]
    by_cases hr : j = RecoveryFullBound.rawSlot d
    · subst hr
      rw [fullSlot_raw, hA3_other _ (Or.inr (by simp [at_, old])) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
        (by simp [at_, old]) (Or.inl (by simp [at_, old])), hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
        (Or.inl (by simp [at_, old])), hA1_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old]))]
      simp [A0, input, old]
    by_cases hcmp : j = RecoveryFullBound.compareSlot d
    · subst hcmp
      rw [fullSlot_compare, hA3_other _ (Or.inr (by simp [at_, old])) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
        (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old])), hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
        (Or.inl (by simp [at_, old])), hA1_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old]))]
      simp [A0, input, old]
    have hf : fullSlot d j = ⟨342 + j.val, by unfold uTapes; omega⟩ := by
      simp only [fullSlot, if_neg hs, if_neg hr, if_neg hcmp]
    rw [hf, hA3_other _ (Or.inr (by dsimp only; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega))
      (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (Or.inr (by dsimp only; omega)),
      hA2_other _ (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (Or.inr (by first | (dsimp only; omega) | (simp; omega))),
      hA1_other _ (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (by first | (dsimp only; omega) | (simp; omega)) (Or.inr (by first | (dsimp only; omega) | (simp; omega)))]
    have n1 : ¬(342 + j.val = 158) := by omega
    have n2 : ¬(342 + j.val = 159) := by omega
    have n3 : ¬(342 + j.val = 179) := by omega
    simp only [A0, input, n1, n2, n3, if_false]
  have h4 := hF.focus (fullSlot d) (fullSlot_injective d) A3 hin4
  set A4 := install (fullSlot d) A3 F with hA4
  refine ⟨A4, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 (ClockJoin.join _ _ _ _ _ _ _ h3 h4)),
    ?_, ?_, ?_⟩
  · have hA4o : ∀ i : Fin 158, i.val ≠ 153 → i.val ≠ 155 → i.val ≠ 152 → A4 (old d i) = A3 (old d i) :=
      fun i a b c => full_other d A3 F (old d i) a b c (by simp only [old]; omega)
    have hA3o : ∀ i : Fin 158, (i.val < 78 ∨ 115 ≤ i.val) → i.val ≠ 76 → i.val ≠ 115 → i.val ≠ 153 →
        i.val ≠ 156 → A3 (old d i) = A2 (old d i) :=
      fun i a b c e f => hA3_other _ a (by simp only [old]; omega) (by simp only [old]; omega) b c e f
        (Or.inl (by simp only [old]; omega))
    have hA2o : ∀ i : Fin 158, i.val ≠ 154 → i.val ≠ 76 → i.val ≠ 77 → A2 (old d i) = A1 (old d i) :=
      fun i a b c => hA2_other _ (by simp only [old]; omega) a b c (Or.inl (by simp only [old]; omega))
    have hA1o : ∀ i : Fin 158, i.val ≠ 106 → i.val ≠ 70 → i.val ≠ 157 → A1 (old d i) = [] := by
      intro i a b c
      rw [hA1_other _ a b c (Or.inl (by simp only [old]; omega))]
      have hi := i.isLt
      simp only [A0, input, old]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hfields := cStream_eq w vals
    have hcl := unit_clauses_length w vals
    intro i
    unfold prepared RecoveryBoundedColdPrepared.input
    refine Fin.addCases (m := 153) (n := 5) (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (m := 116) (n := 37) (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (m := 78) (n := 38) (fun z => ?_) (fun z => ?_) j
        · simp only [Fin.addCases_left]
          have hz := z.isLt
          change A4 (old d ⟨z.val, by omega⟩) = RecoveryBoundedColdPrepared.shared B (DedupBytes.fields p) z
          unfold RecoveryBoundedColdPrepared.shared
          by_cases h70 : z = 70
          · subst h70
            rw [if_pos rfl, hA4o _ (by simp) (by simp) (by simp), hA3o _ (Or.inl (by simp)) (by simp)
              (by simp) (by simp) (by simp), hA2o _ (by simp) (by simp) (by simp),
              show old d ⟨(70 : Fin 78).val, by omega⟩ = old d 70 from rfl, hA1_70, hp, hfields]
          rw [if_neg h70]
          by_cases h76 : z = 76
          · subst h76
            rw [if_pos rfl, hA4o _ (by simp) (by simp) (by simp),
              show old d ⟨(76 : Fin 78).val, by omega⟩ = projSlot d 104 from Fin.ext rfl, hA3,
              install_slot _ (projSlot_injective d), h104]
          rw [if_neg h76]
          by_cases h77 : z = 77
          · subst h77
            rw [if_pos rfl, hA4o _ (by simp) (by simp) (by simp), hA3o _ (Or.inl (by simp)) (by simp)
              (by simp) (by simp) (by simp), show old d ⟨(77 : Fin 78).val, by omega⟩ = old d 77 from rfl,
              hA2_77]
          rw [if_neg h77]
          have v70 : z.val ≠ 70 := fun h => h70 (Fin.ext h)
          have v76 : z.val ≠ 76 := fun h => h76 (Fin.ext h)
          have v77 : z.val ≠ 77 := fun h => h77 (Fin.ext h)
          rw [hA4o _ (by simp only; omega) (by simp only; omega) (by simp only; omega),
            hA3o _ (Or.inl (by simp only; omega)) (by simp only; omega) (by simp only; omega) (by simp only; omega)
              (by simp only; omega),
            hA2o _ (by simp only; omega) (by simp only; omega) (by simp only; omega),
            hA1o _ (by simp only; omega) (by simp only; omega) (by simp only; omega)]
        · refine Fin.addCases (m := 37) (n := 1) (fun t => ?_) (fun t => ?_) z
          · simp only [Fin.addCases_left, Fin.addCases_right, RecoveryBoundedFixedRestart.extra]
            have ht := t.isLt
            change A4 (old d ⟨78 + t.val, by omega⟩) = _
            rw [hA4o _ (by simp only; omega) (by simp only; omega) (by simp only; omega),
              show old d ⟨78 + t.val, by omega⟩ = projSlot d (RecoveryProjectionCold.bankSlots t) from
                Fin.ext (by simp [old, projSlot, projVal, RecoveryProjectionCold.bankSlots, ht]),
              hA3, install_slot _ (projSlot_injective d), hbank]
          · have ht : t = 0 := Subsingleton.elim _ _
            subst ht
            change A4 (old d 115) = _
            rw [hA4o _ (by simp) (by simp) (by simp), show old d 115 = projSlot d 106 from Fin.ext rfl,
              hA3, install_slot _ (projSlot_injective d), h106]
            rfl
      · refine Fin.addCases (m := 36) (n := 1) (fun z => ?_) (fun z => ?_) j
        · simp only [Fin.addCases_left, Fin.addCases_right]
          have hz := z.isLt
          change A4 (old d ⟨116 + z.val, by omega⟩) = []
          rw [hA4o _ (by simp only; omega) (by simp only; omega) (by simp only; omega),
            hA3o _ (Or.inr (by simp only; omega)) (by simp only; omega) (by simp only; omega) (by simp only; omega)
              (by simp only; omega),
            hA2o _ (by simp only; omega) (by simp only; omega) (by simp only; omega),
            hA1o _ (by simp only; omega) (by simp only; omega) (by simp only; omega)]
        · have hz : z = 0 := Subsingleton.elim _ _
          subst hz
          change A4 (old d 152) = _
          rw [← fullSlot_compare, hA4, install_slot _ (fullSlot_injective d), hFc]
          rfl
    · fin_cases i
      · change A4 (old d 153) = _
        rw [← fullSlot_source, hA4, install_slot _ (fullSlot_injective d), hFs]
        rfl
      · change A4 (old d 154) = _
        rw [hA4o _ (by decide) (by decide) (by decide), hA3o _ (Or.inr (by decide)) (by decide) (by decide)
          (by decide) (by decide), hA2_154]
        rfl
      · change A4 (old d 155) = _
        rw [← fullSlot_raw, hA4, install_slot _ (fullSlot_injective d), hFr]
        rfl
      · change A4 (old d 156) = _
        rw [hA4o _ (by decide) (by decide) (by decide), show old d 156 = projSlot d 111 from Fin.ext rfl, hA3,
          install_slot _ (projSlot_injective d), h111]
        rfl
      · change A4 (old d 157) = _
        rw [hA4o _ (by decide) (by decide) (by decide), hA3o _ (Or.inr (by decide)) (by decide) (by decide)
          (by decide) (by decide), hA2o _ (by decide) (by decide) (by decide), hA1_157]
        rfl
  · rw [hA4, full_other _ _ _ _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]), hA3, proj_other _ _ _ _
      (Or.inr (by simp [at_, old])) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
      (Or.inl (by simp [at_, old])), hA2_other _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (Or.inl (by simp [at_, old])),
      hA1_158]
  · rw [hA4, full_other _ _ _ _ (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]), hA3, proj_other _ _ _ _
      (Or.inr (by simp [at_, old])) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old]) (by simp [at_, old])
      (Or.inl (by simp [at_, old])), hA2_179]

end NearCubicGates.Close.ENP.USupply
