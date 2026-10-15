import Proof.Gates.TabMachine.Mono3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- The tuples of children of a monomial's occurrences (stored largest variable first) at the inner point `c`. -/
def monoTuples (c : ℕ) (os : List Occ) : List (List (List ℤ)) := tuples (os.reverse.map fun o => o.kids c)

/-- The side conditions of one monomial at the inner point `c`: its block sits at `p` (count `m = |os|`), every
occurrence step meets `StepOK` within cost `CS`, the stacking values fit `Wd`, `cap` and `B` are large enough. -/
structure MonoOK (cap W s k Wd CS B : ℕ) (xs : List ℕ) (p c : ℕ) (os : List Occ) (out : List Bool) (g : ℕ) :
    Prop where
  hp : p < xs.length
  hxp : xs[p] = os.length
  hm : os.length < 2 ^ (W + 1)
  cap0 : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * p + xs[p] + 2 ≤ cap
  hos : ∀ o ∈ os, o.outW.length = s
  step : ∀ i (hi : i < os.length),
    StepOK cap W s k xs (posOf (p + 1) os i) c os[i] (tupF c (os.take i)) (i * (s + 1))
  cost : ∀ i (hi : i < os.length),
    occStepCost W s k xs (posOf (p + 1) os i) c os[i] (tupF c (os.take i)).length (i * (s + 1)) ≤ CS
  capL : 2 * os.length ≤ cap
  bound : ∀ ls ∈ monoTuples c os, (magL ls + 1) ^ (os.length + 1) < 2 ^ Wd
  hB : os.length * (s + 1) + (monoTuples c os).length + s + 1 + os.length ≤ B
  hBc : B ≤ cap
  capS : ((fieldNums ((monoTuples c os).map List.flatten)).length + 1) * (2 * (Wd + 1) + 1) +
      2 * (fieldNums ((monoTuples c os).map List.flatten)).length + 2 * os.length + 2 * (os.length * (s + 1)) +
      (monoTuples c os).length * (os.length * (s + 1)) + 2 * (s + 1) + os.length * (s + 1) + g +
      (monoTuples c os).length + 1 + 2 * (monoTuples c os).length ≤ cap
  capO : out.length + (monoTuples c os).length * ((s + 2) * (2 * (Wd + 1) + 1)) + 1 ≤ cap

section MonoStep
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def monoStep : WMX ns nr := .seq (monoPre Z Y) (.seq (occLoop Z Y) (monoStack Z Y))

def monoStepCost (W s Wd CS B p m F T : ℕ) : ℕ :=
  monoPreCost W p m + 1 + (m * (CS + 8) + 7 * m + 3 + 1 + monoStackCost Wd s m F T B)

/-- The streams one monomial may change. -/
def monoIdx : List (Fin 64) := [47, 31] ++ stepIdx ++ stackIdx

theorem monoStep_spec (cap W s k Wd CS B : ℕ) (hs1 : 1 ≤ s) (hWd : Wd + 1 = (s + 1) * (W + 1)) (hWd1 : 1 ≤ Wd)
    (xs : List ℕ) (c : ℕ) (coef : ℤ) (out L0 : List Bool) (g p : ℕ) (os : List Occ) (σ : WState ns nr)
    (h : MonoRest Z Y cap W s k xs c coef out L0 g p σ) (hok : MonoOK cap W s k Wd CS B xs p c os out g) :
    Runs cap (monoStep Z Y) σ (monoStepCost W s Wd CS B p os.length
        (fieldNums ((monoTuples c os).map List.flatten)).length (monoTuples c os).length) (fun τ =>
      MonoRest Z Y cap W s k xs c coef (out ++ (monoTuples c os).flatMap (cutRecs Wd s coef)) L0
        (g + (monoTuples c os).length) (posOf (p + 1) os os.length) τ ∧
      SameExcept σ τ (monoIdx.map Z) [Y 77, Y 74, Y 56]) := by
  have h1 := monoPre_spec Z Y cap W s k xs c coef out L0 g p σ h hok.hp (by rw [hok.hxp]; exact hok.hm) hok.cap0
  rw [hok.hxp] at h1
  refine Runs.seq h1 fun τ1 h1' => ?_
  obtain ⟨g1, a98, a77, a47, ha31, f1⟩ := h1'
  have st1 : ∀ i : Fin 64, i ∉ ([47, 31] : List (Fin 64)) → τ1.st (Z i) = σ.st (Z i) ∧ τ1.sh (Z i) = σ.sh (Z i) :=
    fun i hi => fr_st Z f1 i hi
  have v1 : ∀ r : Fin 112, r ∉ ([98, 77, 47] : List (Fin 112)) → τ1.val (Y r) = σ.val (Y r) :=
    fun r hr => fr_val Y f1 r hr
  obtain ⟨jx, hpg⟩ := h.pg
  have h2 := occLoop_spec Z Y cap W s k CS hs1 τ1 xs jx (p + 1) c os g1
    (by rw [(st1 46 (by decide)).1]; exact hpg) (by rw [(st1 46 (by decide)).2]; exact h.pgh) a77
    ⟨by rw [(st1 54 (by decide)).1]; exact h.cx.1, by rw [(st1 54 (by decide)).2]; exact h.cx.2⟩ ha31
    (by rw [v1 44 (by decide)]; exact h.r44) a47 a98 (by rw [v1 99 (by decide)]; exact h.r99) hok.hos hok.step
    hok.cost hok.capL
  refine Runs.seq h2 fun τ2 h2' => ?_
  obtain ⟨⟨g2, ⟨j2, ht2⟩, b77, b44, b47, f2⟩, b98, b99⟩ := h2'
  have st2 : ∀ i : Fin 64, i ∉ stepIdx → τ2.st (Z i) = τ1.st (Z i) ∧ τ2.sh (Z i) = τ1.sh (Z i) :=
    fun i hi => f2.1 _ (by rw [mem_map_emb]; exact hi)
  have v2 : ∀ r : Fin 112, r ∉ ([77, 44, 47, 98, 99] : List (Fin 112)) → τ2.val (Y r) = τ1.val (Y r) :=
    fun r hr => fr_val Y f2 r hr
  have htake : os.take os.length = os := List.take_of_length_le le_rfl
  rw [htake, tupF_eq] at ht2 b47
  have hm : ∀ ls ∈ monoTuples c os, ls.length = os.length := fun ls hls => by
    rw [mem_tuples_length _ ls hls]; simp
  have hl : ∀ ls ∈ monoTuples c os, ∀ l ∈ ls, l.length = s + 1 := by
    intro ls hls l hl
    obtain ⟨L, hL, hlL⟩ := mem_tuples_mem _ ls hls l hl
    simp only [List.mem_map, List.mem_reverse] at hL
    obtain ⟨o, ho, rfl⟩ := hL
    rw [kids_length o c l hlL, hok.hos o ho]
  have hfit : ∀ o ∈ os, ∀ kid ∈ o.kids c, ∀ y ∈ kid, y.natAbs < 2 ^ W := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    exact (hok.step i hi).fit
  have hW1 : 2 ^ (W + 1) ≤ 2 ^ (Wd + 1) := Nat.pow_le_pow_right (by norm_num) (by rw [hWd]; nlinarith)
  have hfl : ∀ x ∈ fieldNums ((monoTuples c os).map List.flatten), x < 2 ^ (Wd + 1) := by
    intro x hx
    have := tupF_fields c W os hfit x (by rw [tupF_eq]; exact hx)
    omega
  have e43 : τ2.st (Z 43) = σ.st (Z 43) ∧ τ2.sh (Z 43) = σ.sh (Z 43) := by
    rw [(st2 43 (by decide)).1, (st2 43 (by decide)).2]; exact st1 43 (by decide)
  have e34 : τ2.st (Z 34) = σ.st (Z 34) ∧ τ2.sh (Z 34) = σ.sh (Z 34) := by
    rw [(st2 34 (by decide)).1, (st2 34 (by decide)).2]; exact st1 34 (by decide)
  have h3 := monoStack_spec Z Y cap W s k Wd os.length hWd hWd1 τ2 coef out L0 g (monoTuples c os) j2 g2 ht2 b44
    (by rw [b47, List.length_map]; rfl) b98
    ⟨by rw [e43.1]; exact h.coef.1, by rw [e43.2]; exact h.coef.2⟩
    ⟨by rw [e34.1]; exact h.cut.1, by rw [e34.2]; exact h.cut.2.1,
      by rw [v2 56 (by decide), v1 56 (by decide)]; exact h.cut.2.2⟩
    (by rw [v2 74 (by decide), v1 74 (by decide)]; exact h.gc) hm hl hfl hok.bound B hok.hB hok.hBc hok.capS hok.capO
  refine h3.post fun τ h3' => ?_
  obtain ⟨g3, c44, c47, c98, cO, cg, f3⟩ := h3'
  have st3 : ∀ i : Fin 64, i ∉ stackIdx → τ.st (Z i) = τ2.st (Z i) ∧ τ.sh (Z i) = τ2.sh (Z i) :=
    fun i hi => f3.1 _ (by rw [mem_map_emb]; exact hi)
  have v3 : ∀ r : Fin 112, r ∉ ([56, 74, 44, 47, 98] : List (Fin 112)) → τ.val (Y r) = τ2.val (Y r) :=
    fun r hr => fr_val Y f3 r hr
  have stall : ∀ i : Fin 64, i ∉ monoIdx → τ.st (Z i) = σ.st (Z i) ∧ τ.sh (Z i) = σ.sh (Z i) := by
    intro i hi
    have n1 : i ∉ ([47, 31] : List (Fin 64)) := fun hm => hi (by unfold monoIdx; simp only [List.mem_append]; tauto)
    have n2 : i ∉ stepIdx := fun hm => hi (by unfold monoIdx; simp only [List.mem_append]; tauto)
    have n3 : i ∉ stackIdx := fun hm => hi (by unfold monoIdx; simp only [List.mem_append]; tauto)
    rw [(st3 i n3).1, (st3 i n3).2, (st2 i n2).1, (st2 i n2).2]; exact st1 i n1
  refine ⟨⟨g3, c98, ?_, c44, c47, ⟨jx, ?_⟩, ?_, ?_, ?_, cO, cg, ?_⟩, ?_⟩
  · rw [v3 99 (by decide)]; exact b99
  · rw [(stall 46 (by decide)).1]; exact hpg
  · rw [(stall 46 (by decide)).2]; exact h.pgh
  · exact ⟨by rw [(stall 54 (by decide)).1]; exact h.cx.1, by rw [(stall 54 (by decide)).2]; exact h.cx.2⟩
  · exact ⟨by rw [(stall 43 (by decide)).1]; exact h.coef.1, by rw [(stall 43 (by decide)).2]; exact h.coef.2⟩
  · rw [v3 77 (by decide)]; exact b77
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [f3.2.2, f2.2.2, f1.2.2]⟩
    · by_cases hz : ∃ i, Z i = x
      · obtain ⟨i, rfl⟩ := hz
        exact stall i (fun hm => hx (by rw [mem_map_emb]; exact hm))
      · have n1 : x ∉ ([47, 31] : List (Fin 64)).map Z := fun hm => hz (by
          obtain ⟨i, _, e⟩ := List.mem_map.mp hm; exact ⟨i, e⟩)
        have n2 : x ∉ stepIdx.map Z := fun hm => hz (by
          obtain ⟨i, _, e⟩ := List.mem_map.mp hm; exact ⟨i, e⟩)
        have n3 : x ∉ stackIdx.map Z := fun hm => hz (by
          obtain ⟨i, _, e⟩ := List.mem_map.mp hm; exact ⟨i, e⟩)
        rw [(f3.1 x n3).1, (f3.1 x n3).2, (f2.1 x n2).1, (f2.1 x n2).2]; exact f1.1 x n1
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases hy : ∃ i, Y i = r
      · obtain ⟨i, rfl⟩ := hy
        have n77 : i ≠ 77 := fun e => hr.1 (by rw [e])
        have n74 : i ≠ 74 := fun e => hr.2.1 (by rw [e])
        have n56 : i ≠ 56 := fun e => hr.2.2 (by rw [e])
        by_cases hc : i ∈ ([44, 47, 98, 99] : List (Fin 112))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl
          · rw [c44]; exact h.r44.symm
          · rw [c47]; exact h.r47.symm
          · rw [c98]; exact h.r98.symm
          · rw [v3 99 (by decide), b99]; exact h.r99.symm
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
          have m3 : i ∉ ([56, 74, 44, 47, 98] : List (Fin 112)) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n56, n74, hc.1, hc.2.1, hc.2.2.1⟩
          have m2 : i ∉ ([77, 44, 47, 98, 99] : List (Fin 112)) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n77, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
          have m1 : i ∉ ([98, 77, 47] : List (Fin 112)) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hc.2.2.1, n77, hc.2.1⟩
          rw [v3 i m3, v2 i m2, v1 i m1]
      · have n : ∀ i, r ≠ Y i := fun i e => hy ⟨i, e.symm⟩
        rw [f3.2.1 r (by simp [n]), f2.2.1 r (by simp [n]), f1.2.1 r (by simp [n])]

end MonoStep

end NearCubicGates.Close.TabMachine
