import Proof.Wire_3_5.StarPartition
import Proof.Wire_3_5.StarCarrierPopulation
import Proof.Wire_3_5.StarMixedScore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared.StarParams
open NearCubicWires Finset NearCubicWires.WireExponent3_5.Stars

variable (P : StarParams)

/-- The left-side coordinates. -/
abbrev SideL := {i : Fin P.n // P.centerSide i = true}

/-- The right-side coordinates. -/
abbrev SideR := {i : Fin P.n // ¬ P.centerSide i = true}

/-- The left half `z_L` of an input. -/
def leftPart (x : BitInput P.n) : P.SideL → Bool := fun i => x i.1

/-- The right half `z_R` of an input. -/
def rightPart (x : BitInput P.n) : P.SideR → Bool := fun i => x i.1

/-- The input with halves `z_L`, `z_R`. -/
def glue (xL : P.SideL → Bool) (xR : P.SideR → Bool) : BitInput P.n :=
  fun i => if h : P.centerSide i = true then xL ⟨i, h⟩ else xR ⟨i, h⟩

theorem glue_parts (x : BitInput P.n) : P.glue (P.leftPart x) (P.rightPart x) = x := by
  funext i; unfold glue leftPart rightPart; split_ifs <;> rfl

theorem leftPart_glue (xL : P.SideL → Bool) (xR : P.SideR → Bool) : P.leftPart (P.glue xL xR) = xL := by
  funext i; simp only [leftPart, glue, dif_pos i.2]

theorem rightPart_glue (xL : P.SideL → Bool) (xR : P.SideR → Bool) : P.rightPart (P.glue xL xR) = xR := by
  funext i; simp only [rightPart, glue, dif_neg i.2]

/-- Coordinatewise exclusive-or of two halves. -/
def xorHalf {α : Type} (a b : α → Bool) : α → Bool := fun i => xor (a i) (b i)

theorem leftPart_xorInput (x y : BitInput P.n) :
    P.leftPart (xorInput x y) = xorHalf (P.leftPart x) (P.leftPart y) := rfl

theorem rightPart_xorInput (x y : BitInput P.n) :
    P.rightPart (xorInput x y) = xorHalf (P.rightPart x) (P.rightPart y) := rfl

theorem xorHalf_false {α : Type} (a : α → Bool) : xorHalf a (fun _ => false) = a := by
  funext i; simp [xorHalf]

/-- The right errors vanish on the left half. -/
theorem leftPart_errorVector_right (v : P.Errors) :
    P.leftPart (P.errorVector P.rightBlock v) = fun _ => false := by
  funext i
  simp only [leftPart, errorVector, decide_eq_false_iff_not, not_exists, not_and]
  intro j i' _ h
  have := P.centerSide_rightBlock j i'
  rw [h, i.2] at this
  exact Bool.noConfusion this

/-- The left errors vanish on the right half. -/
theorem rightPart_errorVector_left (u : P.Errors) :
    P.rightPart (P.errorVector P.leftBlock u) = fun _ => false := by
  funext i
  simp only [rightPart, errorVector, decide_eq_false_iff_not, not_exists, not_and]
  intro j i' _ h
  have := P.centerSide_leftBlock j i'
  rw [h] at this
  exact i.2 this

theorem centerSide_rightBlock' (j : Fin (P.r / 2)) (i : Fin P.b) :
    ¬ P.centerSide (P.blockCoord (P.rightBlock j) i) = true := by
  rw [P.centerSide_rightBlock]; simp

/-- The coset conditions of the left blocks, on the left half. -/
def LeftOK (σ : P.Translation) (xL : P.SideL → Bool) : Prop :=
  ∀ j : Fin (P.r / 2),
    P.syndrome (fun i => xL ⟨P.blockCoord (P.leftBlock j) i, P.centerSide_leftBlock j i⟩) = σ (P.leftBlock j)

/-- The coset conditions of the right blocks, on the right half. -/
def RightOK (σ : P.Translation) (xR : P.SideR → Bool) : Prop :=
  ∀ j : Fin (P.r / 2),
    P.syndrome (fun i => xR ⟨P.blockCoord (P.rightBlock j) i, P.centerSide_rightBlock' j i⟩) = σ (P.rightBlock j)

instance (σ : P.Translation) : DecidablePred (P.LeftOK σ) := fun _ => by
  unfold LeftOK; infer_instance

instance (σ : P.Translation) : DecidablePred (P.RightOK σ) := fun _ => by
  unfold RightOK; infer_instance

theorem isCenter_iff_halves (σ : P.Translation) (c : BitInput P.n) :
    P.IsCenter σ c ↔ P.LeftOK σ (P.leftPart c) ∧ P.RightOK σ (P.rightPart c) := by
  constructor
  · intro h; exact ⟨fun j => h (P.leftBlock j), fun j => h (P.rightBlock j)⟩
  · rintro ⟨hl, hr⟩ J
    rcases P.block_cases J with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hl j
    · exact hr j

/-- The left half score `Σ_{i left} w_i x_i`. -/
def halfScoreL (g : NormalizedThresholdGate P.n) (xL : P.SideL → Bool) : ℤ :=
  ∑ i : P.SideL, g.weight i.1 * if xL i then 1 else 0

/-- The right half score `Σ_{i right} w_i x_i`. -/
def halfScoreR (g : NormalizedThresholdGate P.n) (xR : P.SideR → Bool) : ℤ :=
  ∑ i : P.SideR, g.weight i.1 * if xR i then 1 else 0

theorem gateScore_eq_halves (g : NormalizedThresholdGate P.n) (x : BitInput P.n) :
    gateScore g x = P.halfScoreL g (P.leftPart x) + P.halfScoreR g (P.rightPart x) :=
  (Fintype.sum_subtype_add_sum_subtype (fun i => P.centerSide i = true)
    (fun i => g.weight i * if x i then 1 else 0)).symm

/-- The left half scores `a_j(z_L)` of the four corners `c+u+v, c+u, c+v, c` at the error row `(u, v)`. -/
def cornerLeft (g : NormalizedThresholdGate P.n) (u : P.Errors) (xL : P.SideL → Bool) : Fin 4 → ℤ :=
  ![P.halfScoreL g (xorHalf xL (P.leftPart (P.errorVector P.leftBlock u))),
    P.halfScoreL g (xorHalf xL (P.leftPart (P.errorVector P.leftBlock u))),
    P.halfScoreL g xL, P.halfScoreL g xL]

/-- The right half scores `b_j(z_R)` of the four corners at the error row `(u, v)`. -/
def cornerRight (g : NormalizedThresholdGate P.n) (v : P.Errors) (xR : P.SideR → Bool) : Fin 4 → ℤ :=
  ![P.halfScoreR g (xorHalf xR (P.rightPart (P.errorVector P.rightBlock v))), P.halfScoreR g xR,
    P.halfScoreR g (xorHalf xR (P.rightPart (P.errorVector P.rightBlock v))), P.halfScoreR g xR]

theorem corners_eq (g : NormalizedThresholdGate P.n) (c : BitInput P.n) (u v : P.Errors) :
    corners g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) =
      fun j => decide (g.threshold ≤ P.cornerLeft g u (P.leftPart c) j + P.cornerRight g v (P.rightPart c) j) := by
  have hL := P.leftPart_errorVector_right v
  have hR := P.rightPart_errorVector_left u
  funext j
  fin_cases j
  · show g.eval (xorInput (xorInput c _) _) = _
    rw [eval_eq_decide, gateScore_eq_halves, leftPart_xorInput, leftPart_xorInput, rightPart_xorInput,
      rightPart_xorInput, hL, hR, xorHalf_false, xorHalf_false]; rfl
  · show g.eval (xorInput c _) = _
    rw [eval_eq_decide, gateScore_eq_halves, leftPart_xorInput, rightPart_xorInput, hR, xorHalf_false]; rfl
  · show g.eval (xorInput c _) = _
    rw [eval_eq_decide, gateScore_eq_halves, leftPart_xorInput, rightPart_xorInput, hL, xorHalf_false]; rfl
  · show g.eval c = _
    rw [eval_eq_decide, gateScore_eq_halves]; rfl

def cut (b : Bool) (θ a c : ℤ) : Bool := if b then decide (θ ≤ a + c) else decide (a + c ≤ θ - 1)

theorem cut_eq_true_iff (b : Bool) (θ a c : ℤ) : cut b θ a c = true ↔ decide (θ ≤ a + c) = b := by
  cases b <;> simp [cut]

/-- The corner pattern `π` holds at the halves `(z_L, z_R)`: all four weak inequalities. -/
def PatternHolds (π : Fin 4 → Bool) (g : NormalizedThresholdGate P.n) (u v : P.Errors) (xL : P.SideL → Bool)
    (xR : P.SideR → Bool) : Prop :=
  ∀ j, cut (π j) g.threshold (P.cornerLeft g u xL j) (P.cornerRight g v xR j) = true

instance (π : Fin 4 → Bool) (g : NormalizedThresholdGate P.n) (u v : P.Errors) (xL : P.SideL → Bool)
    (xR : P.SideR → Bool) : Decidable (P.PatternHolds π g u v xL xR) := by
  unfold PatternHolds; infer_instance

/-- A pattern holds exactly when it is the gate's corner pattern. -/
theorem patternHolds_iff (π : Fin 4 → Bool) (g : NormalizedThresholdGate P.n) (u v : P.Errors) (c : BitInput P.n) :
    P.PatternHolds π g u v (P.leftPart c) (P.rightPart c) ↔
      corners g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) = π := by
  rw [P.corners_eq]
  simp only [PatternHolds, cut_eq_true_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

def rowCount (σ : P.Translation) (g : NormalizedThresholdGate P.n) (u v : P.Errors) : ℕ :=
  ∑ π ∈ univ.filter (fun π : Fin 4 → Bool => cornerDelta π ≠ 0),
    (((univ.filter (P.LeftOK σ)) ×ˢ (univ.filter (P.RightOK σ))).filter
      (fun p => P.PatternHolds π g u v p.1 p.2)).card

theorem rowCount_eq (σ : P.Translation) (g : NormalizedThresholdGate P.n) (u v : P.Errors) :
    P.rowCount σ g u v = (univ.filter fun c : BitInput P.n => P.IsCenter σ c ∧
      mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0).card := by
  classical
  set eL := P.errorVector P.leftBlock u
  set eR := P.errorVector P.rightBlock v
  set OK := (univ.filter (P.LeftOK σ)) ×ˢ (univ.filter (P.RightOK σ))
  set f : (P.SideL → Bool) × (P.SideR → Bool) → (Fin 4 → Bool) := fun p => corners g.eval (P.glue p.1 p.2) eL eR
  set S := OK.filter fun p => cornerDelta (f p) ≠ 0
  -- centers ↔ halves
  have hA : (univ.filter fun c : BitInput P.n => P.IsCenter σ c ∧ mixedDifference g.eval c eL eR ≠ 0).card =
      S.card := by
    apply Finset.card_nbij' (fun c => (P.leftPart c, P.rightPart c)) (fun p => P.glue p.1 p.2)
    · intro c hc
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc
      simp only [S, OK, f, coe_filter, mem_product, mem_filter, mem_univ, true_and, Set.mem_setOf_eq, glue_parts]
      exact ⟨(P.isCenter_iff_halves σ c).mp hc.1, hc.2⟩
    · intro p hp
      simp only [S, OK, f, coe_filter, mem_product, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      refine ⟨(P.isCenter_iff_halves σ _).mpr ?_, hp.2⟩
      rw [leftPart_glue, rightPart_glue]; exact hp.1
    · intro c _; exact P.glue_parts c
    · intro p _; simp [leftPart_glue, rightPart_glue]
  -- split by the corner pattern
  have hB : S.card = ∑ π ∈ univ.filter (fun π : Fin 4 → Bool => cornerDelta π ≠ 0),
      (S.filter fun p => f p = π).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    simp only [S, coe_filter, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact hp.2
  rw [hA, hB]
  unfold rowCount
  apply Finset.sum_congr rfl
  intro π hπ
  simp only [mem_filter, mem_univ, true_and] at hπ
  congr 1
  ext p
  have hp := P.patternHolds_iff π g u v (P.glue p.1 p.2)
  rw [leftPart_glue, rightPart_glue] at hp
  have hS : p ∈ S ↔ p ∈ OK ∧ cornerDelta (f p) ≠ 0 := mem_filter
  rw [mem_filter, mem_filter, hp, hS]
  constructor
  · intro h; exact ⟨⟨h.1, by rw [show f p = π from h.2]; exact hπ⟩, h.2⟩
  · intro h; exact ⟨h.1.1, h.2⟩

def objective (σ : P.Translation) (pops : List (ℚ × Carrier P.n)) : ℚ :=
  (pops.map fun p => p.1 * ∑ x, (inputPopulation P σ p.2 x : ℚ)).sum / 2 ^ P.n

def starObjectiveRef (σ : P.Translation) (pops : List (ℚ × Carrier P.n)) : ℚ :=
  (pops.map fun p => p.1 * (p.2.map fun g => ∑ u : P.Errors, ∑ v : P.Errors, (P.rowCount σ g u v : ℚ)).sum).sum /
    2 ^ P.n

/-- One atom's summed population over the inputs is its row counts. -/
theorem sum_atomResidual_eq (σ : P.Translation) (g : NormalizedThresholdGate P.n) :
    (∑ x, (Carrier.atomResidual g (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
        (P.errorVector P.rightBlock (P.rightErrors σ x)) : ℚ)) =
      ∑ u : P.Errors, ∑ v : P.Errors, (P.rowCount σ g u v : ℚ) := by
  rw [P.sum_eq_sum_cells σ]
  have h1 : ∀ c ∈ univ.filter (P.IsCenter σ), ∀ u v : P.Errors,
      (Carrier.atomResidual g (P.center σ (P.point c u v))
        (P.errorVector P.leftBlock (P.leftErrors σ (P.point c u v)))
        (P.errorVector P.rightBlock (P.rightErrors σ (P.point c u v))) : ℚ) =
      if mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0 then 1 else 0 := by
    intro c hc u v
    have hc' : P.IsCenter σ c := (mem_filter.mp hc).2
    rw [P.center_point hc', P.leftErrors_point hc', P.rightErrors_point hc', atomResidual_star_eq]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => h1 c hc u v]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  rw [P.rowCount_eq, ← Finset.filter_filter, Finset.card_filter]
  push_cast; rfl

/-- One carrier's summed population over the inputs is the sum of its atoms' row counts. -/
theorem sum_inputPopulation_eq (σ : P.Translation) (X : Carrier P.n) :
    (∑ x, (inputPopulation P σ X x : ℚ)) =
      (X.map fun g => ∑ u : P.Errors, ∑ v : P.Errors, (P.rowCount σ g u v : ℚ)).sum := by
  induction X with
  | nil => simp [inputPopulation, Carrier.population]
  | cons g X ih =>
    have hsplit : ∀ x, (inputPopulation P σ (g :: X) x : ℚ) =
        (Carrier.atomResidual g (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
          (P.errorVector P.rightBlock (P.rightErrors σ x)) : ℚ) + (inputPopulation P σ X x : ℚ) := by
      intro x; simp [inputPopulation, Carrier.population]
    simp only [hsplit, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih, P.sum_atomResidual_eq]

/-- **The reference computes the objective exactly**: rows × gates × corner patterns agree with the enumeration of
the inputs. -/
theorem objective_eq_ref (σ : P.Translation) (pops : List (ℚ × Carrier P.n)) :
    P.objective σ pops = P.starObjectiveRef σ pops := by
  unfold objective starObjectiveRef
  congr 2
  apply List.map_congr_left
  intro p _
  rw [P.sum_inputPopulation_eq]

theorem sum_list_map_sum {ι α : Type} [Fintype ι] (l : List α) (F : ι → α → ℝ) :
    (∑ i, (l.map (F i)).sum) = (l.map fun a => ∑ i, F i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem list_sum_mul_mul {α : Type} (l : List α) (g : α → ℝ) (a b : ℝ) :
    a * (l.map g).sum * b = (l.map fun x => a * g x * b).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- The objective in `ℝ`. -/
theorem objective_cast (σ : P.Translation) (pops : List (ℚ × Carrier P.n)) :
    (P.objective σ pops : ℝ) =
      (pops.map fun p => (p.1 : ℝ) * ∑ x, (inputPopulation P σ p.2 x : ℝ)).sum / 2 ^ P.n := by
  unfold objective
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map]
  congr 2
  apply List.map_congr_left
  intro p _
  simp

theorem sum_objective (pops : List (ℚ × Carrier P.n)) :
    (∑ σ : P.Translation, (P.objective σ pops : ℝ)) =
      (Fintype.card P.Translation : ℝ) * (pops.map fun p => (p.1 : ℝ) * Carrier.popMean P p.2).sum := by
  simp only [objective_cast]
  rw [← Finset.sum_div]
  have hsw : (∑ σ : P.Translation, (pops.map fun p => (p.1 : ℝ) * ∑ x, (inputPopulation P σ p.2 x : ℝ)).sum) =
      (pops.map fun p => (p.1 : ℝ) * ∑ σ : P.Translation, ∑ x, (inputPopulation P σ p.2 x : ℝ)).sum := by
    rw [sum_list_map_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    rw [Finset.mul_sum]
  rw [hsw]
  have hX : ∀ X : Carrier P.n, (∑ σ : P.Translation, ∑ x, (inputPopulation P σ X x : ℝ)) =
      ∑ c, ∑ u : P.Errors, ∑ v : P.Errors, (Carrier.starPopulation P X c u v : ℝ) :=
    fun X => P.sum_translations_inputs
      (fun c u v => (Carrier.population X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) : ℝ))
  simp only [hX]
  have hT : (Fintype.card P.Translation : ℝ) = (Fintype.card P.Errors : ℝ) ^ 2 := by
    have h1 := P.card_translation
    have h2 := P.card_cell
    rw [Fintype.card_prod] at h2
    rw [sq]; exact_mod_cast h1.trans h2.symm
  have h2n : (0 : ℝ) < 2 ^ P.n := by positivity
  have hE : (0 : ℝ) < (Fintype.card P.Errors : ℝ) ^ 2 := by
    have : 0 < Fintype.card P.Errors := Fintype.card_pos
    positivity
  rw [div_eq_iff h2n.ne', list_sum_mul_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Carrier.popMean]
  rw [hT]; field_simp

theorem exists_translation_le (pops : List (ℚ × Carrier P.n)) (hp : ∀ p ∈ pops, 0 ≤ p.1) :
    ∃ σ : P.Translation, (P.objective σ pops : ℝ) ≤
      P.popRate * (pops.map fun p => (p.1 : ℝ) * (Carrier.wires p.2 : ℝ)).sum := by
  set bound := P.popRate * (pops.map fun p => (p.1 : ℝ) * (Carrier.wires p.2 : ℝ)).sum
  have hmean : (pops.map fun p => (p.1 : ℝ) * Carrier.popMean P p.2).sum ≤ bound := by
    have := weighted_popMean_le P (pops.map fun p => ((p.1 : ℝ), p.2))
      (fun x hx => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
        show (0 : ℝ) ≤ (p.1 : ℝ)
        exact_mod_cast hp p hp')
    rw [List.map_map, List.map_map] at this
    exact this
  have hsum : (∑ σ : P.Translation, (P.objective σ pops : ℝ)) ≤ ∑ _σ : P.Translation, bound := by
    rw [P.sum_objective, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨σ, hσ⟩

theorem minimizer_le (pops : List (ℚ × Carrier P.n)) (hp : ∀ p ∈ pops, 0 ≤ p.1) (σ₀ : P.Translation)
    (hmin : ∀ σ, P.starObjectiveRef σ₀ pops ≤ P.starObjectiveRef σ pops) :
    (P.objective σ₀ pops : ℝ) ≤ P.popRate * (pops.map fun p => (p.1 : ℝ) * (Carrier.wires p.2 : ℝ)).sum := by
  obtain ⟨σ, hσ⟩ := P.exists_translation_le pops hp
  have h : P.objective σ₀ pops ≤ P.objective σ pops := by
    rw [P.objective_eq_ref, P.objective_eq_ref]; exact hmin σ
  exact le_trans (by exact_mod_cast h) hσ

end NearCubicWires.WireExponent3_5.Shared.StarParams
