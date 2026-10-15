import Proof.Wire_3_5.ListMachineFlatten
import Proof.Wire_3_5.ListConsumer
import Proof.Wire_3_5.RowsThr

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk

/-! ## Products and relabelling -/

/-- The product of two factored expressions. -/
def exprMul (V W : Expr) : Expr := V.flatMap fun t => W.map fun t' => (t.1 * t'.1, t.2 ++ t'.2)

theorem expr_eval_map_mul (c : ℤ) (fs : List Poly) (W : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (W.map fun t' => (c * t'.1, fs ++ t'.2)) ρ =
      c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod * IntExpression.eval W ρ := by
  induction W with
  | nil => simp [IntExpression.eval]
  | cons t' W ih =>
    obtain ⟨c', fs'⟩ := t'
    rw [List.map_cons, expr_eval_cons, expr_eval_cons, ih, List.map_append, List.prod_append]
    ring

theorem expr_eval_mul (V W : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (exprMul V W) ρ = IntExpression.eval V ρ * IntExpression.eval W ρ := by
  unfold exprMul
  induction V with
  | nil => simp [IntExpression.eval]
  | cons t V ih =>
    obtain ⟨c, fs⟩ := t
    rw [List.flatMap_cons, expr_eval_append, ih, expr_eval_map_mul, expr_eval_cons]
    ring

/-- The unit expression `1`. -/
def exprOne : Expr := [(1, [])]

theorem expr_eval_one (ρ : ℕ → Bool) : IntExpression.eval exprOne ρ = 1 := by simp [exprOne, IntExpression.eval]

/-- A population's coordinate `i` reads atom `lab i`. -/
def renamePoly (lab : ℕ → ℕ) (p : Poly) : Poly := p.map (List.map lab)

def renameExpr (lab : ℕ → ℕ) (V : Expr) : Expr := V.map fun t => (t.1, t.2.map (renamePoly lab))

theorem eval_renamePoly (lab : ℕ → ℕ) (p : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (renamePoly lab p) ρ = F2Poly.eval p (fun i => ρ (lab i)) := by
  unfold renamePoly
  induction p with
  | nil => rfl
  | cons m p ih => rw [List.map_cons, eval_cons, eval_cons, ih, List.all_map]; rfl

theorem expr_eval_rename (lab : ℕ → ℕ) (V : Expr) (ρ : ℕ → Bool) :
    IntExpression.eval (renameExpr lab V) ρ = IntExpression.eval V (fun i => ρ (lab i)) := by
  unfold renameExpr
  induction V with
  | nil => rfl
  | cons t V ih =>
    obtain ⟨c, fs⟩ := t
    rw [List.map_cons, expr_eval_cons, expr_eval_cons, ih]
    simp only [List.map_map, Function.comp_def, eval_renamePoly]

/-- An expression reads only the atoms below `L`. -/
def ExprAtomsLt (V : Expr) (L : ℕ) : Prop := ∀ t ∈ V, ∀ p ∈ t.2, AtomsLt p L

theorem eval_congr_atoms {p : Poly} {L : ℕ} (hp : AtomsLt p L) {ρ ρ' : ℕ → Bool} (h : ∀ i < L, ρ i = ρ' i) :
    F2Poly.eval p ρ = F2Poly.eval p ρ' := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    rw [eval_cons, eval_cons, ih (fun m' hm' => hp m' (List.mem_cons_of_mem _ hm'))]
    congr 1
    have hm : ∀ i ∈ m, ρ i = ρ' i := fun i hi => h i (hp m (List.mem_cons_self ..) i hi)
    clear hp ih
    induction m with
    | nil => rfl
    | cons i m ihm =>
      rw [List.all_cons, List.all_cons, hm i (List.mem_cons_self ..),
        ihm (fun j hj => hm j (List.mem_cons_of_mem _ hj))]

theorem expr_eval_congr_atoms {V : Expr} {L : ℕ} (hV : ExprAtomsLt V L) {ρ ρ' : ℕ → Bool} (h : ∀ i < L, ρ i = ρ' i) :
    IntExpression.eval V ρ = IntExpression.eval V ρ' := by
  induction V with
  | nil => rfl
  | cons t V ih =>
    obtain ⟨c, fs⟩ := t
    rw [expr_eval_cons, expr_eval_cons, ih (fun t ht => hV t (List.mem_cons_of_mem _ ht))]
    have hmap : (fs.map fun p => bitZ (F2Poly.eval p ρ)) = (fs.map fun p => bitZ (F2Poly.eval p ρ')) := by
      apply List.map_congr_left
      intro p hp
      rw [eval_congr_atoms (hV (c, fs) (List.mem_cons_self ..) p hp) h]
    rw [hmap]

/-! ## The amplified states read only their population -/

theorem atomsLt_nnot {p : Poly} {L : ℕ} (h : AtomsLt p L) : AtomsLt (nnot p) L := atomsLt_normalize (atomsLt_pnot h)

theorem visitPolys_atoms (P : FlatListParams) (e : P.FlatSeed) (L k s : ℕ) : AtomsLt (visitPolys P e L k s) L := by
  unfold visitPolys
  split_ifs
  · exact (stateRefN_size _ L s).2.1
  · exact atomsLt_pzero L

theorem rowFactors_atoms (Pv : ℕ → Poly) (L : ℕ) (hP : ∀ k, AtomsLt (Pv k) L) (o : ℕ) (r : List Bool) :
    ∀ p ∈ rowFactors Pv o r, AtomsLt p L := by
  induction r generalizing o with
  | nil => simp [rowFactors]
  | cons x r ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · split_ifs
      · exact hP o
      · exact atomsLt_nnot (hP o)
    · exact ih (o + 1) p hp

theorem majTerms_atoms (t θ : ℕ) (Pv : ℕ → Poly) (L : ℕ) (hP : ∀ k, AtomsLt (Pv k) L) :
    ExprAtomsLt (majTerms t θ Pv) L := by
  intro term hterm
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hterm
  exact rowFactors_atoms Pv L hP 0 r

theorem flatExprOf_atoms (P : FlatListParams) (e : P.FlatSeed) (L s : ℕ) : ExprAtomsLt (flatExprOf P e L s) L := by
  unfold flatExprOf flatExpr
  split_ifs
  · intro term hterm
    rcases List.mem_cons.mp hterm with rfl | hterm
    · simp
    · obtain ⟨i, _, hterm⟩ := List.mem_flatMap.mp hterm
      unfold exprNeg at hterm
      obtain ⟨term', hterm', rfl⟩ := List.mem_map.mp hterm
      exact majTerms_atoms _ _ _ L (fun k => visitPolys_atoms P e L k _) term' hterm'
  · exact majTerms_atoms _ _ _ L (fun k => visitPolys_atoms P e L k s)

/-- The amplified state of a population read through its labels. -/
theorem renamed_flat_eval (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (lab : ℕ → ℕ) (ρ : ℕ → Bool) (s : ℕ)
    (hs : s ≤ P.M) :
    IntExpression.eval (renameExpr lab (flatExprOf P e L s)) ρ =
      bitInt (decide (P.flatReport e (List.ofFn fun i : Fin L => ρ (lab i)) = s)) := by
  rw [expr_eval_rename, ← flatExprOf_eval P e L (fun i : Fin L => ρ (lab i)) s hs]
  apply expr_eval_congr_atoms (flatExprOf_atoms P e L s)
  intro i hi
  simp [ext, hi]

/-! ## C2h: the SYM joint state and row -/

/-- The populations of a SYM row: `a` circuits, each with a positive and a negative residual population
(sizes `Lp j`, `Lm j`, atom labels `labP j`, `labM j`). -/
structure SymPops (a : ℕ) where
  Lp : Fin a → ℕ
  Lm : Fin a → ℕ
  labP : Fin a → ℕ → ℕ
  labM : Fin a → ℕ → ℕ

/-- The populations' inputs at an atom assignment. -/
def SymPops.Zp {a : ℕ} (S : SymPops a) (ρ : ℕ → Bool) (j : Fin a) : List Bool := List.ofFn fun i : Fin (S.Lp j) => ρ (S.labP j i)
def SymPops.Zm {a : ℕ} (S : SymPops a) (ρ : ℕ → Bool) (j : Fin a) : List Bool := List.ofFn fun i : Fin (S.Lm j) => ρ (S.labM j i)

def symStateExpr (P : FlatListParams) (e : P.FlatSeed) {a : ℕ} (S : SymPops a)
    (τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1)) : Expr :=
  (List.finRange a).foldr (fun j acc => exprMul (renameExpr (S.labP j) (flatExprOf P e (S.Lp j) (τ j).1))
    (exprMul (renameExpr (S.labM j) (flatExprOf P e (S.Lm j) (τ j).2)) acc)) exprOne

theorem bitInt_and (x y : Bool) : bitInt (x && y) = bitInt x * bitInt y := by cases x <;> cases y <;> rfl

theorem symStateExpr_eval (P : FlatListParams) (e : P.FlatSeed) {a : ℕ} (S : SymPops a)
    (τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1)) (ρ : ℕ → Bool) :
    IntExpression.eval (symStateExpr P e S τ) ρ = bitInt (P.jointIndicator (S.Zp ρ) (S.Zm ρ) e τ) := by
  have hstep : ∀ l : List (Fin a), IntExpression.eval ((l.foldr (fun j acc => exprMul
      (renameExpr (S.labP j) (flatExprOf P e (S.Lp j) (τ j).1))
      (exprMul (renameExpr (S.labM j) (flatExprOf P e (S.Lm j) (τ j).2)) acc)) exprOne)) ρ =
        bitInt (decide (∀ j ∈ l, P.jointState (S.Zp ρ) (S.Zm ρ) e j = ((τ j).1.val, (τ j).2.val))) := by
    intro l
    induction l with
    | nil => simp [expr_eval_one, bitInt]
    | cons j l ih =>
      rw [List.foldr_cons, expr_eval_mul, expr_eval_mul, ih,
        renamed_flat_eval P e _ _ ρ _ (Nat.le_of_lt_succ (τ j).1.isLt),
        renamed_flat_eval P e _ _ ρ _ (Nat.le_of_lt_succ (τ j).2.isLt)]
      rw [← bitInt_and, ← bitInt_and]
      congr 1
      simp only [List.forall_mem_cons, FlatListParams.jointState, Prod.mk.injEq, SymPops.Zp, SymPops.Zm]
      cases h1 : decide (P.flatReport e (List.ofFn fun i : Fin (S.Lp j) => ρ (S.labP j i)) = (τ j).1) <;>
        cases h2 : decide (P.flatReport e (List.ofFn fun i : Fin (S.Lm j) => ρ (S.labM j i)) = (τ j).2) <;>
        simp_all
  unfold symStateExpr FlatListParams.jointIndicator
  rw [hstep]
  congr 1
  simp

def symRowExpr (G : Poly) (P : FlatListParams) (e : P.FlatSeed) {a : ℕ} (S : SymPops a)
    (τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1)) : Expr :=
  exprMul [(1, [G])] (symStateExpr P e S τ)

theorem symRowExpr_eval (G : Poly) (P : FlatListParams) (e : P.FlatSeed) {a : ℕ} (S : SymPops a)
    (τ : Fin a → Fin (P.M + 1) × Fin (P.M + 1)) (ρ : ℕ → Bool) :
    IntExpression.eval (symRowExpr G P e S τ) ρ =
      bitInt (F2Poly.eval G ρ && P.jointIndicator (S.Zp ρ) (S.Zm ρ) e τ) := by
  rw [symRowExpr, expr_eval_mul, symStateExpr_eval, bitInt_and]
  simp [IntExpression.eval, bitZ, bitInt]

/-! ## C2i: the THR radix states -/

/-- All digit-state pairs `(t^+, t^−)` with `t^± ≤ K`. -/
def pairsUpTo (K : ℕ) : List (ℕ × ℕ) := (List.range (K + 1)).flatMap fun a => (List.range (K + 1)).map fun b => (a, b)

/-- All signed digit tuples of length `n`. -/
def allTuples (K : ℕ) : ℕ → List (List (ℕ × ℕ))
  | 0 => [[]]
  | n + 1 => (pairsUpTo K).flatMap fun ab => (allTuples K n).map (ab :: ·)

/-- The factors of a tuple, from digit `o`: `P_{d,+,t_d^+}` and `P_{d,−,t_d^−}`. -/
def tupleFactors (Pp Pm : ℕ → ℕ → Poly) : ℕ → List (ℕ × ℕ) → List Poly
  | _, [] => []
  | o, ab :: tl => Pp o ab.1 :: Pm o ab.2 :: tupleFactors Pp Pm (o + 1) tl

/-- The signed radix value `Σ_d b_0^d(t_d^+ − t_d^−)` of a tuple, from digit `o`. -/
def tupleValue (b0 : ℕ) : ℕ → List (ℕ × ℕ) → ℤ
  | _, [] => 0
  | o, ab :: tl => (b0 : ℤ) ^ o * ((ab.1 : ℤ) - ab.2) + tupleValue b0 (o + 1) tl

def radixExpr (τ₀ K p b0 : ℕ) (Pp Pm : ℕ → ℕ → Poly) (s : ZMod p) : Expr :=
  ((allTuples K τ₀).filter fun tup => decide (((tupleValue b0 0 tup : ℤ) : ZMod p) = s)).map fun tup =>
    ((1 : ℤ), tupleFactors Pp Pm 0 tup)

theorem mem_pairsUpTo {K a b : ℕ} (ha : a ≤ K) (hb : b ≤ K) : (a, b) ∈ pairsUpTo K := by
  simp [pairsUpTo, List.mem_flatMap, List.mem_map, List.mem_range]; omega

theorem nodup_pairsUpTo (K : ℕ) : (pairsUpTo K).Nodup := by
  unfold pairsUpTo
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_range).map (fun b b' h => by simpa using h), ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
  intro a a' _ _ hne
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hx'
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b', _, h⟩ := List.mem_map.mp hx'
  exact hne (congrArg Prod.fst h).symm

theorem sum_select_nodup {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup) (x : α) (hx : x ∈ l) (h : α → ℤ) :
    (l.map fun y => if y = x then h y else 0).sum = h x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.nodup_cons.mp hl with ⟨hy, hl'⟩
    by_cases hyx : y = x
    · subst hyx
      rw [if_pos rfl]
      have : (l.map fun y' => if y' = y then h y' else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hv
        rw [if_neg (show y' ≠ y from fun he => hy (he ▸ hy'))]
      rw [this, add_zero]
    · rw [if_neg hyx, zero_add]
      exact ih hl' ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))

theorem sum_map_flatMap {α β : Type} (l : List α) (f : α → List β) (F : β → ℤ) :
    ((l.flatMap f).map F).sum = (l.map fun x => ((f x).map F).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem sum_tuples_select (K : ℕ) (Pp Pm : ℕ → ℕ → Poly) (ρ : ℕ → Bool) (tp tm : ℕ → ℕ) (n : ℕ) :
    ∀ (o : ℕ), (∀ d, d < o + n → tp d ≤ K ∧ tm d ≤ K) →
      (∀ d t, d < o + n → t ≤ K → F2Poly.eval (Pp d t) ρ = decide (t = tp d)) →
      (∀ d t, d < o + n → t ≤ K → F2Poly.eval (Pm d t) ρ = decide (t = tm d)) →
      ∀ (g : List (ℕ × ℕ) → ℤ),
      ((allTuples K n).map fun tup => g tup * ((tupleFactors Pp Pm o tup).map fun q => bitZ (F2Poly.eval q ρ)).prod).sum =
        g ((List.range n).map fun k => (tp (o + k), tm (o + k))) := by
  induction n with
  | zero => intro o _ _ _ g; simp [allTuples, tupleFactors]
  | succ n ih =>
    intro o hb hp hm g
    have ho : o < o + (n + 1) := by omega
    have ih' := ih (o + 1) (fun d hd => hb d (by omega)) (fun d t hd => hp d t (by omega))
      (fun d t hd => hm d t (by omega))
    simp only [allTuples]
    rw [sum_map_flatMap]
    have hpair : ∀ ab ∈ pairsUpTo K,
        (((allTuples K n).map (ab :: ·)).map fun tup =>
          g tup * ((tupleFactors Pp Pm o tup).map fun q => bitZ (F2Poly.eval q ρ)).prod).sum =
        if ab = (tp o, tm o) then g (ab :: (List.range n).map fun k => (tp (o + 1 + k), tm (o + 1 + k))) else 0 := by
      intro ab hab
      have hab' : ab.1 ≤ K ∧ ab.2 ≤ K := by
        obtain ⟨a, b⟩ := ab
        simp only [pairsUpTo, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hab
        obtain ⟨a', ha', b', hb', rfl, rfl⟩ := hab
        exact ⟨by omega, by omega⟩
      rw [List.map_map]
      have hfac : ∀ tl : List (ℕ × ℕ), ((tupleFactors Pp Pm o (ab :: tl)).map fun q => bitZ (F2Poly.eval q ρ)).prod =
          (if ab = (tp o, tm o) then 1 else 0) * ((tupleFactors Pp Pm (o + 1) tl).map fun q => bitZ (F2Poly.eval q ρ)).prod := by
        intro tl
        simp only [tupleFactors, List.map_cons, List.prod_cons, hp o ab.1 ho hab'.1, hm o ab.2 ho hab'.2]
        obtain ⟨a, b⟩ := ab
        by_cases h1 : a = tp o <;> by_cases h2 : b = tm o <;> simp [h1, h2, bitZ]
      have hsum : (((allTuples K n).map fun tl => g (ab :: tl) *
          ((tupleFactors Pp Pm o (ab :: tl)).map fun q => bitZ (F2Poly.eval q ρ)).prod)).sum =
          (if ab = (tp o, tm o) then 1 else 0) * g (ab :: (List.range n).map fun k => (tp (o + 1 + k), tm (o + 1 + k))) := by
        rw [← ih' (fun tl => g (ab :: tl)), ← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro tl _
        rw [hfac]
        ring
      simp only [Function.comp_def]
      rw [hsum]
      split_ifs <;> simp
    rw [List.map_congr_left hpair, sum_select_nodup _ (nodup_pairsUpTo K) (tp o, tm o)
      (mem_pairsUpTo (hb o ho).1 (hb o ho).2)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def]
    congr 3
    funext k
    rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem tupleValue_range (b0 : ℕ) (x y : ℕ → ℕ) (n : ℕ) :
    ∀ o, tupleValue b0 o ((List.range n).map fun k => (x (o + k), y (o + k))) =
      ∑ k ∈ range n, (b0 : ℤ) ^ (o + k) * ((x (o + k) : ℤ) - y (o + k)) := by
  induction n with
  | zero => intro o; rfl
  | succ n ih =>
    intro o
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, tupleValue, Finset.sum_range_succ']
    have := ih (o + 1)
    simp only [Function.comp_def, Nat.add_zero] at *
    have hshift : ((List.range n).map fun k => (x (o + (k + 1)), y (o + (k + 1)))) =
        ((List.range n).map fun k => (x (o + 1 + k), y (o + 1 + k))) := by
      apply List.map_congr_left; intro k _; rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [hshift, this]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem eval_filter_map_tuples (l : List (List (ℕ × ℕ))) (c : List (ℕ × ℕ) → Bool) (F : List (ℕ × ℕ) → List Poly)
    (ρ : ℕ → Bool) :
    IntExpression.eval ((l.filter c).map fun r => ((1 : ℤ), F r)) ρ =
      (l.map fun r => bitZ (c r) * ((F r).map fun q => bitZ (F2Poly.eval q ρ)).prod).sum := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    cases hc : c r
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]; simp [bitZ]
    · simp only [↓reduceIte, List.map_cons]
      rw [expr_eval_cons, ih]; simp [bitZ]

theorem radixExpr_eval (τ₀ K p b0 : ℕ) [NeZero p] (Pp Pm : ℕ → ℕ → Poly) (ρ : ℕ → Bool) (tp tm : Fin τ₀ → Fin (K + 1))
    (hp : ∀ (d : Fin τ₀) t, t ≤ K → F2Poly.eval (Pp d t) ρ = decide (t = tp d))
    (hm : ∀ (d : Fin τ₀) t, t ≤ K → F2Poly.eval (Pm d t) ρ = decide (t = tm d)) (s : ZMod p) :
    IntExpression.eval (radixExpr τ₀ K p b0 Pp Pm s) ρ =
      (Rows.radixState p b0 (fun (d : Fin τ₀) (t : Fin (K + 1)) => F2Poly.eval (Pp d t) ρ)
        (fun (d : Fin τ₀) (t : Fin (K + 1)) => F2Poly.eval (Pm d t) ρ) s : ℤ) := by
  let tpN : ℕ → ℕ := fun d => if h : d < τ₀ then tp ⟨d, h⟩ else 0
  let tmN : ℕ → ℕ := fun d => if h : d < τ₀ then tm ⟨d, h⟩ else 0
  rw [Rows.radixState_of_oneHot p b0 _ _ tp tm (fun d t => (hp d t (Nat.le_of_lt_succ t.isLt)).trans (by
      simp [Fin.ext_iff])) (fun d t => (hm d t (Nat.le_of_lt_succ t.isLt)).trans (by simp [Fin.ext_iff])) s]
  unfold radixExpr
  rw [eval_filter_map_tuples]
  rw [sum_tuples_select K Pp Pm ρ tpN tmN τ₀ 0
    (fun d hd => by simp only [tpN, tmN, dif_pos (show d < τ₀ by omega)]; exact ⟨Nat.le_of_lt_succ (tp _).isLt,
      Nat.le_of_lt_succ (tm _).isLt⟩)
    (fun d t hd ht => by simpa [tpN, dif_pos (show d < τ₀ by omega)] using hp ⟨d, by omega⟩ t ht)
    (fun d t hd ht => by simpa [tmN, dif_pos (show d < τ₀ by omega)] using hm ⟨d, by omega⟩ t ht)
    fun tup => bitZ (decide (((tupleValue b0 0 tup : ℤ) : ZMod p) = s))]
  rw [tupleValue_range b0 tpN tmN τ₀ 0]
  have hres : ((∑ k ∈ range τ₀, (b0 : ℤ) ^ (0 + k) * ((tpN (0 + k) : ℤ) - tmN (0 + k)) : ℤ) : ZMod p) =
      Rows.tupleResidue p b0 (fun d => (tp d : ℕ)) (fun d => (tm d : ℕ)) := by
    unfold Rows.tupleResidue
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [tpN, tmN, d.isLt]
  rw [hres]
  split_ifs with h <;> simp [bitZ, h]

end NearCubicWires.WireExponent3_5.ListMachine
