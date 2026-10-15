import Proof.Wire_3_5.SeedFixSampObjective

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
open Finset

abbrev SExpr := IntExpression ℕ

theorem seval_nil (ρ : ℕ → Bool) : IntExpression.eval ([] : SExpr) ρ = 0 := rfl

theorem seval_cons (c : ℤ) (fs : List (F2Poly ℕ)) (V : SExpr) (ρ : ℕ → Bool) :
    IntExpression.eval ((c, fs) :: V) ρ = c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod + IntExpression.eval V ρ := by
  simp [IntExpression.eval]

theorem seval_append (V W : SExpr) (ρ : ℕ → Bool) :
    IntExpression.eval (V ++ W) ρ = IntExpression.eval V ρ + IntExpression.eval W ρ := by
  simp [IntExpression.eval]

theorem seval_flatMap {β : Type} (l : List β) (f : β → SExpr) (ρ : ℕ → Bool) :
    IntExpression.eval (l.flatMap f) ρ = (l.map fun b => IntExpression.eval (f b) ρ).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, seval_append, ih, List.map_cons, List.sum_cons]

theorem prod_map_flatMap {β γ : Type} (l : List β) (f : β → List γ) (g : γ → ℤ) :
    ((l.flatMap f).map g).prod = (l.map fun b => ((f b).map g).prod).prod := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_cons, List.prod_append, ih]

/-! ## Products of expressions -/

def smul (V W : SExpr) : SExpr := V.flatMap fun t => W.map fun t' => (t.1 * t'.1, t.2 ++ t'.2)

theorem seval_map_mul (c : ℤ) (fs : List (F2Poly ℕ)) (W : SExpr) (ρ : ℕ → Bool) :
    IntExpression.eval (W.map fun t' => (c * t'.1, fs ++ t'.2)) ρ =
      c * (fs.map fun p => bitZ (F2Poly.eval p ρ)).prod * IntExpression.eval W ρ := by
  induction W with
  | nil => simp [IntExpression.eval]
  | cons t' W ih =>
    obtain ⟨c', fs'⟩ := t'
    rw [List.map_cons, seval_cons, seval_cons, ih, List.map_append, List.prod_append]
    ring

theorem seval_smul (V W : SExpr) (ρ : ℕ → Bool) :
    IntExpression.eval (smul V W) ρ = IntExpression.eval V ρ * IntExpression.eval W ρ := by
  unfold smul
  induction V with
  | nil => simp [IntExpression.eval]
  | cons t V ih =>
    obtain ⟨c, fs⟩ := t
    rw [List.flatMap_cons, seval_append, ih, seval_map_mul, seval_cons]
    ring

/-- **The product fold**: `A` times every expression of `L`, left to right. -/
def sfold (A : SExpr) (L : List SExpr) : SExpr := L.foldl smul A

theorem seval_sfold (ρ : ℕ → Bool) : ∀ (L : List SExpr) (A : SExpr),
    IntExpression.eval (sfold A L) ρ = IntExpression.eval A ρ * (L.map fun V => IntExpression.eval V ρ).prod
  | [], A => by simp [sfold]
  | V :: L, A => by
    show IntExpression.eval (sfold (smul A V) L) ρ = _
    rw [seval_sfold ρ L, seval_smul, List.map_cons, List.prod_cons]
    ring

/-! ## Factors per term -/

/-- Every term has exactly `m` factors. -/
def Uniform (V : SExpr) (m : ℕ) : Prop := ∀ t ∈ V, t.2.length = m

theorem Uniform.smul {V W : SExpr} {a b : ℕ} (hV : Uniform V a) (hW : Uniform W b) : Uniform (smul V W) (a + b) := by
  intro t ht
  unfold SeedFix.smul at ht
  obtain ⟨x, hx, hxt⟩ := List.mem_flatMap.mp ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxt
  simp [hV x hx, hW y hy]

theorem Uniform.sfold (f : SExpr → ℕ) : ∀ (L : List SExpr) (A : SExpr) (a : ℕ), Uniform A a →
    (∀ V ∈ L, Uniform V (f V)) → Uniform (SeedFix.sfold A L) (a + (L.map f).sum)
  | [], A, a, hA, _ => by simpa [SeedFix.sfold] using hA
  | V :: L, A, a, hA, hL => by
    show Uniform (SeedFix.sfold (SeedFix.smul A V) L) _
    have h := Uniform.sfold f L (SeedFix.smul A V) (a + f V) (hA.smul (hL V List.mem_cons_self))
      (fun W hW => hL W (List.mem_cons_of_mem _ hW))
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc]
    exact h

theorem Uniform.append {V W : SExpr} {m : ℕ} (hV : Uniform V m) (hW : Uniform W m) : Uniform (V ++ W) m := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hV t h
  · exact hW t h

theorem Uniform.flatMap {β : Type} (l : List β) (f : β → SExpr) (m : ℕ) (h : ∀ b ∈ l, Uniform (f b) m) :
    Uniform (l.flatMap f) m := by
  intro t ht
  obtain ⟨b, hb, htb⟩ := List.mem_flatMap.mp ht
  exact h b hb t htb

/-! ## The terms -/

section Terms
variable (P : SeedParams)

def entryRows (batch : List SExpr) (R N t u v : ℕ) : List SExpr :=
  (List.range R).map fun r => batch.getD (((t * N + u) * N + v) * R + r) []

/-- The constraints of a subset `β` of a walk term's eight positions, with the labels as numbers. -/
def consL (N : ℕ) (α : Fin 8 → ℕ) (c : Fin 8 → Cell N) (β : Fin 8 → Bool) : List (ℕ × ℕ) :=
  (List.finRange 8).filterMap fun k => if β k then some (α k, cellNumC (c k)) else none

/-- The elimination count of `(w, α, β)` at a prefix (`samp:seed`: `0` or `2^{rest − rank}`). -/
def cntL (plen pre : ℕ) (α : Fin 8 → ℕ) (w : Fin 8 → Fin P.N) (β : Fin 8 → Bool) : ℕ :=
  (JoinElimination.condProbGauss P.modulus P.ell 8 (2 * P.kh) plen pre
    (consL P.N α (fun k => cellOf (by norm_num) w k) β)).1

/-- The coefficient term `(−N²)^{|β|}·count`, with no factors. -/
def coefTerm (β : Fin 8 → Bool) (cnt : ℕ) : SExpr :=
  [((-(P.N : ℤ) ^ 2) ^ (univ.filter fun k => β k = true).card * cnt, [])]

/-- The rows of the eight entries of walk `w` at state `t`. -/
def walkRows (batch : List SExpr) (R : ℕ) (w : Fin 8 → Fin P.N) (t : ℕ) : List SExpr :=
  (List.finRange 8).flatMap fun k => entryRows batch R P.N t (cellOf (by norm_num) w k).1 (cellOf (by norm_num) w k).2

/-- One term group: the coefficient times the eight entries of state `t`. -/
def termsAt (batch : List SExpr) (R plen pre : ℕ) (w : Fin 8 → Fin P.N) (α : Fin 8 → ℕ) (β : Fin 8 → Bool)
    (t : ℕ) : SExpr :=
  sfold (coefTerm P β (cntL P plen pre α w β)) (walkRows P batch R w t)

/-- The coefficient of a nonzero count `2^e`: a sign and a power of two, `(−1)^{|β|}·2^{2kh|β| + e}` (`N = 2^{kh}`). -/
theorem coefTerm_pow (β : Fin 8 → Bool) (e : ℕ) :
    coefTerm P β (2 ^ e) = [((-1 : ℤ) ^ (univ.filter fun k => β k = true).card *
      2 ^ (2 * P.kh * (univ.filter fun k => β k = true).card + e), [])] := by
  unfold coefTerm
  congr 2
  set b := (univ.filter fun k => β k = true).card
  have hN : ((P.N : ℕ) : ℤ) = 2 ^ P.kh := by simp [SeedParams.N]
  rw [hN]
  push_cast
  have h1 : (-((2 : ℤ) ^ P.kh) ^ 2) ^ b = (-1) ^ b * 2 ^ (2 * P.kh * b) := by
    rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring
  rw [h1, pow_add]
  ring

/-- The count is `0` or a power of two (`condProbGauss`). -/
theorem cntL_cases (plen pre : ℕ) (α : Fin 8 → ℕ) (w : Fin 8 → Fin P.N) (β : Fin 8 → Bool) :
    cntL P plen pre α w β = 0 ∨ ∃ e, cntL P plen pre α w β = 2 ^ e := by
  unfold cntL JoinElimination.condProbGauss
  dsimp only
  split
  · right; exact ⟨_, rfl⟩
  · left; rfl

/-- Digit vectors in counter order. -/
def digitsL (m : ℕ) : List (Fin 8 → Fin m) := (List.finRange (m ^ 8)).map finFunctionFinEquiv.symm

/-- The terms of state `t`: over walks, labels below `Q` and signs with a nonzero count, the coefficient times the
eight entries of `t`. -/
def sampTermsT (R : ℕ) (batch : List SExpr) (plen pre t : ℕ) : SExpr :=
  (digitsL P.N).flatMap fun w => (digitsL (2 ^ P.ell)).flatMap fun α' =>
    if ∀ k, (α' k : ℕ) < P.Q then
      (digitsL 2).flatMap fun β' =>
        if cntL P plen pre (fun k => α' k) w (fun k => finTwoEquiv (β' k)) = 0 then []
        else termsAt P batch R plen pre w (fun k => α' k) (fun k => finTwoEquiv (β' k)) t
    else []

def sampTerms (nT R : ℕ) (batch : List SExpr) (plen pre : ℕ) : SExpr :=
  (List.range nT).flatMap (sampTermsT P R batch plen pre)

theorem consL_eq (α : Fin 8 → Fin P.Q) (c : Fin 8 → Cell P.N) (β : Fin 8 → Bool) :
    consL P.N (fun k => α k) c β = consOfC P α c β := rfl

theorem sum_digitsL {m : ℕ} (F : (Fin 8 → Fin m) → ℤ) : ((digitsL m).map F).sum = ∑ f, F f := by
  unfold digitsL
  rw [List.map_map, ← Fin.sum_univ_def]
  exact Equiv.sum_comp finFunctionFinEquiv.symm F

/-- Labels below `Q` among the `ℓ`-bit digit vectors are the labels of `Fin Q`. -/
theorem sum_labels (F : (Fin 8 → ℕ) → ℤ) :
    ∑ α' : Fin 8 → Fin (2 ^ P.ell), (if ∀ k, (α' k : ℕ) < P.Q then F (fun k => α' k) else 0) =
      ∑ α : Fin 8 → Fin P.Q, F (fun k => α k) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun α _ => fun k => Fin.castLE P.Q_le (α k))
    (fun α' h => fun k => ⟨α' k, (Finset.mem_filter.mp h).2 k⟩) ?_ ?_ ?_ ?_ ?_
  · intro α _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact fun k => (α k).isLt
  · intro α' _
    exact Finset.mem_univ _
  · intro α _
    funext k
    rfl
  · intro α' _
    funext k
    rfl
  · intro α _
    rfl

theorem sum_signs (F : (Fin 8 → Bool) → ℤ) :
    ∑ β' : Fin 8 → Fin 2, F (fun k => finTwoEquiv (β' k)) = ∑ β : Fin 8 → Bool, F β :=
  Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv) F

/-- **The printed expression's value is the printed column value** `V_p(z)` (`sampElim`), whenever the rows of each
entry multiply to the entry's Boolean value at the column's atoms `ρ`. -/
theorem sampTerms_eval (nT R : ℕ) (batch : List SExpr) (plen pre : ℕ) (D : Fin nT → Cell P.N → Bool) (ρ : ℕ → Bool)
    (hD : ∀ (t : Fin nT) (c : Cell P.N),
      ((entryRows batch R P.N t c.1 c.2).map fun V => IntExpression.eval V ρ).prod = bitZ (D t c)) :
    IntExpression.eval (sampTerms P nT R batch plen pre) ρ = sampElim P D plen pre := by
  -- one term group
  have hgroup : ∀ (w : Fin 8 → Fin P.N) (α : Fin 8 → ℕ) (β : Fin 8 → Bool) (t : Fin nT),
      IntExpression.eval (termsAt P batch R plen pre w α β t) ρ =
        (-(P.N : ℤ) ^ 2) ^ (univ.filter fun k => β k = true).card * (cntL P plen pre α w β : ℤ) *
          ∏ k, bitZ (D t (cellOf (by norm_num) w k)) := by
    intro w α β t
    unfold termsAt
    rw [seval_sfold]
    unfold coefTerm walkRows
    rw [seval_cons, seval_nil, prod_map_flatMap]
    simp only [List.map_nil, List.prod_nil, mul_one, add_zero]
    congr 1
    rw [Fin.prod_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    exact hD t (cellOf (by norm_num) w k)
  -- one state
  have hstate : ∀ t : Fin nT, IntExpression.eval (sampTermsT P R batch plen pre t) ρ =
      ∑ w : Fin 8 → Fin P.N, coefW P plen pre w * ∏ k, bitZ (D t (cellOf (by norm_num) w k)) := by
    intro t
    unfold sampTermsT
    rw [seval_flatMap, sum_digitsL]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [seval_flatMap, sum_digitsL]
    have hlab : ∀ α' : Fin 8 → Fin (2 ^ P.ell), IntExpression.eval (if ∀ k, (α' k : ℕ) < P.Q then
        (digitsL 2).flatMap (fun β' => if cntL P plen pre (fun k => α' k) w (fun k => finTwoEquiv (β' k)) = 0 then []
          else termsAt P batch R plen pre w (fun k => α' k) (fun k => finTwoEquiv (β' k)) t)
        else []) ρ =
        if ∀ k, (α' k : ℕ) < P.Q then ∑ β : Fin 8 → Bool,
          (-(P.N : ℤ) ^ 2) ^ (univ.filter fun k => β k = true).card * (cntL P plen pre (fun k => α' k) w β : ℤ) *
            ∏ k, bitZ (D t (cellOf (by norm_num) w k)) else 0 := by
      intro α'
      split
      · rw [seval_flatMap, sum_digitsL, ← sum_signs]
        refine Finset.sum_congr rfl fun β' _ => ?_
        split
        · rename_i h0
          rw [seval_nil, h0]
          simp
        · exact hgroup w _ _ t
      · rfl
    simp only [hlab]
    rw [sum_labels P (fun α => ∑ β : Fin 8 → Bool, (-(P.N : ℤ) ^ 2) ^ (univ.filter fun k => β k = true).card *
      (cntL P plen pre α w β : ℤ) * ∏ k, bitZ (D t (cellOf (by norm_num) w k)))]
    unfold coefW
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_mul]
    rfl
  -- the states
  unfold sampTerms sampElim
  rw [seval_flatMap, Fin.sum_univ_def, ← List.map_coe_finRange_eq_range, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  exact hstate t

end Terms

end NearCubicWires.WireExponent3_5.SeedFix
