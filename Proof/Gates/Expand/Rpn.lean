import Proof.Gates.Expand.Value

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires NearCubicWires.RepairRepresentation
open scoped BigOperators

/-- The operations of one evaluation pass. -/
structure Alg where
  c : ℤ → ℕ
  v : ℕ → ℕ
  add : ℕ → ℕ → ℕ
  neg : ℕ → ℕ
  sub : ℕ → ℕ → ℕ
  mul : ℕ → ℕ → ℕ
  pow : ℕ → ℕ → ℕ

namespace Alg
variable (A : Alg)

/-- One token on the stack (top first). A missing argument reads as `0` (the stack number of the machine,
`senc`, cannot tell `[]` from `[0]`); `toks F` never reaches that case. -/
def step : List ℕ → Tok → List ℕ
  | xs, .const a => A.c a :: xs
  | xs, .var v => A.v v :: xs
  | xs, .add => A.add (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail
  | xs, .neg => A.neg (xs.headD 0) :: xs.tail
  | xs, .sub => A.sub (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail
  | xs, .mul => A.mul (xs.tail.headD 0) (xs.headD 0) :: xs.tail.tail
  | xs, .pow e => A.pow (xs.headD 0) e :: xs.tail

/-- The value of a formula in the pass. -/
def eval {V : ℕ} : Formula V → ℕ
  | .const a => A.c a
  | .var v => A.v v.val
  | .add f g => A.add (eval f) (eval g)
  | .neg f => A.neg (eval f)
  | .sub f g => A.sub (eval f) (eval g)
  | .mul f g => A.mul (eval f) (eval g)
  | .pow f e => A.pow (eval f) e

/-- Running the tokens of `F` pushes its value. -/
theorem foldl_toks {V : ℕ} (F : Formula V) (rest : List Tok) (xs : List ℕ) :
    (toks F ++ rest).foldl A.step xs = rest.foldl A.step (A.eval F :: xs) := by
  induction F generalizing rest xs with
  | const a => simp [toks, step, eval]
  | var v => simp [toks, step, eval]
  | add f g hf hg => simp only [toks, List.append_assoc, hf, hg, List.cons_append, List.nil_append,
      List.foldl_cons, step, eval, List.tail_cons, List.headD_cons]
  | neg f hf => simp only [toks, List.append_assoc, hf, List.cons_append, List.nil_append, List.foldl_cons, step, List.tail_cons, List.headD_cons,
      eval]
  | sub f g hf hg => simp only [toks, List.append_assoc, hf, hg, List.cons_append, List.nil_append,
      List.foldl_cons, step, eval, List.tail_cons, List.headD_cons]
  | mul f g hf hg => simp only [toks, List.append_assoc, hf, hg, List.cons_append, List.nil_append,
      List.foldl_cons, step, eval, List.tail_cons, List.headD_cons]
  | pow f e hf => simp only [toks, List.append_assoc, hf, List.cons_append, List.nil_append, List.foldl_cons, step, List.tail_cons, List.headD_cons,
      eval]

theorem foldl_toks_nil {V : ℕ} (F : Formula V) : (toks F).foldl A.step [] = [A.eval F] := by
  simpa using A.foldl_toks F [] []

/-- A pass whose operations stay below `M` when their arguments do. -/
structure Closed (M : ℕ) : Prop where
  c : ∀ a, A.c a < M
  v : ∀ j, A.v j < M
  add : ∀ x y, x < M → y < M → A.add x y < M
  neg : ∀ x, x < M → A.neg x < M
  sub : ∀ x y, x < M → y < M → A.sub x y < M
  mul : ∀ x y, x < M → y < M → A.mul x y < M
  pow : ∀ x e, x < M → A.pow x e < M

theorem headD_lt {M : ℕ} (hM : 0 < M) (xs : List ℕ) (h : ∀ x ∈ xs, x < M) : xs.headD 0 < M := by
  cases xs with
  | nil => simpa using hM
  | cons x xs => exact h x (by simp)

theorem tail_lt {M : ℕ} (xs : List ℕ) (h : ∀ x ∈ xs, x < M) : ∀ x ∈ xs.tail, x < M :=
  fun x hx => h x (List.mem_of_mem_tail hx)

theorem step_lt {M : ℕ} (hA : A.Closed M) (xs : List ℕ) (t : Tok) (h : ∀ x ∈ xs, x < M) :
    (∀ x ∈ A.step xs t, x < M) ∧ (A.step xs t).length ≤ xs.length + 1 := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) (hA.c 0)
  have h0 := headD_lt hM xs h
  have h1 := headD_lt hM xs.tail (tail_lt xs h)
  have h2 := tail_lt xs.tail (tail_lt xs h)
  have h3 := tail_lt xs h
  have l1 : xs.tail.length ≤ xs.length := by simp
  have l2 : xs.tail.tail.length ≤ xs.length := by simp; omega
  have cl : ∀ (a : ℕ) (l : List ℕ), a < M → (∀ x ∈ l, x < M) → ∀ x ∈ a :: l, x < M := by
    intro a l ha hl x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hl x hx
  cases t with
  | const a => exact ⟨cl _ _ (hA.c a) h, by simp only [step, List.length_cons]; omega⟩
  | var j => exact ⟨cl _ _ (hA.v j) h, by simp only [step, List.length_cons]; omega⟩
  | add => exact ⟨cl _ _ (hA.add _ _ h1 h0) h2, by simp only [step, List.length_cons]; omega⟩
  | neg => exact ⟨cl _ _ (hA.neg _ h0) h3, by simp only [step, List.length_cons]; omega⟩
  | sub => exact ⟨cl _ _ (hA.sub _ _ h1 h0) h2, by simp only [step, List.length_cons]; omega⟩
  | mul => exact ⟨cl _ _ (hA.mul _ _ h1 h0) h2, by simp only [step, List.length_cons]; omega⟩
  | pow e => exact ⟨cl _ _ (hA.pow _ e h0) h3, by simp only [step, List.length_cons]; omega⟩

/-- Every prefix run stays below `M`, with depth at most the number of tokens read. -/
theorem foldl_lt {M : ℕ} (hA : A.Closed M) (ts : List Tok) :
    (∀ x ∈ ts.foldl A.step [], x < M) ∧ (ts.foldl A.step []).length ≤ ts.length := by
  induction ts using List.reverseRecOn with
  | nil => simp
  | append_singleton ts t ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := A.step_lt hA _ t ih.1
    exact ⟨this.1, by rw [List.length_append, List.length_singleton]; omega⟩

end Alg

/-! ## The three passes -/

/-- Formal degree, saturated at `K`. -/
def degAlg (K : ℕ) : Alg where
  c _ := 0
  v _ := min 1 K
  add x y := max x y
  neg x := x
  sub x y := max x y
  mul x y := min (x + y) K
  pow x e := min (e * x) K

/-- Bit weight, saturated at `K`. -/
def wtAlg (K : ℕ) : Alg where
  c a := min (Nat.size a.natAbs) K
  v _ := min 1 K
  add x y := min (max x y + 1) K
  neg x := x
  sub x y := min (max x y + 1) K
  mul x y := min (x + y) K
  pow x e := min (e * x) K

theorem min_mul_min (e x K : ℕ) : min (e * min x K) K = min (e * x) K := by
  rcases Nat.lt_or_ge x K with h | h
  · rw [min_eq_left h.le]
  · rw [min_eq_right h]
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [min_eq_right (Nat.le_mul_of_pos_left K he)]
      exact (min_eq_right ((Nat.le_mul_of_pos_left K he).trans (Nat.mul_le_mul_left e h))).symm

theorem degAlg_eval (K : ℕ) {V : ℕ} (F : Formula V) : (degAlg K).eval F = min F.degree K := by
  induction F with
  | const a => simp [Alg.eval, degAlg, Formula.degree]
  | var v => simp [Alg.eval, degAlg, Formula.degree]
  | add f g hf hg => simp only [Alg.eval, degAlg, Formula.degree] at *; rw [hf, hg, min_max_distrib_right]
  | neg f hf => simp only [Alg.eval, degAlg, Formula.degree] at *; exact hf
  | sub f g hf hg => simp only [Alg.eval, degAlg, Formula.degree] at *; rw [hf, hg, min_max_distrib_right]
  | mul f g hf hg =>
    simp only [Alg.eval, degAlg, Formula.degree] at *
    rw [hf, hg]
    omega
  | pow f e hf =>
    simp only [Alg.eval, degAlg, Formula.degree] at *
    rw [hf, min_mul_min]

theorem wtAlg_eval (K : ℕ) {V : ℕ} (F : Formula V) : (wtAlg K).eval F = min F.weight K := by
  induction F with
  | const a => simp [Alg.eval, wtAlg, Formula.weight]
  | var v => simp [Alg.eval, wtAlg, Formula.weight]
  | add f g hf hg =>
    simp only [Alg.eval, wtAlg, Formula.weight] at *
    rw [hf, hg]
    omega
  | neg f hf => simp only [Alg.eval, wtAlg, Formula.weight] at *; exact hf
  | sub f g hf hg =>
    simp only [Alg.eval, wtAlg, Formula.weight] at *
    rw [hf, hg]
    omega
  | mul f g hf hg =>
    simp only [Alg.eval, wtAlg, Formula.weight] at *
    rw [hf, hg]
    omega
  | pow f e hf =>
    simp only [Alg.eval, wtAlg, Formula.weight] at *
    rw [hf, min_mul_min]

theorem degAlg_closed (K : ℕ) : (degAlg K).Closed (K + 1) where
  c _ := by simp only [degAlg]; omega
  v _ := by simp only [degAlg]; omega
  add x y hx hy := by simp only [degAlg]; omega
  neg x hx := hx
  sub x y hx hy := by simp only [degAlg]; omega
  mul x y _ _ := by simp only [degAlg]; omega
  pow x e _ := by simp only [degAlg]; omega

theorem wtAlg_closed (K : ℕ) : (wtAlg K).Closed (K + 1) where
  c _ := by simp only [wtAlg]; omega
  v _ := by simp only [wtAlg]; omega
  add x y _ _ := by simp only [wtAlg]; omega
  neg x hx := hx
  sub x y _ _ := by simp only [wtAlg]; omega
  mul x y _ _ := by simp only [wtAlg]; omega
  pow x e _ := by simp only [wtAlg]; omega

/-- Values at the point `t` (a characteristic number), modulo `2^W`. -/
def valAlg (W t : ℕ) : Alg where
  c a := (a % (2 ^ W : ℤ)).toNat
  v j := if t.testBit j then 1 % 2 ^ W else 0
  add x y := (x + y) % 2 ^ W
  neg x := (2 ^ W - x) % 2 ^ W
  sub x y := (x + (2 ^ W - y)) % 2 ^ W
  mul x y := x * y % 2 ^ W
  pow x e := x ^ e % 2 ^ W

theorem valAlg_closed (W t : ℕ) : (valAlg W t).Closed (2 ^ W) where
  c a := by
    have h1 : (0 : ℤ) ≤ a % (2 ^ W : ℤ) := Int.emod_nonneg _ (by positivity)
    have h2 : a % (2 ^ W : ℤ) < 2 ^ W := Int.emod_lt_of_pos _ (by positivity)
    exact (Int.toNat_lt h1).mpr (by exact_mod_cast h2)
  v j := by
    simp only [valAlg]
    split_ifs
    · exact Nat.mod_lt _ (Nat.two_pow_pos W)
    · exact Nat.two_pow_pos W
  add x y _ _ := Nat.mod_lt _ (Nat.two_pow_pos W)
  neg x _ := Nat.mod_lt _ (Nat.two_pow_pos W)
  sub x y _ _ := Nat.mod_lt _ (Nat.two_pow_pos W)
  mul x y _ _ := Nat.mod_lt _ (Nat.two_pow_pos W)
  pow x e _ := Nat.mod_lt _ (Nat.two_pow_pos W)

theorem Alg.eval_lt (A : Alg) {M : ℕ} (hA : A.Closed M) {V : ℕ} (F : Formula V) : A.eval F < M := by
  induction F with
  | const a => exact hA.c a
  | var v => exact hA.v _
  | add f g hf hg => exact hA.add _ _ hf hg
  | neg f hf => exact hA.neg _ hf
  | sub f g hf hg => exact hA.sub _ _ hf hg
  | mul f g hf hg => exact hA.mul _ _ hf hg
  | pow f e hf => exact hA.pow _ _ hf

/-- The pass computes the value at the indicator point of `setOf V t`, modulo `2^W`. -/
theorem valAlg_eval (W t : ℕ) {V : ℕ} (F : Formula V) :
    ((valAlg W t).eval F : ℤ) = F.eval (boolPoint (ind (setOf V t))) % 2 ^ W := by
  have key : ∀ (N : ℕ) (E : ℤ), (N : ℤ) ≡ E [ZMOD 2 ^ W] → ((N % 2 ^ W : ℕ) : ℤ) = E % 2 ^ W := by
    intro N E h
    rw [Int.natCast_mod]; push_cast; exact h
  have back : ∀ (x : ℕ) (e : ℤ), (x : ℤ) = e % 2 ^ W → (x : ℤ) ≡ e [ZMOD 2 ^ W] := by
    intro x e h; unfold Int.ModEq; rw [h, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have h0 : ((2 : ℤ) ^ W) ≡ 0 [ZMOD 2 ^ W] := by unfold Int.ModEq; simp
  have hlt : ∀ G : Formula V, (valAlg W t).eval G ≤ 2 ^ W := fun G => ((valAlg W t).eval_lt (valAlg_closed W t) G).le
  induction F with
  | const a =>
    show (((a % (2 ^ W : ℤ)).toNat : ℕ) : ℤ) = a % 2 ^ W
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  | var v =>
    show ((if t.testBit v.val then 1 % 2 ^ W else 0 : ℕ) : ℤ) = boolPoint (ind (setOf V t)) v % 2 ^ W
    have hb : boolPoint (ind (setOf V t)) v = if t.testBit v.val then 1 else 0 := by
      simp [boolPoint, ind, setOf]
    rw [hb]
    split_ifs
    · exact key 1 1 (Int.ModEq.refl _)
    · simp
  | add f g hf hg =>
    show ((((valAlg W t).eval f + (valAlg W t).eval g) % 2 ^ W : ℕ) : ℤ) = _
    exact key _ _ (by push_cast; exact (back _ _ hf).add (back _ _ hg))
  | neg f hf =>
    show (((2 ^ W - (valAlg W t).eval f) % 2 ^ W : ℕ) : ℤ) = _
    simp only [Formula.eval]
    refine key _ _ ?_
    rw [Nat.cast_sub (hlt f)]
    push_cast
    simpa using h0.sub (back _ _ hf)
  | sub f g hf hg =>
    show ((((valAlg W t).eval f + (2 ^ W - (valAlg W t).eval g)) % 2 ^ W : ℕ) : ℤ) = _
    simp only [Formula.eval]
    refine key _ _ ?_
    rw [Nat.cast_add, Nat.cast_sub (hlt g)]
    push_cast
    have := (back _ _ hf).add (h0.sub (back _ _ hg))
    simpa [sub_eq_add_neg] using this
  | mul f g hf hg =>
    show ((((valAlg W t).eval f * (valAlg W t).eval g) % 2 ^ W : ℕ) : ℤ) = _
    exact key _ _ (by push_cast; exact (back _ _ hf).mul (back _ _ hg))
  | pow f e hf =>
    show ((((valAlg W t).eval f ^ e) % 2 ^ W : ℕ) : ℤ) = _
    exact key _ _ (by push_cast; exact (back _ _ hf).pow e)

/-! ## Bounds by the word length -/

def tokBits {V : ℕ} (F : Formula V) : ℕ := ((toks F).flatMap tokWord).length

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 :=
  NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x

theorem lt_two_pow_natBitLength (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem size_le_natBitLength (x : ℕ) : Nat.size x ≤ natBitLength x := by
  rw [Nat.size_le]
  exact lt_two_pow_natBitLength x

section TokBits
variable {V : ℕ}
theorem tokBits_const (a : ℤ) : tokBits (Formula.const a : Formula V) =
    3 + (2 * natBitLength (if a < 0 then 1 else 0) + 1) + (2 * natBitLength a.natAbs + 1) := by
  have h2 : natBitLength 0 = 1 := by decide
  simp only [tokBits, toks, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2, Interfaces.intWord]
  omega
theorem tokBits_var (v : Fin V) : tokBits (Formula.var v) = 3 + (2 * natBitLength v.val + 1) := by
  have h2 : natBitLength 1 = 1 := by decide
  simp only [tokBits, toks, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
theorem tokBits_add (f g : Formula V) : tokBits (Formula.add f g) = tokBits f + tokBits g + 5 := by
  have h2 : natBitLength 2 = 2 := by decide
  simp only [tokBits, toks, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
theorem tokBits_neg (f : Formula V) : tokBits (Formula.neg f) = tokBits f + 5 := by
  have h2 : natBitLength 3 = 2 := by decide
  simp only [tokBits, toks, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
theorem tokBits_sub (f g : Formula V) : tokBits (Formula.sub f g) = tokBits f + tokBits g + 7 := by
  have h2 : natBitLength 4 = 3 := by decide
  simp only [tokBits, toks, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
theorem tokBits_mul (f g : Formula V) : tokBits (Formula.mul f g) = tokBits f + tokBits g + 7 := by
  have h2 : natBitLength 5 = 3 := by decide
  simp only [tokBits, toks, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
theorem tokBits_pow (f : Formula V) (e : ℕ) :
    tokBits (Formula.pow f e) = tokBits f + 7 + (2 * natBitLength e + 1) := by
  have h2 : natBitLength 6 = 3 := by decide
  simp only [tokBits, toks, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tokWord, natWord_len, h2]
  omega
end TokBits

theorem pow_mono_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem degree_weight_lt {V : ℕ} (F : Formula V) :
    F.degree < 2 ^ (tokBits F + 1) ∧ F.weight < 2 ^ (tokBits F + 1) := by
  induction F with
  | const a =>
    simp only [Formula.degree, Formula.weight, tokBits_const]
    refine ⟨Nat.two_pow_pos _, ?_⟩
    exact lt_of_le_of_lt (size_le_natBitLength _) (pow_mono_lt Nat.lt_two_pow_self (by omega))
  | var v =>
    simp only [Formula.degree, Formula.weight, tokBits_var]
    exact ⟨pow_mono_lt (by norm_num : 1 < 2 ^ 1) (by omega), pow_mono_lt (by norm_num : 1 < 2 ^ 1) (by omega)⟩
  | add f g hf hg =>
    simp only [Formula.degree, Formula.weight, tokBits_add]
    have e1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits f + 1 ≤ tokBits f + tokBits g + 5)
    have e2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits g + 1 ≤ tokBits f + tokBits g + 5)
    rw [pow_succ]
    omega
  | neg f hf =>
    simp only [Formula.degree, Formula.weight, tokBits_neg]
    exact ⟨pow_mono_lt hf.1 (by omega), pow_mono_lt hf.2 (by omega)⟩
  | sub f g hf hg =>
    simp only [Formula.degree, Formula.weight, tokBits_sub]
    have e1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits f + 1 ≤ tokBits f + tokBits g + 7)
    have e2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits g + 1 ≤ tokBits f + tokBits g + 7)
    rw [pow_succ]
    omega
  | mul f g hf hg =>
    simp only [Formula.degree, Formula.weight, tokBits_mul]
    have e1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits f + 1 ≤ tokBits f + tokBits g + 7)
    have e2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : tokBits g + 1 ≤ tokBits f + tokBits g + 7)
    rw [pow_succ]
    omega
  | pow f e hf =>
    simp only [Formula.degree, Formula.weight, tokBits_pow]
    set b := tokBits f
    have he : e < 2 ^ (2 * natBitLength e + 8) :=
      pow_mono_lt (lt_two_pow_natBitLength e) (by omega)
    have hsplit : 2 ^ (b + 7 + (2 * natBitLength e + 1) + 1) = 2 ^ (2 * natBitLength e + 8) * 2 ^ (b + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have hp : 0 < 2 ^ (b + 1) := Nat.two_pow_pos _
    constructor
    · calc e * f.degree ≤ e * 2 ^ (b + 1) := Nat.mul_le_mul_left e hf.1.le
        _ < _ := Nat.mul_lt_mul_of_pos_right he hp
    · calc e * f.weight ≤ e * 2 ^ (b + 1) := Nat.mul_le_mul_left e hf.2.le
        _ < _ := Nat.mul_lt_mul_of_pos_right he hp

theorem tokBits_le (r : FormulaReq) : tokBits r.2 ≤ (formulaWord r).length := by
  simp only [tokBits, formulaWord, listWord, List.length_append]
  omega

/-- With the cap `2^{|input|+1}`, the saturated degree and weight are exact. -/
theorem degAlg_exact (r : FormulaReq) :
    (degAlg (2 ^ ((formulaWord r).length + 1))).eval r.2 = r.2.degree := by
  rw [degAlg_eval]
  exact min_eq_left (lt_of_lt_of_le (degree_weight_lt r.2).1
    (Nat.pow_le_pow_right (by norm_num) (by have := tokBits_le r; omega))).le

theorem wtAlg_exact (r : FormulaReq) :
    (wtAlg (2 ^ ((formulaWord r).length + 1))).eval r.2 = r.2.weight := by
  rw [wtAlg_eval]
  exact min_eq_left (lt_of_lt_of_le (degree_weight_lt r.2).2
    (Nat.pow_le_pow_right (by norm_num) (by have := tokBits_le r; omega))).le

end NearCubicGates.Close.Expand
