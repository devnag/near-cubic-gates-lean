import Proof.Wire_3_5.TransferUnion

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost

section Poly4Q
variable {α : Type}

/-- A rational masked polynomial of degree at most four (the rational form of `Poly4`). -/
structure Poly4Q (α : Type) where
  κ : Fin 4 → ℚ
  F : Fin 4 → Fin 4 → α → ℚ

/-- Its real form. -/
noncomputable def Poly4Q.toReal (P : Poly4Q α) : Poly4 α := ⟨fun j => (P.κ j : ℝ), fun j k a => (P.F j k a : ℝ)⟩

/-- The rational coefficient of the call on tuple `t` from monomial `j`. -/
def Poly4Q.coeff (P : Poly4Q α) (j : Fin 4) (t : Fin 4 → α) : ℚ := P.κ j * ∏ k, P.F j k (t k)

theorem Poly4Q.coeff_toReal (P : Poly4Q α) (j : Fin 4) (t : Fin 4 → α) :
    P.toReal.coeff j t = (P.coeff j t : ℝ) := by
  simp only [Poly4.coeff, Poly4Q.coeff, Poly4Q.toReal, Rat.cast_mul, Rat.cast_prod]

/-- A rational linear form, as a real one. -/
noncomputable def castF (w : α → ℚ) : α → ℝ := fun a => (w a : ℝ)

/-- `polyV` with rational weights. -/
def polyVQ (sys : Bool) (wS wOne wE : α → ℚ) : Poly4Q α :=
  if sys then ⟨![1, -2, 1, 0], ![![wS, wS, wOne, wOne], ![wE, wS, wOne, wOne], ![wE, wOne, wOne, wOne],
    ![wOne, wOne, wOne, wOne]]⟩
  else ⟨![1, -2, 1, 0], ![![wS, wS, wOne, wOne], ![wS, wS, wS, wOne], ![wS, wS, wS, wS], ![wOne, wOne, wOne, wOne]]⟩

/-- `polyQ` with rational weights. -/
def polyQQ (wS wOne : α → ℚ) : Poly4Q α :=
  ⟨![1, 0, 0, 0], ![![wS, wS, wOne, wOne], ![wOne, wOne, wOne, wOne], ![wOne, wOne, wOne, wOne],
    ![wOne, wOne, wOne, wOne]]⟩

/-- The literal offset `[negated]`. -/
def litAQ (n : Bool) : ℚ := if n then 1 else 0
/-- The literal slope `±1`. -/
def litBQ (n : Bool) : ℚ := if n then -1 else 1

/-- `polyMu` with rational weights. -/
def polyMuQ (n₀ n₁ : Bool) (wX wY wOne : α → ℚ) : Poly4Q α :=
  ⟨![litAQ n₀ + litAQ n₁ - litAQ n₀ * litAQ n₁, litBQ n₀ * (1 - litAQ n₁), litBQ n₁ * (1 - litAQ n₀),
      -(litBQ n₀ * litBQ n₁)],
    ![![wOne, wOne, wOne, wOne], ![wX, wOne, wOne, wOne], ![wY, wOne, wOne, wOne], ![wX, wY, wOne, wOne]]⟩

theorem litAQ_cast (n : Bool) : (litAQ n : ℝ) = litA n := by cases n <;> simp [litAQ, litA]
theorem litBQ_cast (n : Bool) : (litBQ n : ℝ) = litB n := by cases n <;> simp [litBQ, litB]

theorem polyVQ_toReal (sys : Bool) (wS wOne wE : α → ℚ) :
    (polyVQ sys wS wOne wE).toReal = polyV sys (castF wS) (castF wOne) (castF wE) := by
  cases sys <;>
  · simp only [polyVQ, polyV, Poly4Q.toReal, Poly4.mk4, Bool.false_eq_true, if_false, if_true]
    congr 1
    · funext j; fin_cases j <;> simp
    · funext j k a; fin_cases j <;> fin_cases k <;> rfl

theorem polyQQ_toReal (wS wOne : α → ℚ) : (polyQQ wS wOne).toReal = polyQ (castF wS) (castF wOne) := by
  simp only [polyQQ, polyQ, Poly4Q.toReal, Poly4.mk4]
  congr 1
  · funext j; fin_cases j <;> simp
  · funext j k a; fin_cases j <;> fin_cases k <;> rfl

theorem polyMuQ_toReal (n₀ n₁ : Bool) (wX wY wOne : α → ℚ) :
    (polyMuQ n₀ n₁ wX wY wOne).toReal = polyMu n₀ n₁ (castF wX) (castF wY) (castF wOne) := by
  simp only [polyMuQ, polyMu, Poly4Q.toReal, Poly4.mk4]
  congr 1
  · funext j; fin_cases j <;> simp [litAQ_cast, litBQ_cast]
  · funext j k a; fin_cases j <;> fin_cases k <;> rfl

end Poly4Q

section Lists

/-- The list of all elements of a finite type, through a numbering. -/
theorem sum_map_equiv {β M : Type} [Fintype β] [AddCommMonoid M] {K : ℕ} (e : Fin K ≃ β) (f : β → M) :
    (((List.finRange K).map e).map f).sum = ∑ b, f b := by
  rw [List.map_map, ← Fin.sum_univ_def]
  exact Equiv.sum_comp e f

theorem mem_map_equiv {β : Type} {K : ℕ} (e : Fin K ≃ β) (b : β) : b ∈ (List.finRange K).map e :=
  List.mem_map.2 ⟨e.symm b, List.mem_finRange _, e.apply_symm_apply b⟩

/-- A term with nonzero coefficient, or nothing. -/
def nzTerm (c : ℚ) (r : PrimRequest) : Option (ℚ × PrimRequest) := if c = 0 then none else some (c, r)

/-- The machine's combination `Σ c·val(req)` of a list of terms. -/
def combine (terms : List (ℚ × PrimRequest)) (val : PrimRequest → ℚ) : ℚ := (terms.map fun p => p.1 * val p.2).sum

theorem combine_flatMap {β : Type} (l : List β) (f : β → List (ℚ × PrimRequest)) (val : PrimRequest → ℚ) :
    combine (l.flatMap f) val = (l.map fun b => combine (f b) val).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [combine, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

theorem combine_filterMap {β : Type} (l : List β) (c : β → ℚ) (r : β → PrimRequest) (val : PrimRequest → ℚ) :
    combine (l.filterMap fun b => nzTerm (c b) (r b)) val = (l.map fun b => c b * val (r b)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← ih]
      unfold nzTerm
      by_cases hb : c b = 0
      · simp [hb]
      · simp [hb, combine]

theorem mem_filterMap_nzTerm {β : Type} (l : List β) (c : β → ℚ) (r : β → PrimRequest) (p : ℚ × PrimRequest) :
    p ∈ l.filterMap (fun b => nzTerm (c b) (r b)) ↔ ∃ b ∈ l, c b ≠ 0 ∧ (c b, r b) = p := by
  rw [List.mem_filterMap]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  unfold nzTerm
  by_cases hb : c b = 0 <;> simp [hb]

theorem combine_congr (l : List (ℚ × PrimRequest)) (val val' : PrimRequest → ℚ) (h : ∀ p ∈ l, val p.2 = val' p.2) :
    combine l val = combine l val' := by
  unfold combine
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem length_flatMap_le {β γ : Type} (l : List β) (f : β → List γ) (b : ℕ) (h : ∀ x ∈ l, (f x).length ≤ b) :
    (l.flatMap f).length ≤ l.length * b := by
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul (l.map fun x => (f x).length) b (by simpa using h)
  simpa using this

end Lists

structure UnionCheckData where
  mode : Mode
  q : ℕ
  H : BooleanCircuit q
  pcpp : PointwisePCPP H
  s : ℕ
  sign : PcppVar pcpp → Fin s → ℤ
  atom : PcppVar pcpp → Fin s → mode.Circuit q
  const : mode.Circuit q
  parityOf : Finset (Fin q) → mode.Circuit q
  mass : ℚ
  translation : List ℕ

namespace UnionCheckData
variable (D : UnionCheckData)

/-- Whether a variable is systematic. -/
def sysBit (X : PcppVar D.pcpp) : Bool := decide (X.val < D.pcpp.systematicBits)

/-- The encoding support of a systematic variable (empty otherwise). -/
def support (X : PcppVar D.pcpp) : Finset (Fin D.q) :=
  if h : X.val < D.pcpp.systematicBits then D.pcpp.systematicSupport ⟨X.val, h⟩ else ∅

def parity (X : PcppVar D.pcpp) : D.mode.Circuit D.q := D.parityOf (D.support X)

def carrier (X : PcppVar D.pcpp) : Stars.Carrier D.q :=
  (List.ofFn fun a => D.mode.gates (D.atom X a)).flatten ++ (if D.sysBit X then D.mode.gates (D.parity X) else [])

/-- The atoms of the calls: the constant, the grid atoms, the encoding parities. -/
abbrev AtomIx : Type := Unit ⊕ (PcppVar D.pcpp × Fin D.s) ⊕ PcppVar D.pcpp

/-- The circuit of each atom. -/
def circ : D.AtomIx → D.mode.Circuit D.q
  | Sum.inl _ => D.const
  | Sum.inr (Sum.inl (X, a)) => D.atom X a
  | Sum.inr (Sum.inr X) => D.parity X

/-- `S_X = (Λ̄/s)Σ_a σ_{X,a} C_{X,a}`, rational. -/
def wS (X : PcppVar D.pcpp) : D.AtomIx → ℚ
  | Sum.inr (Sum.inl p) => if p.1 = X then D.mass / D.s * D.sign p.1 p.2 else 0
  | _ => 0

/-- The constant `1`. -/
def wOne : D.AtomIx → ℚ
  | Sum.inl _ => 1
  | _ => 0

/-- The encoding parity `E_X`. -/
def wE (X : PcppVar D.pcpp) : D.AtomIx → ℚ
  | Sum.inr (Sum.inr Y) => if Y = X then 1 else 0
  | _ => 0

/-- The call of a `V`/`Q` term at a position (one named carrier). -/
def vCall (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (t : Fin 4 → D.AtomIx) : PrimRequest :=
  tupleRequest D.mode D.q D.circ t [D.carrier (posVar D.pcpp pos.1 pos.2)] D.translation

/-- The call of a `μ` term of a clause (two named carriers). -/
def muCall (i : Fin (2 ^ D.pcpp.clauseBits)) (t : Fin 4 → D.AtomIx) : PrimRequest :=
  tupleRequest D.mode D.q D.circ t [D.carrier (posVar D.pcpp i 0), D.carrier (posVar D.pcpp i 1)] D.translation

/-- The validity polynomial at a position. -/
def polyVAt (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) : Poly4Q D.AtomIx :=
  polyVQ (D.sysBit (posVar D.pcpp pos.1 pos.2)) (D.wS (posVar D.pcpp pos.1 pos.2)) D.wOne
    (D.wE (posVar D.pcpp pos.1 pos.2))

/-- The second-moment polynomial at a position. -/
def polyQAt (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) : Poly4Q D.AtomIx :=
  polyQQ (D.wS (posVar D.pcpp pos.1 pos.2)) D.wOne

/-- The clause polynomial of a clause. -/
def polyMuAt (i : Fin (2 ^ D.pcpp.clauseBits)) : Poly4Q D.AtomIx :=
  polyMuQ (posNeg D.pcpp i 0) (posNeg D.pcpp i 1) (D.wS (posVar D.pcpp i 0)) (D.wS (posVar D.pcpp i 1)) D.wOne

/-! ### Enumeration -/

/-- The number of PCPP variables. -/
abbrev nvars : ℕ := D.pcpp.systematicBits + D.pcpp.auxiliaryBits

/-- The number of atoms: the constant, `s` grid atoms per variable, one parity per variable. -/
def atomCount : ℕ := 1 + (D.nvars * D.s + D.nvars)

/-- The numbering of the atoms: the constant, then the grid atoms variable-major, then the parities. -/
def atomEquiv : D.AtomIx ≃ Fin D.atomCount :=
  (Equiv.sumCongr finOneEquiv.symm (Equiv.sumCongr finProdFinEquiv (Equiv.refl _))).trans
    ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)

/-- The numbering of the four-tuples of atoms. -/
def tupleEquiv : (Fin 4 → D.AtomIx) ≃ Fin (D.atomCount ^ 4) :=
  (Equiv.arrowCongr (Equiv.refl (Fin 4)) D.atomEquiv).trans finFunctionFinEquiv

/-- Every four-tuple of atoms, in order. -/
def tuples : List (Fin 4 → D.AtomIx) := (List.finRange (D.atomCount ^ 4)).map D.tupleEquiv.symm

/-- Every position `(i, j)`, in order. -/
def positions : List (Fin (2 ^ D.pcpp.clauseBits) × Fin 2) :=
  (List.finRange (2 ^ D.pcpp.clauseBits * 2)).map finProdFinEquiv.symm

theorem length_tuples : D.tuples.length = D.atomCount ^ 4 := by simp [tuples]
theorem length_positions : D.positions.length = 2 ^ D.pcpp.clauseBits * 2 := by simp [positions]

/-! ### The terms and the schedule -/

/-- The `V` terms: per position, monomial and tuple with nonzero coefficient, the coefficient and the call. -/
def termsV : List (ℚ × PrimRequest) :=
  D.positions.flatMap fun pos => (List.finRange 4).flatMap fun j =>
    D.tuples.filterMap fun t => nzTerm ((D.polyVAt pos).coeff j t) (D.vCall pos t)

/-- The `Q` terms. -/
def termsQ : List (ℚ × PrimRequest) :=
  D.positions.flatMap fun pos => (List.finRange 4).flatMap fun j =>
    D.tuples.filterMap fun t => nzTerm ((D.polyQAt pos).coeff j t) (D.vCall pos t)

/-- The `μ` terms. -/
def termsMu : List (ℚ × PrimRequest) :=
  (List.finRange (2 ^ D.pcpp.clauseBits)).flatMap fun i => (List.finRange 4).flatMap fun j =>
    D.tuples.filterMap fun t => nzTerm ((D.polyMuAt i).coeff j t) (D.muCall i t)

/-- **The call schedule**: the primitive requests the machine issues, in order. -/
def schedule : List PrimRequest := (D.termsV ++ D.termsQ ++ D.termsMu).map Prod.snd

theorem length_termsV : D.termsV.length ≤ 2 ^ D.pcpp.clauseBits * 2 * (4 * D.atomCount ^ 4) := by
  rw [← D.length_positions]
  refine length_flatMap_le _ _ _ fun pos _ => ?_
  calc _ ≤ (List.finRange 4).length * D.atomCount ^ 4 :=
        length_flatMap_le _ _ _ fun j _ => (List.length_filterMap_le _ _).trans D.length_tuples.le
    _ = 4 * D.atomCount ^ 4 := by rw [List.length_finRange]

theorem length_termsQ : D.termsQ.length ≤ 2 ^ D.pcpp.clauseBits * 2 * (4 * D.atomCount ^ 4) := by
  rw [← D.length_positions]
  refine length_flatMap_le _ _ _ fun pos _ => ?_
  calc _ ≤ (List.finRange 4).length * D.atomCount ^ 4 :=
        length_flatMap_le _ _ _ fun j _ => (List.length_filterMap_le _ _).trans D.length_tuples.le
    _ = 4 * D.atomCount ^ 4 := by rw [List.length_finRange]

theorem length_termsMu : D.termsMu.length ≤ 2 ^ D.pcpp.clauseBits * (4 * D.atomCount ^ 4) := by
  refine (length_flatMap_le _ _ (4 * D.atomCount ^ 4) fun i _ => ?_).trans (by rw [List.length_finRange])
  calc _ ≤ (List.finRange 4).length * D.atomCount ^ 4 :=
        length_flatMap_le _ _ _ fun j _ => (List.length_filterMap_le _ _).trans D.length_tuples.le
    _ = 4 * D.atomCount ^ 4 := by rw [List.length_finRange]

/-- **The schedule's length**: at most `3·(2M)·4·A⁴` requests for `M` clauses and `A` atoms. -/
theorem length_schedule : D.schedule.length ≤ 3 * (2 ^ D.pcpp.clauseBits * 2) * (4 * D.atomCount ^ 4) := by
  have h1 := D.length_termsV
  have h2 := D.length_termsQ
  have h3 := D.length_termsMu
  simp only [schedule, List.length_map, List.length_append]
  nlinarith [Nat.zero_le (2 ^ D.pcpp.clauseBits * (4 * D.atomCount ^ 4))]

theorem mem_termsV (p : ℚ × PrimRequest) :
    p ∈ D.termsV ↔ ∃ pos j t, (D.polyVAt pos).coeff j t ≠ 0 ∧ ((D.polyVAt pos).coeff j t, D.vCall pos t) = p := by
  simp only [termsV, List.mem_flatMap, mem_filterMap_nzTerm]
  constructor
  · rintro ⟨pos, -, j, -, t, -, h⟩; exact ⟨pos, j, t, h⟩
  · rintro ⟨pos, j, t, h⟩
    exact ⟨pos, mem_map_equiv _ _, j, List.mem_finRange _, t, mem_map_equiv _ _, h⟩

theorem mem_termsQ (p : ℚ × PrimRequest) :
    p ∈ D.termsQ ↔ ∃ pos j t, (D.polyQAt pos).coeff j t ≠ 0 ∧ ((D.polyQAt pos).coeff j t, D.vCall pos t) = p := by
  simp only [termsQ, List.mem_flatMap, mem_filterMap_nzTerm]
  constructor
  · rintro ⟨pos, -, j, -, t, -, h⟩; exact ⟨pos, j, t, h⟩
  · rintro ⟨pos, j, t, h⟩
    exact ⟨pos, mem_map_equiv _ _, j, List.mem_finRange _, t, mem_map_equiv _ _, h⟩

theorem mem_termsMu (p : ℚ × PrimRequest) :
    p ∈ D.termsMu ↔ ∃ i j t, (D.polyMuAt i).coeff j t ≠ 0 ∧ ((D.polyMuAt i).coeff j t, D.muCall i t) = p := by
  simp only [termsMu, List.mem_flatMap, mem_filterMap_nzTerm]
  constructor
  · rintro ⟨i, -, j, -, t, -, h⟩; exact ⟨i, j, t, h⟩
  · rintro ⟨i, j, t, h⟩
    exact ⟨i, List.mem_finRange _, j, List.mem_finRange _, t, mem_map_equiv _ _, h⟩

/-- The schedule consists exactly of the calls with a nonzero coefficient. -/
theorem forall_schedule_iff (ok : PrimRequest → Prop) :
    (∀ r ∈ D.schedule, ok r) ↔
      (∀ pos j t, (D.polyVAt pos).coeff j t ≠ 0 → ok (D.vCall pos t)) ∧
      (∀ pos j t, (D.polyQAt pos).coeff j t ≠ 0 → ok (D.vCall pos t)) ∧
      (∀ i j t, (D.polyMuAt i).coeff j t ≠ 0 → ok (D.muCall i t)) := by
  simp only [schedule, List.mem_map, List.mem_append]
  constructor
  · intro h
    refine ⟨fun pos j t hc => h _ ⟨_, Or.inl (Or.inl ((D.mem_termsV _).2 ⟨pos, j, t, hc, rfl⟩)), rfl⟩,
      fun pos j t hc => h _ ⟨_, Or.inl (Or.inr ((D.mem_termsQ _).2 ⟨pos, j, t, hc, rfl⟩)), rfl⟩,
      fun i j t hc => h _ ⟨_, Or.inr ((D.mem_termsMu _).2 ⟨i, j, t, hc, rfl⟩), rfl⟩⟩
  · rintro ⟨hV, hQ, hM⟩ r ⟨p, hp, rfl⟩
    rcases hp with (hp | hp) | hp
    · obtain ⟨pos, j, t, hc, rfl⟩ := (D.mem_termsV p).1 hp; exact hV pos j t hc
    · obtain ⟨pos, j, t, hc, rfl⟩ := (D.mem_termsQ p).1 hp; exact hQ pos j t hc
    · obtain ⟨i, j, t, hc, rfl⟩ := (D.mem_termsMu p).1 hp; exact hM i j t hc

/-! ### The estimates and the check -/

variable (val : PrimRequest → ℚ)

/-- The machine's `V̂`, exact rational. -/
def VhatQ : ℚ := combine D.termsV val / (2 ^ D.pcpp.clauseBits * 2)

/-- The machine's `Q̂`, exact rational. -/
def QhatQ : ℚ := combine D.termsQ val / (2 ^ D.pcpp.clauseBits * 2)

/-- The machine's `μ̂`, exact rational. -/
def μhatQ : ℚ := combine D.termsMu val / 2 ^ D.pcpp.clauseBits

theorem combine_termsV :
    combine D.termsV val = ∑ pos, ∑ j, ∑ t, (D.polyVAt pos).coeff j t * val (D.vCall pos t) := by
  simp only [termsV, combine_flatMap, combine_filterMap]
  rw [positions, sum_map_equiv]
  refine Finset.sum_congr rfl fun pos _ => ?_
  rw [← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tuples, sum_map_equiv]

theorem combine_termsQ :
    combine D.termsQ val = ∑ pos, ∑ j, ∑ t, (D.polyQAt pos).coeff j t * val (D.vCall pos t) := by
  simp only [termsQ, combine_flatMap, combine_filterMap]
  rw [positions, sum_map_equiv]
  refine Finset.sum_congr rfl fun pos _ => ?_
  rw [← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tuples, sum_map_equiv]

theorem combine_termsMu :
    combine D.termsMu val = ∑ i, ∑ j, ∑ t, (D.polyMuAt i).coeff j t * val (D.muCall i t) := by
  simp only [termsMu, combine_flatMap, combine_filterMap]
  rw [← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tuples, sum_map_equiv]

/-- The grid signs are in `{−1, 0, 1}`. -/
def signsOk : Bool := decide (∀ X a, D.sign X a ∈ ({-1, 0, 1} : Finset ℤ))

/-- **The check** from the call answers `val`: grid signs, every scheduled call admissible, and `tr:thresholds`
`V̂ ≤ 2v₀`, `Q̂ ≤ 1+v₀`, `τ ≤ μ̂` in exact rationals. -/
def check (v0 τ : ℚ) (callOk : PrimRequest → Bool) : Bool :=
  D.signsOk && D.schedule.all callOk && decide (D.VhatQ val ≤ 2 * v0) && decide (D.QhatQ val ≤ 1 + v0) &&
    decide (τ ≤ D.μhatQ val)

/-- The check reads the answers only at the scheduled requests. -/
theorem check_congr (v0 τ : ℚ) (callOk : PrimRequest → Bool) (val' : PrimRequest → ℚ)
    (h : ∀ r ∈ D.schedule, val r = val' r) : D.check val v0 τ callOk = D.check val' v0 τ callOk := by
  have hs : ∀ p ∈ D.termsV ++ D.termsQ ++ D.termsMu, val p.2 = val' p.2 := fun p hp =>
    h p.2 (List.mem_map.2 ⟨p, hp, rfl⟩)
  have hV : D.VhatQ val = D.VhatQ val' := by
    unfold VhatQ; rw [combine_congr _ val val' fun p hp => hs p (by simp [hp])]
  have hQ : D.QhatQ val = D.QhatQ val' := by
    unfold QhatQ; rw [combine_congr _ val val' fun p hp => hs p (by simp [hp])]
  have hM : D.μhatQ val = D.μhatQ val' := by
    unfold μhatQ; rw [combine_congr _ val val' fun p hp => hs p (by simp [hp])]
  simp only [check, hV, hQ, hM]

end UnionCheckData

end NearCubicWires.WireExponent3_5.Transfer
