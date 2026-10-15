import Proof.Wire_3_5.ListMachineRowRadixRow

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord coefWord)

/-! ## The store and the contribution fields -/

/-- The digit-list prints of digits `o, …, o + n − 1`, block by block. -/
def storeFrom (K : ℕ) (Pp Pm : ℕ → ℕ → Poly) (o : ℕ) : ℕ → List Poly
  | 0 => []
  | n + 1 => (List.range (K + 1)).map (Pp o) ++ ((List.range (K + 1)).map (Pm o) ++ storeFrom K Pp Pm (o + 1) n)

/-- The contributions `(±b_0^d·t) mod p` of digits `o, …, o + n − 1`, in the store's order. -/
def consFrom (K p b0 : ℕ) (o : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (List.range (K + 1)).map (fun t => b0 ^ o * t % p) ++
      ((List.range (K + 1)).map (fun t => (p - b0 ^ o % p) * t % p) ++ consFrom K p b0 (o + 1) n)

@[simp] theorem storeFrom_length (K : ℕ) (Pp Pm : ℕ → ℕ → Poly) : ∀ (o n : ℕ),
    (storeFrom K Pp Pm o n).length = 2 * n * (K + 1)
  | _, 0 => by simp [storeFrom]
  | o, n + 1 => by simp [storeFrom, storeFrom_length K Pp Pm (o + 1) n]; ring

@[simp] theorem consFrom_length (K p b0 : ℕ) : ∀ (o n : ℕ), (consFrom K p b0 o n).length = 2 * n * (K + 1)
  | _, 0 => by simp [consFrom]
  | o, n + 1 => by simp [consFrom, consFrom_length K p b0 (o + 1) n]; ring

theorem flatP_length (tup : List (ℕ × ℕ)) : (flatP tup).length = 2 * tup.length := by
  induction tup with
  | nil => rfl
  | cons ab tl ih => simp [flatP] at ih ⊢; omega

theorem flatP_cons (a b : ℕ) (tl : List (ℕ × ℕ)) : flatP ((a, b) :: tl) = a :: b :: flatP tl := rfl

theorem mselW_append (r1 r2 : List Bool) (fs1 fs2 : List Poly) (h : r1.length = fs1.length) :
    mselW (r1 ++ r2) (fs1 ++ fs2) = mselW r1 fs1 ++ mselW r2 fs2 := by
  unfold mselW
  rw [List.zip_append h, List.flatMap_append]

theorem flatMap_range_single {β : Type} (f : ℕ → List β) (t : ℕ) : ∀ n, t < n →
    (List.range n).flatMap (fun i => if i = t then f i else []) = f t := by
  have zero : ∀ n, n ≤ t → (List.range n).flatMap (fun i => if i = t then f i else []) = [] := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.flatMap_append, ih (by omega)]; simp; omega
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : t < n
    · rw [ih h]; simp; omega
    · have : t = n := by omega
      subst this
      rw [zero t le_rfl]; simp

theorem mselW_ohB (K t : ℕ) (g : ℕ → Poly) (ht : t ≤ K) :
    mselW (ohB K t) ((List.range (K + 1)).map g) = true :: polyWord (g t) := by
  unfold mselW ohB
  rw [List.zip_map', List.flatMap_map]
  have := flatMap_range_single (fun i => true :: polyWord (g i)) t (K + 1) (by omega)
  rw [← this]
  refine congrArg (fun h => (List.range (K + 1)).flatMap h) (funext fun i => ?_)
  by_cases h : i = t <;> simp [h]

/-- **The selected factors are `tupleFactors`.** -/
theorem mselW_storeFrom (K : ℕ) (Pp Pm : ℕ → ℕ → Poly) : ∀ (tup : List (ℕ × ℕ)) (o : ℕ),
    (∀ ab ∈ tup, ab.1 ≤ K ∧ ab.2 ≤ K) →
    mselW (encT K (flatP tup)) (storeFrom K Pp Pm o tup.length) =
      (tupleFactors Pp Pm o tup).flatMap fun f => true :: polyWord f
  | [], _, _ => by simp [flatP, encT, storeFrom, mselW, tupleFactors]
  | (a, b) :: tl, o, h => by
    have ha := (h (a, b) (by simp)).1
    have hb := (h (a, b) (by simp)).2
    rw [flatP_cons]
    simp only [encT, List.flatMap_cons, List.length_cons, storeFrom, tupleFactors]
    rw [mselW_append _ _ _ _ (by simp), mselW_append _ _ _ _ (by simp),
      mselW_ohB K a _ ha, mselW_ohB K b _ hb]
    have ih := mselW_storeFrom K Pp Pm tl (o + 1) (fun ab hab => h ab (by simp [hab]))
    simp only [encT] at ih
    rw [ih]

/-- **The masked sum is the signed radix value mod `p`.** -/
theorem dotB_consFrom (K p b0 : ℕ) (hp : 0 < p) : ∀ (tup : List (ℕ × ℕ)) (o : ℕ), (∀ ab ∈ tup, ab.1 ≤ K ∧ ab.2 ≤ K) →
    ((dotB (encT K (flatP tup)) (consFrom K p b0 o tup.length) : ℕ) : ZMod p) =
      ((tupleValue b0 o tup : ℤ) : ZMod p)
  | [], _, _ => by simp [flatP, encT, consFrom, dotB, tupleValue]
  | (a, b) :: tl, o, h => by
    have ha := (h (a, b) (by simp)).1
    have hb := (h (a, b) (by simp)).2
    rw [flatP_cons]
    simp only [encT, List.flatMap_cons, List.length_cons, consFrom, tupleValue]
    rw [dotB_append _ _ _ _ (by simp), dotB_append _ _ _ _ (by simp),
      dotB_ohB K a _ ha, dotB_ohB K b _ hb]
    have ih := dotB_consFrom K p b0 hp tl (o + 1) (fun ab hab => h ab (by simp [hab]))
    simp only [encT] at ih
    have hle : b0 ^ o % p ≤ p := (Nat.mod_lt _ hp).le
    push_cast
    rw [ih]
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_sub hle, ZMod.natCast_self, Nat.cast_pow]
    ring

theorem dotB_consFrom_le (K p b0 : ℕ) (hp : 0 < p) : ∀ (tup : List (ℕ × ℕ)) (o : ℕ), (∀ ab ∈ tup, ab.1 ≤ K ∧ ab.2 ≤ K) →
    dotB (encT K (flatP tup)) (consFrom K p b0 o tup.length) ≤ 2 * tup.length * (p - 1)
  | [], _, _ => by simp [flatP, encT, consFrom, dotB]
  | (a, b) :: tl, o, h => by
    have ha := (h (a, b) (by simp)).1
    have hb := (h (a, b) (by simp)).2
    rw [flatP_cons]
    simp only [encT, List.flatMap_cons, List.length_cons, consFrom]
    rw [dotB_append _ _ _ _ (by simp), dotB_append _ _ _ _ (by simp),
      dotB_ohB K a _ ha, dotB_ohB K b _ hb]
    have ih := dotB_consFrom_le K p b0 hp tl (o + 1) (fun ab hab => h ab (by simp [hab]))
    simp only [encT] at ih
    have h1 : b0 ^ o * a % p ≤ p - 1 := by have := Nat.mod_lt (b0 ^ o * a) hp; omega
    have h2 : (p - b0 ^ o % p) * b % p ≤ p - 1 := by have := Nat.mod_lt ((p - b0 ^ o % p) * b) hp; omega
    rw [Nat.mul_add]; nlinarith

/-! ## The RADIX row's output is `exprWord (radixExpr …)` -/

theorem flatMap_range_getD {α β : Type} (g : α → List β) (d : α) :
    ∀ l : List α, (List.range l.length).flatMap (fun i => g (l.getD i d)) = l.flatMap g
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [flatMap_range_getD g d l]

theorem flatMap_filter' {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ l : List α, (l.filter p).flatMap f = l.flatMap fun x => if p x then f x else []
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons]
    cases h : p a <;> simp [h, flatMap_filter' p f l]

theorem mem_allTuples_bound {K n : ℕ} {tup : List (ℕ × ℕ)} (h : tup ∈ allTuples K n) :
    tup.length = n ∧ ∀ ab ∈ tup, ab.1 ≤ K ∧ ab.2 ≤ K := by
  have hm : flatP tup ∈ lexT K (2 * n) := by rw [← allTuples_flat]; exact List.mem_map_of_mem h
  obtain ⟨h1, h2⟩ := mem_lexT hm
  refine ⟨by rw [flatP_length] at h1; omega, fun ab hab => ⟨h2 _ ?_, h2 _ ?_⟩⟩
  · simp only [flatP, List.mem_flatMap]; exact ⟨ab, hab, by simp⟩
  · simp only [flatP, List.mem_flatMap]; exact ⟨ab, hab, by simp⟩

theorem flatMap_congr_mem {α β : Type} (f g : α → List β) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), flatMap_congr_mem f g l (fun x hx => h x (by simp [hx]))]

theorem radOut_eq (τ₀ K p b0 : ℕ) [NeZero p] (Pp Pm : ℕ → ℕ → Poly) (s : ZMod p) :
    radOut K (2 * τ₀) (consFrom K p b0 0 τ₀) (patT p s.val (2 * τ₀ * p + 1)) (storeFrom K Pp Pm 0 τ₀) =
      Rec.exprWord (radixExpr τ₀ K p b0 Pp Pm s) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold radOut radW radAt Rec.exprWord radixExpr
  congr 1
  have e1 : (List.range ((K + 1) ^ (2 * τ₀))).flatMap
      (fun i => radTermOr K (consFrom K p b0 0 τ₀) (patT p s.val (2 * τ₀ * p + 1)) (storeFrom K Pp Pm 0 τ₀)
        (tupAt K (2 * τ₀) i)) =
      (lexT K (2 * τ₀)).flatMap (radTermOr K (consFrom K p b0 0 τ₀) (patT p s.val (2 * τ₀ * p + 1))
        (storeFrom K Pp Pm 0 τ₀)) := by
    rw [← flatMap_range_getD _ (List.replicate (2 * τ₀) 0) (lexT K (2 * τ₀)), length_lexT]
    rfl
  rw [e1, ← allTuples_flat, List.flatMap_map, List.flatMap_map, flatMap_filter']
  refine flatMap_congr_mem _ _ _ fun tup htup => ?_
  obtain ⟨hlen, hb⟩ := mem_allTuples_bound htup
  subst hlen
  have hD := dotB_consFrom_le K p b0 hp tup 0 hb
  have hZ := dotB_consFrom K p b0 hp tup 0 hb
  simp only [radTermOr]
  rw [patT_read _ _ _ _ (by
    have : 2 * tup.length * (p - 1) < 2 * tup.length * p + 1 := by
      have := Nat.mul_le_mul_left (2 * tup.length) (Nat.sub_le p 1); omega
    omega)]
  have hacc : decide (dotB (encT K (flatP tup)) (consFrom K p b0 0 tup.length) % p = s.val) =
      decide (((tupleValue b0 0 tup : ℤ) : ZMod p) = s) := by
    rw [← hZ]
    apply decide_eq_decide.mpr
    rw [← ZMod.val_natCast]
    exact ⟨fun h => ZMod.val_injective p h, fun h => by rw [h]⟩
  rw [hacc]
  split_ifs
  · simp [radTerm, Rec.termWord, mselW_storeFrom K Pp Pm tup 0 hb, List.append_assoc]
  · rfl

end NearCubicWires.WireExponent3_5.ListMachine.Row
