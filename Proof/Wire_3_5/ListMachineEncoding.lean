import Proof.Foundations.OrdinaryStreaming

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Rec
open NearCubicWires.RepairOrdinary

/-! ## The fields -/

/-- A coordinate index in unary. -/
def atomCode (i : ℕ) : List Bool := List.replicate i true ++ [false]

/-- The bits of a monomial: its atoms' codes. -/
def monoBits (m : List ℕ) : List Bool := m.flatMap atomCode

theorem monoBits_append (a b : List ℕ) : monoBits (a ++ b) = monoBits a ++ monoBits b := by
  simp [monoBits]

/-- A monomial record. -/
def recW (m : List ℕ) : List Bool := true :: frame (monoBits m)

@[simp] theorem recW_length (m : List ℕ) : (recW m).length = 2 * (monoBits m).length + 2 := by
  simp [recW, frame_length]

/-- A polynomial: its monomial records, then `false`. -/
def polyWord (p : List (List ℕ)) : List Bool := p.flatMap recW ++ [false]

/-- A coefficient: its sign, then the little-endian bits of its magnitude, framed. -/
def coefWord (c : ℤ) : List Bool := frame (decide (c < 0) :: Nat.bits c.natAbs)

/-- A term: its coefficient, then its factor records `true :: polyWord f`, then `false`. -/
def termWord (t : ℤ × List (List (List ℕ))) : List Bool :=
  coefWord t.1 ++ (t.2.flatMap (fun f => true :: polyWord f) ++ [false])

/-- An integer expression (S0's `IntExpression ℕ`): its term records `true :: termWord t`, then `false`. -/
def exprWord (V : List (ℤ × List (List (List ℕ)))) : List Bool :=
  V.flatMap (fun t => true :: termWord t) ++ [false]

/-! ## Self-delimiting fields -/

/-- `enc` is a prefix code: an encoded value followed by anything determines both. -/
def PrefixInj {α : Type} (enc : α → List Bool) : Prop :=
  ∀ a b : α, ∀ r s : List Bool, enc a ++ r = enc b ++ s → a = b ∧ r = s

theorem frame_prefixInj : PrefixInj frame := by
  intro x
  induction x with
  | nil =>
    intro y r s h
    cases y with
    | nil => simpa [frame] using h
    | cons b y => simp [frame] at h
  | cons a x ih =>
    intro y r s h
    cases y with
    | nil => simp [frame] at h
    | cons b y =>
      simp only [frame, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hab, h⟩ := h
      obtain ⟨hxy, hrs⟩ := ih y r s h
      exact ⟨by rw [hab, hxy], hrs⟩

theorem atomCode_prefixInj : PrefixInj atomCode := by
  intro i
  induction i with
  | zero =>
    intro j r s h
    cases j with
    | zero => simpa [atomCode] using h
    | succ j => simp [atomCode, List.replicate_succ] at h
  | succ i ih =>
    intro j r s h
    cases j with
    | zero => simp [atomCode, List.replicate_succ] at h
    | succ j =>
      have h' : atomCode i ++ r = atomCode j ++ s := by simpa [atomCode, List.replicate_succ] using h
      obtain ⟨hij, hrs⟩ := ih j r s h'
      exact ⟨by rw [hij], hrs⟩

/-- A concatenation of nonempty prefix-code words determines its list. -/
theorem flatMap_injective {α : Type} (enc : α → List Bool) (h : PrefixInj enc) (hne : ∀ a, enc a ≠ []) :
    Function.Injective (fun l : List α => l.flatMap enc) := by
  intro l
  induction l with
  | nil =>
    intro l' h'
    cases l' with
    | nil => rfl
    | cons b l' =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h'
      cases hb : enc b with
      | nil => exact absurd hb (hne b)
      | cons x xs => rw [hb] at h'; simp at h'
  | cons a l ih =>
    intro l' h'
    cases l' with
    | nil =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h'
      cases ha : enc a with
      | nil => exact absurd ha (hne a)
      | cons x xs => rw [ha] at h'; simp at h'
    | cons b l' =>
      simp only [List.flatMap_cons] at h'
      obtain ⟨hab, hrest⟩ := h a b _ _ h'
      rw [hab, ih hrest]

theorem monoBits_injective : Function.Injective monoBits :=
  flatMap_injective atomCode atomCode_prefixInj (by simp [atomCode])

/-- A `true`-marked record list ended by `false`, of a prefix code, is a prefix code. -/
theorem records_prefixInj {α : Type} (enc : α → List Bool) (h : PrefixInj enc) :
    PrefixInj (fun l : List α => l.flatMap (fun a => true :: enc a) ++ [false]) := by
  intro l
  induction l with
  | nil =>
    intro l' r s h'
    cases l' with
    | nil => simpa using h'
    | cons b l' => simp at h'
  | cons a l ih =>
    intro l' r s h'
    cases l' with
    | nil => simp at h'
    | cons b l' =>
      simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h'
      obtain ⟨hab, hrs⟩ := h a b _ _ h'
      obtain ⟨hl, hr⟩ := ih l' r s (by simpa [List.append_assoc] using hrs)
      exact ⟨by rw [hab, hl], hr⟩

theorem monoFrame_prefixInj : PrefixInj (fun m : List ℕ => frame (monoBits m)) := by
  intro a b r s h
  obtain ⟨h1, h2⟩ := frame_prefixInj _ _ r s h
  exact ⟨monoBits_injective h1, h2⟩

theorem polyWord_prefixInj : PrefixInj polyWord :=
  records_prefixInj (fun m : List ℕ => frame (monoBits m)) monoFrame_prefixInj

/-- `Nat.bits` determines its number (little-endian binary digits). -/
theorem bits_injective : Function.Injective Nat.bits := by
  have key : ∀ n : ℕ, (Nat.bits n).foldr (fun b acc => 2 * acc + b.toNat) 0 = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [Nat.zero_bits]
        · rw [Nat.bit0_bits k (by omega)]
          simp [ih k (by omega)]
      · rw [Nat.bit1_bits k]
        simp [ih k (by omega)]
  intro m n h
  rw [← key m, ← key n, h]

theorem coefWord_prefixInj : PrefixInj coefWord := by
  intro c d r s h
  obtain ⟨h1, h2⟩ := frame_prefixInj _ _ r s h
  simp only [List.cons.injEq] at h1
  obtain ⟨hsign, hbits⟩ := h1
  have habs := bits_injective hbits
  refine ⟨?_, h2⟩
  have hs : (c < 0 ↔ d < 0) := by simpa using hsign
  have e1 := Int.natAbs_eq c
  have e2 := Int.natAbs_eq d
  rw [habs] at e1
  omega

theorem termWord_prefixInj : PrefixInj termWord := by
  intro a b r s h
  have h' : coefWord a.1 ++ (a.2.flatMap (fun f => true :: polyWord f) ++ [false] ++ r) =
      coefWord b.1 ++ (b.2.flatMap (fun f => true :: polyWord f) ++ [false] ++ s) := by
    simpa [termWord, List.append_assoc] using h
  obtain ⟨h1, h2⟩ := coefWord_prefixInj a.1 b.1 _ _ h'
  obtain ⟨h3, h4⟩ := records_prefixInj polyWord polyWord_prefixInj a.2 b.2 r s h2
  exact ⟨Prod.ext h1 h3, h4⟩

/-- **The expression word is a prefix code**: `exprWord V ++ rest` determines `V` and `rest`. -/
theorem exprWord_prefixInj : PrefixInj exprWord :=
  records_prefixInj termWord termWord_prefixInj

theorem exprWord_injective : Function.Injective exprWord := fun V W h =>
  (exprWord_prefixInj V W [] [] (by rw [List.append_nil, List.append_nil, h])).1

theorem polyWord_injective : Function.Injective polyWord := fun p q h =>
  (polyWord_prefixInj p q [] [] (by rw [List.append_nil, List.append_nil, h])).1

end NearCubicWires.WireExponent3_5.ListMachine.Rec
