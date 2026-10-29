import SourceAdapters.Compile.CNFStack
import SourceAdapters.Compile.CNFRunOK

/-!
# The balanced encoder, part A: the explicit-stack evaluation of `encodeBalancedList`

proof of `lem:multitape-refuter`: the query uses the native balanced outer coding of the clause list (`encodeBalancedList`,
`Statement.lean:74`: midpoint split, left half `⌈len/2⌉`). The printing program evaluates it without recursion:
a task stack (`0` combine, `len + 1` evaluate the next `len` leaves) and a value stack; leaves are read in order.
`bstep` is one pass; `brun` proves that `bcnt len` passes evaluate the next `len` leaves, and that every pass on the
way is in range (`bok`: the combined value is at most the whole code `B`, a leaf is in the list, heights `≤ Hb`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.CanonicalBinary
set_option autoImplicit false

/-- The encoder state: task stack, value stack (tops first), leaves consumed. -/
structure BS where
  tk : List ℕ
  vs : List ℕ
  p : ℕ

/-- One pass. -/
def bstep (cl : List ℕ) (S : BS) : BS :=
  match S.tk with
  | [] => S
  | 0 :: ts => ⟨ts, Nat.pair 2 (Nat.pair (popS (popS S.vs).2).1 (popS S.vs).1) :: (popS (popS S.vs).2).2, S.p⟩
  | 1 :: ts => ⟨ts, 0 :: S.vs, S.p⟩
  | 2 :: ts => ⟨ts, Nat.pair 1 (cl.getD S.p 0) :: S.vs, S.p + 1⟩
  | (c + 3) :: ts => ⟨((c + 3) / 2 + 1) :: (c + 2 - (c + 3) / 2 + 1) :: 0 :: ts, S.vs, S.p⟩

/-- The number of passes evaluating `len` leaves. -/
def bcnt : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | c + 2 => bcnt ((c + 3) / 2) + bcnt (c + 2 - (c + 3) / 2) + 2
termination_by n => n
decreasing_by all_goals omega

theorem bcnt_le : ∀ len, bcnt len ≤ 3 * len + 1 := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
      match len with
      | 0 => simp [bcnt]
      | 1 => simp [bcnt]
      | c + 2 =>
          rw [bcnt]
          have h1 := ih ((c + 3) / 2) (by omega)
          have h2 := ih (c + 2 - (c + 3) / 2) (by omega)
          -- sharper: bcnt l ≤ 3 l - 2 for l ≥ 1
          have k1 : ∀ l, 1 ≤ l → l < c + 2 → bcnt l + 2 ≤ 3 * l := by
            intro l hl hlc
            clear h1 h2
            induction l using Nat.strong_induction_on with
            | h l ihl =>
                match l with
                | 0 => omega
                | 1 => simp [bcnt]
                | d + 2 =>
                    rw [bcnt]
                    have g1 := ihl ((d + 3) / 2) (by omega) (by omega) (by omega)
                    have g2 := ihl (d + 2 - (d + 3) / 2) (by omega) (by omega) (by omega)
                    omega
          have g1 := k1 ((c + 3) / 2) (by omega) (by omega)
          have g2 := k1 (c + 2 - (c + 3) / 2) (by omega) (by omega)
          omega

theorem bcnt_pos (l : ℕ) : 1 ≤ bcnt l := by
  match l with
  | 0 => simp [bcnt]
  | 1 => simp [bcnt]
  | c + 2 => rw [bcnt]; omega

/-- The next `len` leaves from position `p`. -/
def seg (cl : List ℕ) (p len : ℕ) : List ℕ := (cl.drop p).take len

theorem seg_length (cl : List ℕ) (p len : ℕ) (h : p + len ≤ cl.length) : (seg cl p len).length = len := by
  simp [seg]; omega

theorem encodeBalancedList_split (l : List ℕ) (hl : 2 ≤ l.length) :
    encodeBalancedList l = Nat.pair 2 (Nat.pair (encodeBalancedList (l.take ((l.length + 1) / 2)))
      (encodeBalancedList (l.drop ((l.length + 1) / 2)))) := by
  match l, hl with
  | x :: y :: rest, _ => rw [encodeBalancedList]

theorem seg_take (cl : List ℕ) (p len h : ℕ) (hh : h ≤ len) : (seg cl p len).take h = seg cl p h := by
  simp [seg, List.take_take, Nat.min_eq_left hh]

theorem seg_drop (cl : List ℕ) (p len h : ℕ) : (seg cl p len).drop h = seg cl (p + h) (len - h) := by
  simp [seg, List.drop_take, List.drop_drop]

/-- The heights stay below `Hb`. -/
def hgt (Hb : ℕ) (S : BS) : Prop := S.tk.length + S.vs.length ≤ Hb

/-- The pass from `S` is in range: a task is pending, task codes are at most `|cl| + 1`, a combined value is at most
`B`, a leaf is in the list and its value is at most `B`. -/
def bok (cl : List ℕ) (B : ℕ) (S : BS) : Prop :=
  S.tk ≠ [] ∧ ∀ c ts, S.tk = c :: ts → c ≤ cl.length + 1 ∧
    (c = 0 → Nat.pair 2 (Nat.pair (popS (popS S.vs).2).1 (popS S.vs).1) ≤ B) ∧
    (c = 2 → S.p < cl.length ∧ Nat.pair 1 (cl.getD S.p 0) ≤ B)

theorem iter_split {α : Type} (f : α → α) (x : α) (m n : ℕ) : f^[m + n] x = f^[m] (f^[n] x) :=
  Function.iterate_add_apply f m n x

/-- **The stack evaluation is correct and in range.** -/
theorem brun (cl : List ℕ) (B Hb : ℕ) : ∀ len ts vs p, p + len ≤ cl.length →
    encodeBalancedList (seg cl p len) ≤ B → ts.length + vs.length + 3 * len + 1 ≤ Hb →
    (∀ j ≤ bcnt len, hgt Hb ((bstep cl)^[j] ⟨(len + 1) :: ts, vs, p⟩)) ∧
    (∀ j < bcnt len, bok cl B ((bstep cl)^[j] ⟨(len + 1) :: ts, vs, p⟩)) ∧
    (bstep cl)^[bcnt len] ⟨(len + 1) :: ts, vs, p⟩ = ⟨ts, encodeBalancedList (seg cl p len) :: vs, p + len⟩ := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
      intro ts vs p hp hB hH
      match len, ih, hp, hB, hH with
      | 0, _, hp, hB, hH =>
          have e : (bstep cl)^[1] ⟨(0 + 1) :: ts, vs, p⟩ = ⟨ts, 0 :: vs, p⟩ := rfl
          refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
          · simp only [bcnt] at hj
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
            · simp [hgt]; omega
            · rw [e]; simp [hgt]; omega
          · simp only [bcnt] at hj
            obtain rfl : j = 0 := by omega
            refine ⟨by simp, fun c ts' h => ?_⟩
            simp at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨by omega, by omega, by omega⟩
          · simp only [bcnt]; rw [e]; simp [seg, encodeBalancedList]
      | 1, _, hp, hB, hH =>
          have hs : seg cl p 1 = [cl.getD p 0] := by
            have hp' : p < cl.length := by omega
            unfold seg
            rw [List.drop_eq_getElem_cons hp', List.take_succ_cons, List.take_zero, List.getD_eq_getElem _ _ hp']
          have e : (bstep cl)^[1] ⟨(1 + 1) :: ts, vs, p⟩ = ⟨ts, Nat.pair 1 (cl.getD p 0) :: vs, p + 1⟩ := rfl
          rw [hs, encodeBalancedList] at hB ⊢
          refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
          · simp only [bcnt] at hj
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
            · simp [hgt]; omega
            · rw [e]; simp [hgt]; omega
          · simp only [bcnt] at hj
            obtain rfl : j = 0 := by omega
            refine ⟨by simp, fun c ts' h => ?_⟩
            simp at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨by omega, by omega, fun _ => ⟨by simp; omega, by simpa using hB⟩⟩
          · simp only [bcnt]; rw [e]
      | c + 2, ih, hp, hB, hH =>
          set len := c + 2 with hlen
          set h := (c + 3) / 2 with hh
          have hh1 : 1 ≤ h := by omega
          have hh2 : h < len := by omega
          have hsplit := encodeBalancedList_split (seg cl p len) (by rw [seg_length cl p len hp]; omega)
          rw [seg_length cl p len hp, show (len + 1) / 2 = h by omega, seg_take cl p len h (by omega),
            seg_drop] at hsplit
          set E1 := encodeBalancedList (seg cl p h) with hE1
          set E2 := encodeBalancedList (seg cl (p + h) (len - h)) with hE2
          have hE1B : E1 ≤ B := by
            have := Nat.left_le_pair E1 E2; have := Nat.right_le_pair 2 (Nat.pair E1 E2); omega
          have hE2B : E2 ≤ B := by
            have := Nat.right_le_pair E1 E2; have := Nat.right_le_pair 2 (Nat.pair E1 E2); omega
          set S0 : BS := ⟨(len + 1) :: ts, vs, p⟩ with hS0
          set S1 : BS := ⟨(h + 1) :: (len - h + 1) :: 0 :: ts, vs, p⟩ with hS1
          have e1 : bstep cl S0 = S1 := rfl
          obtain ⟨g1, k1, f1⟩ := ih h (by omega) ((len - h + 1) :: 0 :: ts) vs p (by omega) hE1B
            (by simp only [List.length_cons]; omega)
          set S2 : BS := ⟨(len - h + 1) :: 0 :: ts, E1 :: vs, p + h⟩ with hS2
          obtain ⟨g2, k2, f2⟩ := ih (len - h) (by omega) (0 :: ts) (E1 :: vs) (p + h) (by omega) hE2B
            (by simp only [List.length_cons]; omega)
          set S3 : BS := ⟨0 :: ts, E2 :: E1 :: vs, p + h + (len - h)⟩ with hS3
          have e3 : bstep cl S3 = ⟨ts, encodeBalancedList (seg cl p len) :: vs, p + len⟩ := by
            simp only [hS3, bstep, popS, hsplit]
            congr 1; omega
          have hcnt : bcnt len = 1 + bcnt (len - h) + bcnt h + 1 := by
            rw [hlen, hh, bcnt]; omega
          -- the iterates by ranges
          have rA : ∀ j ≤ bcnt h, (bstep cl)^[j + 1] S0 = (bstep cl)^[j] S1 := by
            intro j _; rw [Function.iterate_succ_apply, e1]
          have rB : ∀ j ≤ bcnt (len - h), (bstep cl)^[j + bcnt h + 1] S0 = (bstep cl)^[j] S2 := by
            intro j _; rw [Nat.add_assoc, iter_split, rA _ le_rfl, f1]
          have rC : (bstep cl)^[bcnt len] S0 = bstep cl S3 := by
            rw [hcnt, show 1 + bcnt (len - h) + bcnt h + 1 = 1 + (bcnt (len - h) + bcnt h + 1) by omega, iter_split,
              rB _ le_rfl, f2]; rfl
          have cover : ∀ j ≤ bcnt len, j = 0 ∨ (∃ i ≤ bcnt h, j = i + 1) ∨
              (∃ i ≤ bcnt (len - h), j = i + bcnt h + 1) ∨ j = bcnt len := by
            intro j hj
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · exact Or.inl h0
            · by_cases hj1 : j ≤ bcnt h + 1
              · exact Or.inr (Or.inl ⟨j - 1, by omega, by omega⟩)
              · by_cases hj2 : j ≤ bcnt (len - h) + bcnt h + 1
                · exact Or.inr (Or.inr (Or.inl ⟨j - bcnt h - 1, by omega, by omega⟩))
                · exact Or.inr (Or.inr (Or.inr (by omega)))
          refine ⟨fun j hj => ?_, fun j hj => ?_, by rw [rC, e3]⟩
          · rcases cover j hj with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
            · simp [hgt, hS0]; omega
            · rw [rA i hi]; exact g1 i hi
            · rw [rB i hi]; exact g2 i hi
            · rw [rC, e3]; simp [hgt]; omega
          · rcases cover j (by omega) with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
            · refine ⟨by simp [hS0], fun c' ts' hc => ?_⟩
              simp [hS0] at hc; obtain ⟨rfl, rfl⟩ := hc
              exact ⟨by omega, by omega, by omega⟩
            · by_cases hi' : i < bcnt h
              · rw [rA i hi]; exact k1 i hi'
              · obtain rfl : i = bcnt h := by omega
                rw [rA _ le_rfl, f1]
                exact k2 0 (bcnt_pos _)
            · by_cases hi' : i < bcnt (len - h)
              · rw [rB i hi]; exact k2 i hi'
              · obtain rfl : i = bcnt (len - h) := by omega
                rw [rB _ le_rfl, f2]
                refine ⟨by simp [hS3], fun c' ts' hc => ?_⟩
                simp [hS3] at hc; obtain ⟨rfl, rfl⟩ := hc
                refine ⟨by omega, fun _ => ?_, by omega⟩
                simp only [hS3, popS]
                rw [← hsplit]; exact hB
            · omega

end NearCubicGates.Adapters.Compile
