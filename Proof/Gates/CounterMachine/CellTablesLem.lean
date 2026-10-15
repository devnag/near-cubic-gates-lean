import Proof.Gates.CounterMachine.CellTablesSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.CellTables

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## Bits of a framed record -/

theorem frame_getD_even : ∀ (u : List Bool) (k : ℕ), k < u.length → (frame u).getD (2 * k) false = true
  | [], k, h => by simp at h
  | b :: u, 0, _ => by simp [frame]
  | b :: u, k + 1, h => by
    simp only [frame, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.getD_cons_succ]
    exact frame_getD_even u k (by simpa using h)

theorem frame_getD_odd : ∀ (u : List Bool) (k : ℕ), (frame u).getD (2 * k + 1) false = u.getD k false
  | [], k => by cases k <;> simp [frame]
  | b :: u, 0 => by simp [frame]
  | b :: u, k + 1 => by
    simp only [frame, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, List.getD_cons_succ]
    exact frame_getD_odd u k

theorem frame_getD_end : ∀ u : List Bool, (frame u).getD (2 * u.length) false = false
  | [] => by simp [frame]
  | b :: u => by
    simp only [frame, List.length_cons, show 2 * (u.length + 1) = 2 * u.length + 1 + 1 by ring,
      List.getD_cons_succ]
    exact frame_getD_end u

theorem frame_length' (u : List Bool) : (frame u).length = 2 * u.length + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frame, ih]; ring

/-- Bit `k` of `binary w v` (low bit first). -/
theorem binary_getD_bit : ∀ (w v k : ℕ), k < w → (binary w v).getD k false = (v / 2 ^ k % 2 == 1)
  | 0, v, k, h => by omega
  | w + 1, v, 0, _ => by simp [binary]
  | w + 1, v, k + 1, h => by
    simp only [binary, List.getD_cons_succ]
    rw [binary_getD_bit w (v / 2) k (by omega), Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (2 ^ k) 2]

theorem toNat_bit (x : ℕ) : (x % 2 == 1).toNat = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- `binary` grows at the high end. -/
theorem binary_snoc : ∀ (j v : ℕ), binary (j + 1) v = binary j v ++ [v / 2 ^ j % 2 == 1]
  | 0, v => by simp [binary]
  | j + 1, v => by
    rw [show j + 1 + 1 = (j + 1) + 1 from rfl, binary, binary_snoc j (v / 2), binary, List.cons_append,
      Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (2 ^ j) 2]

/-! ## The printer order -/

theorem rows_length (a b : ℕ) (f : ℕ → ℕ → ℕ) :
    ((List.range a).flatMap fun i => (List.range b).map (f i)).length = a * b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem rows_getElem? (b : ℕ) (f : ℕ → ℕ → ℕ) :
    ∀ (a i j : ℕ), i < a → j < b →
      ((List.range a).flatMap fun i => (List.range b).map (f i))[i * b + j]? = some (f i j) := by
  intro a
  induction a with
  | zero => intro i j hi; omega
  | succ a ih =>
    intro i j hi hj
    rw [List.range_succ, List.flatMap_append]
    by_cases hia : i < a
    · rw [List.getElem?_append_left (by rw [rows_length]; nlinarith)]
      exact ih i j hia hj
    · have hie : i = a := by omega
      subst hie
      rw [List.getElem?_append_right (by rw [rows_length]; omega), rows_length]
      simp [hj]

theorem printerOrder_length (s : ℕ) : (printerOrder s).length = 2 ^ s := by
  unfold printerOrder
  rw [rows_length, ← pow_add]
  congr 1; omega

theorem printerOrder_getElem? (s r j : ℕ) (hr : r < 2 ^ ((s + 1) / 2)) (hj : j < 2 ^ (s / 2)) :
    (printerOrder s)[r * 2 ^ (s / 2) + j]? = some (r + 2 ^ ((s + 1) / 2) * j) := by
  unfold printerOrder
  exact rows_getElem? (2 ^ (s / 2)) (fun i j => i + 2 ^ ((s + 1) / 2) * j) _ r j hr hj

theorem pow_split (s : ℕ) : 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) = 2 ^ s := by
  rw [← pow_add]; congr 1; omega

theorem index_lt (s r j : ℕ) (hr : r < 2 ^ ((s + 1) / 2)) (hj : j < 2 ^ (s / 2)) :
    r + 2 ^ ((s + 1) / 2) * j < 2 ^ s := by
  rw [← pow_split s]
  have : 2 ^ ((s + 1) / 2) * (j + 1) ≤ 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) := Nat.mul_le_mul_left _ hj
  nlinarith

theorem mem_printerOrder_lt {s i : ℕ} (h : i ∈ printerOrder s) : i < 2 ^ s := by
  unfold printerOrder at h
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨r, hr, j, hj, rfl⟩ := h
  exact index_lt s r j hr hj

/-! ## Record streams -/

theorem recStream_cons (w : List Bool) (ws : List (List Bool)) :
    WordPrograms.recStream (w :: ws) = frame w ++ WordPrograms.recStream ws := by
  simp [WordPrograms.recStream, List.append_assoc]

theorem drop_cons_getElem {α : Type} (l : List α) (t : ℕ) (x : α) (h : l[t]? = some x) :
    l.drop t = x :: l.drop (t + 1) := by
  have ht : t < l.length := by
    rcases Nat.lt_or_ge t l.length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at h; cases h
  rw [List.drop_eq_getElem_cons ht]
  congr
  rw [List.getElem?_eq_getElem ht] at h
  exact Option.some.inj h

theorem take_succ_getElem {α : Type} (l : List α) (t : ℕ) (x : α) (h : l[t]? = some x) :
    l.take (t + 1) = l.take t ++ [x] := by
  rw [List.take_add_one, h]; rfl

/-! ## The value of a table entry -/

/-- The value the program computes from the entry word `v = encS z`: residue requests (`res`) reduce modulo `QE`
(`Int.emod`), moments keep `z.toNat`. -/
def valOf (res : Bool) (QE v : ℕ) : ℕ :=
  if res then (if v % 2 = 1 ∧ v / 2 % QE ≠ 0 then QE - v / 2 % QE else v / 2 % QE)
  else (if v % 2 = 1 then 0 else v / 2)

theorem emod_neg_toNat (m Q : ℕ) (hQ : 0 < Q) :
    ((-(m : ℤ)) % (Q : ℤ)).toNat = if m % Q ≠ 0 then Q - m % Q else 0 := by
  have hm : (m : ℤ) = (Q : ℤ) * ((m / Q : ℕ) : ℤ) + ((m % Q : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod m Q).symm
  have hlt : m % Q < Q := Nat.mod_lt m hQ
  split_ifs with h
  · have e : -(m : ℤ) = ((Q - m % Q : ℕ) : ℤ) + (Q : ℤ) * (-((m / Q : ℕ) : ℤ) - 1) := by
      rw [hm]; push_cast [Nat.cast_sub hlt.le]; ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by omega)]
    simp
  · have h0 : m % Q = 0 := by omega
    have e : -(m : ℤ) = (Q : ℤ) * (-((m / Q : ℕ) : ℤ)) := by rw [hm, h0]; push_cast; ring
    rw [e, Int.mul_emod_right]; rfl

theorem valOf_encS (res : Bool) (QE : ℕ) (z : ℤ) (hQ : res = true → 0 < QE) :
    valOf res QE (WordPrograms.SInt.encS z) = if res then (z % (QE : ℤ)).toNat else z.toNat := by
  unfold valOf
  rw [WordPrograms.SInt.encS_div, WordPrograms.SInt.encS_mod]
  rcases lt_or_ge z 0 with hz | hz
  · have hzm : z = -((z.natAbs : ℕ) : ℤ) := by omega
    rw [if_pos hz]
    cases res
    · simp only [Bool.false_eq_true, if_false, if_true]; omega
    · simp only [if_true, true_and]
      rw [hzm, emod_neg_toNat _ _ (hQ rfl), Int.natAbs_neg, Int.natAbs_natCast]
      split_ifs with h1 <;> omega
  · have hzm : z = ((z.natAbs : ℕ) : ℤ) := by omega
    have hnz : ¬ z < 0 := by omega
    rw [if_neg hnz]
    cases res
    · simp only [Bool.false_eq_true, if_false, show ¬ ((0 : ℕ) = 1) by omega]; omega
    · simp only [if_true, show ¬ ((0 : ℕ) = 1) by omega, false_and, if_false]
      conv_rhs => rw [hzm]
      rw [← Int.natCast_mod, Int.toNat_natCast]

/-! ## The sort with a sentinel -/

theorem insertionSort_sentinel (recs : List ℕ) (S : ℕ) (h : ∀ v ∈ recs, v < S) :
    (recs ++ [S]).insertionSort (· ≤ ·) = recs.insertionSort (· ≤ ·) ++ [S] := by
  refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) ?_ ?_
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_insertionSort _ _, by simp, ?_⟩
    intro a ha b hb
    rw [(List.perm_insertionSort _ _).mem_iff] at ha
    simp at hb; subst hb; exact (h a ha).le
  · exact (List.perm_insertionSort _ _).trans (List.Perm.append_right _ (List.perm_insertionSort _ _).symm)

/-! ## The scratch variables -/

theorem mem_scr (y : Fin VV) : y ∈ scr ↔ 48 ≤ y.val ∧ y.val < 64 := by
  unfold scr
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; simp [Nat.mod_eq_of_lt hj]; omega
  · rintro ⟨h1, h2⟩
    refine ⟨y.val - 48, by omega, ?_⟩
    ext; simp [Nat.mod_eq_of_lt (show y.val - 48 < 16 by omega)]; omega

/-! ## Frames of the fragments -/

/-- Everything but the variables and the output agrees. -/
structure SameO (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem SameO.refl (a : DS VV MM) : SameO a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameO.trans {a b d : DS VV MM} (h1 : SameO a b) (h2 : SameO b d) : SameO a d :=
  ⟨h2.ip.trans h1.ip, h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kin.trans h1.kin, h2.kout.trans h1.kout,
    h2.kc.trans h1.kc⟩

theorem SameO.set (a : DS VV MM) (x : Fin VV) (v : ℕ) : SameO a (a.set x v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameO.out (a : DS VV MM) (o : List Bool) : SameO a { a with out := o } := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.refl (a : DS VV MM) : Frame a a :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {a b d : DS VV MM} (h1 : Frame a b) (h2 : Frame b d) : Frame a d :=
  ⟨Fr.trans h1.fr h2.fr, h2.ip.trans h1.ip, h2.kin.trans h1.kin, h2.kout.trans h1.kout,
    fun m h h' => (h2.ram m h h').trans (h1.ram m h h'), fun m h h' => (h2.rc m h h').trans (h1.rc m h h')⟩

theorem Frame.of_sameO {a b : DS VV MM} {T : List (Fin VV)} (hf : Fr a b T) (hT : ∀ y ∈ T, y ∈ scr)
    (hs : SameO a b) : Frame a b :=
  ⟨Fr.weaken hf hT, hs.ip, hs.kin, hs.kout, fun m _ _ => by rw [hs.ram], fun m _ _ => by rw [hs.rc]⟩

theorem Frame.set (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x ∈ scr) : Frame a (a.set x v) :=
  ⟨Fr.set a v hx, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.out (a : DS VV MM) (o : List Bool) : Frame a { a with out := o } :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.kc (a : DS VV MM) (k : ℕ) : Frame a { a with kc := k } :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.put (a : DS VV MM) (v : ℕ) : Frame a (a.put sREC v) :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun m h _ => by simp [DS.put, Function.update_of_ne h],
    fun m h _ => by simp [DS.put, Function.update_of_ne h]⟩

theorem Frame.adv (a : DS VV MM) : Frame a (a.adv sREC) :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl, fun m h _ => by simp [DS.adv, Function.update_of_ne h]⟩

theorem Frame.rew (a : DS VV MM) : Frame a (a.rew sREC) :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl, fun m h _ => by simp [DS.rew, Function.update_of_ne h]⟩

theorem Frame.srt (a : DS VV MM) : Frame a (a.srt sREC) :=
  ⟨Fr.refl _ _, rfl, rfl, rfl, fun m h _ => by simp [DS.srt, Function.update_of_ne h], fun _ _ _ => rfl⟩

theorem Frame.env_lo {a b : DS VV MM} (h : Frame a b) (y : Fin VV) (hy : y.val < 48) : b.env y = a.env y :=
  h.fr y (fun hm => by rw [mem_scr] at hm; omega)

theorem Frame.cst {a b : DS VV MM} (h : Frame a b) (hc : Cst a) : Cst b :=
  ⟨by rw [h.env_lo vZ (by decide)]; exact hc.z, by rw [h.env_lo v1 (by decide)]; exact hc.one,
    by rw [h.env_lo v2 (by decide)]; exact hc.two⟩

/-- Print the bit held (`0`/`1`) in `x`. -/
def emitV (x : Fin VV) : St VV MM := .ite (.eq x v1) (.op (.emit true)) (.op (.emit false))

theorem emitV_spec (C : Ctx) (x : Fin VV) (hx : x ≠ v1) (e : DS VV MM) (hc : Cst e) :
    Hs C (emitV x) e 2 (· = { e with out := e.out ++ [decide (e.env x = 1)] }) := by
  refine Hs.ite (c := .eq x v1) hx (fun h => ?_) (fun h => ?_)
  · have h1 : e.env x = 1 := by simpa [Cnd.eval, hc.one] using h
    refine Hs.mono (hs_emit C true e) le_rfl ?_
    rintro d rfl; simp [h1]
  · have h1 : e.env x ≠ 1 := by simpa [Cnd.eval, hc.one] using h
    refine Hs.mono (hs_emit C false e) le_rfl ?_
    rintro d rfl; simp [h1]

end NearCubicGates.Close.CounterMachine.CellTables
