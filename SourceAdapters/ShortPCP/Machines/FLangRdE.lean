import SourceAdapters.ShortPCP.Machines.FLangDec
import SourceAdapters.ShortPCP.TimeStages

/-!
# Single-run time, machine layer 31: reading the answered entries

proof of `thm:short-pcp-ours` ("its proof bits are read at addresses below L_π"): after the generic reader stage the input of the
decision half is `readWord s L xs ans rest` (`TimeStages`): `1^s 0`, then one entry `1 0 0 b ++ frame (binary L a)`
per address `a` with its answer `b`, then `0`, then `rest`. `rdE` reads the entries from the input position `s + 1`
and leaves the answer bits as the number `16 := bitsValue ans` (`rdE_spec`), positioned at `rest`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable {G : Glob}

/-- One answered entry. -/
def entW (L a : ℕ) (b : Bool) : List Bool := true :: false :: false :: b :: frame (binary L a)

/-- The entries from number `j` on. -/
def entsFrom (L : ℕ) (xs : List ℕ) (ans : List Bool) (j : ℕ) : List Bool :=
  (List.zipWith (entW L) (xs.drop j) (ans.drop j)).flatten

theorem entsFrom_succ (L : ℕ) (xs : List ℕ) (ans : List Bool) (j : ℕ) (hj : j < xs.length)
    (hl : ans.length = xs.length) :
    entsFrom L xs ans j = entW L (xs.getD j 0) (ans.getD j false) ++ entsFrom L xs ans (j + 1) := by
  unfold entsFrom
  have hj' : j < ans.length := by omega
  rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hj', List.zipWith_cons_cons,
    List.flatten_cons, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj']

theorem entsFrom_end (L : ℕ) (xs : List ℕ) (ans : List Bool) : entsFrom L xs ans xs.length = [] := by
  simp [entsFrom]

theorem readWord_drop (s L : ℕ) (xs : List ℕ) (ans rest : List Bool) :
    (Time.readWord s L xs ans rest).drop (s + 1) = entsFrom L xs ans 0 ++ false :: rest := by
  unfold Time.readWord entsFrom
  rw [List.drop_append]
  simp [List.drop_replicate]
  rfl

/-- Reading one bit of the input. -/
theorem rd_cons (t : FS) (i : Var) (b : Bool) (w : List Bool) (h : G.inp.drop t.ip = b :: w) :
    evalS G (.rd i) t = { t.setv i b.toNat with ip := t.ip + 1 } ∧ G.inp.drop (t.ip + 1) = w := by
  have hlt : t.ip < G.inp.length := by
    by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at h; cases h
  have hb : G.inp.getD t.ip false = b := by
    rw [List.getD_eq_getElem _ _ hlt]
    have := congrArg List.head? h
    rw [List.head?_drop, List.head?_cons] at this
    rw [List.getElem?_eq_getElem hlt] at this
    exact Option.some.inj this
  refine ⟨by rw [evalS_rd G i t hlt, hb], ?_⟩
  rw [← List.drop_drop, h]; rfl

/-- The body: the entry's `0 0 b`, the answer bit into `16` at position `7`, the address frame, the next lead bit. -/
def rdEBody : S :=
  .seq (.rd 6) (.seq (.rd 6) (.seq (.rd 6) (.seq (.set 16 (.add (.v 16) (.shl (.v 6) (.v 7))))
    (.seq (.set 7 (.add (.v 7) (.k 1))) (.seq rdFrame (.rd 5))))))

/-- **The entry reader**: `16 := bitsValue ans`, `7 :=` the number of entries. -/
def rdE : S := .seq (.set 7 (.k 0)) (.seq (.set 16 (.k 0)) (.seq (.rd 5) (.whl (.v 5) rdEBody)))

/-- The variables of the entry reader. -/
def rdEW : List Var := [0, 1, 2, 3, 4, 5, 6, 7, 16]

theorem rd_wr (t : FS) (i : Var) (b : Bool) (hi : i ∈ rdEW) : Wr rdEW t { t.setv i b.toNat with ip := t.ip + 1 } :=
  ⟨fun j hj => by simp [Function.update_of_ne (show j ≠ i from fun h => hj (h ▸ hi))], rfl, rfl, rfl, rfl⟩

/-- The lead bit of entry `j` (or the closing `0`). -/
theorem lead_spec (u : FS) (L : ℕ) (xs : List ℕ) (ans rest : List Bool) (hl : ans.length = xs.length) (j : ℕ)
    (hj : j ≤ xs.length) (hin : G.inp.drop u.ip = entsFrom L xs ans j ++ false :: rest) :
    let u' := evalS G (.rd 5) u
    u'.env 5 = (if j < xs.length then 1 else 0) ∧ Wr rdEW u u' ∧ (∀ i, i ≠ 5 → u'.env i = u.env i) ∧
      ((j < xs.length ∧ G.inp.drop u'.ip = (entW L (xs.getD j 0) (ans.getD j false)).tail ++
          entsFrom L xs ans (j + 1) ++ false :: rest) ∨ (j = xs.length ∧ G.inp.drop u'.ip = rest)) := by
  intro u'
  by_cases h : j < xs.length
  · rw [entsFrom_succ L xs ans j h hl] at hin
    obtain ⟨e, d⟩ := rd_cons u 5 true _ (by rw [hin]; rfl)
    refine ⟨?_, ?_, ?_, Or.inl ⟨h, ?_⟩⟩
    · show (evalS G (.rd 5) u).env 5 = _; rw [e, if_pos h]; simp
    · show Wr rdEW u (evalS G (.rd 5) u); rw [e]; exact rd_wr u 5 true (by decide)
    · intro i hi; show (evalS G (.rd 5) u).env i = _; rw [e]; simp [Function.update_of_ne hi]
    · show G.inp.drop (evalS G (.rd 5) u).ip = _; rw [e]; rw [d]; simp [entW]
  · obtain rfl : j = xs.length := by omega
    rw [entsFrom_end] at hin
    obtain ⟨e, d⟩ := rd_cons u 5 false _ (by rw [hin]; rfl)
    refine ⟨?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · show (evalS G (.rd 5) u).env 5 = _; rw [e, if_neg h]; simp
    · show Wr rdEW u (evalS G (.rd 5) u); rw [e]; exact rd_wr u 5 false (by decide)
    · intro i hi; show (evalS G (.rd 5) u).env i = _; rw [e]; simp [Function.update_of_ne hi]
    · show G.inp.drop (evalS G (.rd 5) u).ip = _; rw [e]; exact d

theorem rd_step (t : FS) (i : Var) (hi : i ∈ rdEW) (b : Bool) (w : List Bool) (h : G.inp.drop t.ip = b :: w) :
    let t' := evalS G (.rd i) t
    t'.env i = b.toNat ∧ (∀ j, j ≠ i → t'.env j = t.env j) ∧ G.inp.drop t'.ip = w ∧ Wr rdEW t t' := by
  intro t'
  obtain ⟨e, d⟩ := rd_cons t i b w h
  refine ⟨?_, fun j hj => ?_, ?_, ?_⟩
  · show (evalS G (.rd i) t).env i = _; rw [e]; simp
  · show (evalS G (.rd i) t).env j = _; rw [e]; simp [Function.update_of_ne hj]
  · show G.inp.drop (evalS G (.rd i) t).ip = _; rw [e]; exact d
  · show Wr rdEW t (evalS G (.rd i) t); rw [e]; exact rd_wr t i b hi

/-- **One entry.** -/
theorem rdEBody_spec (u : FS) (L : ℕ) (xs : List ℕ) (ans rest : List Bool) (hl : ans.length = xs.length) (j : ℕ)
    (hj : j < xs.length) (h7 : u.env 7 = j) (h16 : u.env 16 = bitsValue (ans.take j))
    (hin : G.inp.drop u.ip = (entW L (xs.getD j 0) (ans.getD j false)).tail ++ entsFrom L xs ans (j + 1) ++
      false :: rest)
    (hK : xs.length + 2 ≤ G.K) (hL : L + 2 ≤ G.K) (hLN : L + 1 ≤ G.N) :
    let u' := evalS G rdEBody u
    u'.env 7 = j + 1 ∧ u'.env 16 = bitsValue (ans.take (j + 1)) ∧ Wr rdEW u u' ∧
      u'.env 5 = (if j + 1 < xs.length then 1 else 0) ∧
      ((j + 1 < xs.length ∧ G.inp.drop u'.ip = (entW L (xs.getD (j + 1) 0) (ans.getD (j + 1) false)).tail ++
          entsFrom L xs ans (j + 1 + 1) ++ false :: rest) ∨ (j + 1 = xs.length ∧ G.inp.drop u'.ip = rest)) := by
  intro u'
  have hcK := cap_ge G
  have hin' : G.inp.drop u.ip = false :: false :: ans.getD j false :: (frame (binary L (xs.getD j 0)) ++ (entsFrom L xs ans (j + 1) ++
      false :: rest)) := by rw [hin]; simp [entW]
  obtain ⟨a1, b1, c1, w1⟩ := rd_step u 6 (by decide) false _ hin'
  generalize hu1 : evalS G (.rd 6) u = u1 at a1 b1 c1 w1
  obtain ⟨a2, b2, c2, w2⟩ := rd_step u1 6 (by decide) false _ c1
  generalize hu2 : evalS G (.rd 6) u1 = u2 at a2 b2 c2 w2
  obtain ⟨a3, b3, c3, w3⟩ := rd_step u2 6 (by decide) (ans.getD j false) _ c2
  generalize hu3 : evalS G (.rd 6) u2 = u3 at a3 b3 c3 w3
  have e7 : u3.env 7 = j := by rw [b3 7 (by decide), b2 7 (by decide), b1 7 (by decide), h7]
  have e16 : u3.env 16 = bitsValue (ans.take j) := by rw [b3 16 (by decide), b2 16 (by decide), b1 16 (by decide), h16]
  have hjK : j + 2 ≤ G.K := by omega
  have hpj : 2 ^ (j + 1) ≤ G.cap + 1 := pow_le_cap (by omega)
  have hbt : bitsValue (ans.take (j + 1)) < 2 ^ (j + 1) := by
    have := bv_lt (ans.take (j + 1)); simp at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (min_le_left _ _))
  have hsucc := bitsValue_take_succ ans j (by omega)
  have hbn : (ans.getD j false).toNat ≤ 1 := bool_toNat_le _
  have hp2 : (ans.getD j false).toNat * 2 ^ j ≤ 2 ^ j := by have := Nat.mul_le_mul_right (2 ^ j) hbn; simpa using this
  have hpj' : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have e16v : evalE G u3 (.add (.v 16) (.shl (.v 6) (.v 7))) = bitsValue (ans.take (j + 1)) := by
    have es : evalE G u3 (.shl (.v 6) (.v 7)) = (ans.getD j false).toNat * 2 ^ j := by
      show min (u3.env 6 * 2 ^ u3.env 7) G.cap = _; rw [a3, e7]; exact min_eq_left (by omega)
    rw [eE_add (eE_v 16 |>.trans e16) es (by omega), hsucc]
  set u4 := u3.setv 16 (bitsValue (ans.take (j + 1))) with hu4
  have e7v : evalE G u4 (.add (.v 7) (.k 1)) = j + 1 :=
    eE_add (by simp [u4, evalE, e7]) (eE_k (by omega)) (by omega)
  set u5 := u4.setv 7 (j + 1) with hu5
  have hd5 : G.inp.drop u5.ip = frame (binary L (xs.getD j 0)) ++ (entsFrom L xs ans (j + 1) ++ false :: rest) := c3
  have hfr := rdFrame_spec G u5 (binary L (xs.getD j 0)) _ hd5 (by
      rw [binary_length]; have := pow_le_cap (G := G) (a := L + 2) (by omega); rw [pow_succ, pow_succ] at this
      have : 1 ≤ 2 ^ L := Nat.one_le_two_pow; omega)
    (by rw [binary_length]; exact hLN)
  obtain ⟨-, -, f3, fw⟩ := hfr
  generalize hu6 : evalS G rdFrame u5 = u6 at f3 fw
  have hd6 : G.inp.drop u6.ip = entsFrom L xs ans (j + 1) ++ false :: rest := by
    rw [f3, binary_length, show u5.ip + 2 * L + 1 = u5.ip + (frame (binary L (xs.getD j 0))).length by
      rw [frame_len, binary_length]; omega, ← List.drop_drop, hd5, List.drop_left]
  obtain ⟨l5, lw, lo, lc⟩ := lead_spec u6 L xs ans rest hl (j + 1) (by omega) hd6
  have ht : u' = evalS G (.rd 5) u6 := by
    show evalS G rdEBody u = _
    simp only [rdEBody, evalS_seq]
    rw [hu1, hu2, hu3, evalS_set, evalS_set, e16v, ← hu4, e7v, ← hu5, hu6]
  rw [ht]
  refine ⟨?_, ?_, ?_, l5, lc⟩
  · rw [lo 7 (by decide), fw.env 7 (by decide)]; simp [u5]
  · rw [lo 16 (by decide), fw.env 16 (by decide)]; simp [u5, u4]
  · exact (((w1.trans w2).trans w3).trans ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))).trans
      ((fw.mono (by decide)).trans lw)

/-- **The entry reader** (proof of `thm:short-pcp-ours`): from the first entry, `16 := bitsValue ans`, positioned at `rest`. -/
theorem rdE_spec (t : FS) (L : ℕ) (xs : List ℕ) (ans rest : List Bool) (hl : ans.length = xs.length)
    (hin : G.inp.drop t.ip = entsFrom L xs ans 0 ++ false :: rest)
    (hK : xs.length + 2 ≤ G.K) (hL : L + 2 ≤ G.K) (hN : xs.length + 2 ≤ G.N) (hLN : L + 1 ≤ G.N) :
    let u := evalS G rdE t
    u.env 16 = bitsValue ans ∧ G.inp.drop u.ip = rest ∧ Wr rdEW t u := by
  intro u
  have hcK := cap_ge G
  have h0 : min 0 G.cap = 0 := Nat.zero_min _
  set t1 := (t.setv 7 0).setv 16 0 with ht1
  have w1 : Wr rdEW t t1 := (Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)
  obtain ⟨l5, lw, lo, lc⟩ := lead_spec t1 L xs ans rest hl 0 (by omega) hin
  generalize hu0 : evalS G (.rd 5) t1 = u0 at l5 lw lo lc
  let P : FS → Prop := fun w => ∃ j, j ≤ xs.length ∧ w.env 7 = j ∧ w.env 16 = bitsValue (ans.take j) ∧
    Wr rdEW t w ∧ w.env 5 = (if j < xs.length then 1 else 0) ∧
    ((j < xs.length ∧ G.inp.drop w.ip = (entW L (xs.getD j 0) (ans.getD j false)).tail ++
        entsFrom L xs ans (j + 1) ++ false :: rest) ∨ (j = xs.length ∧ G.inp.drop w.ip = rest))
  have hP0 : P u0 := ⟨0, by omega, by rw [lo 7 (by decide)]; simp [t1], by rw [lo 16 (by decide)]; simp [t1, bitsValue],
    w1.trans lw, l5, lc⟩
  have hw := whl_inv G (c := .v 5) (body := rdEBody) P (fun w => xs.length - w.env 7 + w.env 5) u0 hP0
    (by rw [lo 7 (by decide), l5]; simp [t1]; split_ifs <;> omega) (by
      rintro w ⟨j, hj, w7, w16, ww, w5, wc⟩ hc
      have hjn : j < xs.length := by
        by_contra hn; rw [if_neg hn] at w5; exact hc w5
      rcases wc with ⟨-, wd⟩ | ⟨hjn', -⟩
      · obtain ⟨b7, b16, bw, b5, bc⟩ := rdEBody_spec w L xs ans rest hl j hjn w7 w16 wd hK hL hLN
        refine ⟨⟨j + 1, by omega, b7, b16, ww.trans bw, b5, bc⟩, ?_⟩
        rw [b7, b5, w7, w5, if_pos hjn]; split_ifs <;> omega
      · omega)
  have ht : u = evalS G (.whl (.v 5) rdEBody) u0 := by
    show evalS G rdE t = _
    simp only [rdE, evalS_seq, evalS_set]
    rw [show evalE G t (.k 0) = 0 from h0, show evalE G (t.setv 7 0) (.k 0) = 0 from h0, ← ht1, hu0]
  rw [ht]
  obtain ⟨⟨j, hj, w7, w16, ww, w5, wc⟩, hc⟩ := hw
  have hjn : j = xs.length := by
    by_contra hn; have : j < xs.length := by omega
    rw [if_pos this] at w5; exact absurd (w5 ▸ hc : (1 : ℕ) = 0) (by norm_num)
  rcases wc with ⟨h1, -⟩ | ⟨-, wd⟩
  · omega
  · refine ⟨?_, wd, ww⟩
    rw [w16, hjn, ← hl, List.take_length]

end NearCubicGates.Adapters.ShortPCP.Machines.FL
