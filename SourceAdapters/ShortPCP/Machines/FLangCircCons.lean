import SourceAdapters.ShortPCP.Machines.FLangCirc
import SourceAdapters.ShortPCP.Machines.FLangDeg

/-!
# Single-run time, machine layer 22: the consistency test of Step 4

BCGT13 Construction 8.5 Step 4 (`ShortPCP.consist`): "Verify that `p1(α) = ω`" with
`ω = P_t(α, p0(N_{t,1}(α)), …, p0(N_{t,cN}(α)))`; proof of `thm:short-pcp-ours`: "The consistency test uses `f` bits" (the point `α` is
the first `f` coins as a word, `Request.consistPoint`).

The test is non-adaptive (proof of `thm:short-pcp-ours`): its queries `p1(α)` and `p0(N_{t,i}(α))` depend only on the coins.
* `cqP` (the queries): `36 := α` (the coins in `42`, modulo `2^f`), `37 :=` the packed words of `N_{t,i}(α)`,
  `i < cN`, each by reading its slope and shift and evaluating their field multiply/add (found in `D` from the record's position, slot 6).
* `cdP` (the decision): from `α` (`36`), the packed answers `p0(N_{t,i}(α))` (`37`) and the answer `p1(α)` (`22`),
  `24 := [p1(α) = P_t(α, …)]` by `circP` on the constraint circuit (record slot 7).

`consistPoint_eq`, `nbr_eq`, `consist_eq` relate these to the join's `Request.consistPoint` and
`consist (Request.acsp φ)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells (natWord_one natWord_zero natWord_bit natWord_length lt_natBitLength)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate listWord gateWord)
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)
open NearCubicGates.Adapters.ShortPCP (consist)

variable (G : Glob)

/-! ## The join's quantities -/

section Ref

variable {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F)

theorem cvalF_congr (m : ℕ) (env env' : ℕ → F) (h : ∀ i < m, env i = env' i) (gates : List CodeGate) :
    cvalF φ m env gates = cvalF φ m env' gates := by
  have e : (fun prior g => prior ++ [gvalF φ m env prior g]) = (fun prior g => prior ++ [gvalF φ m env' prior g]) := by
    funext prior g
    cases g with
    | input i =>
      simp only [gvalF]
      by_cases hi : i < m
      · rw [if_pos hi, if_pos hi, h i hi]
      · rw [if_neg hi, if_neg hi]
    | _ => rfl
  unfold cvalF cfoldF; rw [e]

theorem bitsValue_range_mod (c : ℕ → Bool) (x : ℕ) :
    ∀ f, (∀ i < f, x / 2 ^ i % 2 = (c i).toNat) → bitsValue ((List.range f).map c) = x % 2 ^ f
  | 0, _ => by simp [bitsValue, Nat.mod_one]
  | f + 1, h => by
    have ih := bitsValue_range_mod c x f (fun i hi => h i (by omega))
    have hb := h f (by omega)
    rw [List.range_succ, List.map_append, List.map_singleton]
    have hap : ∀ (l : List Bool) (b : Bool), bitsValue (l ++ [b]) = bitsValue l + b.toNat * 2 ^ l.length := by
      intro l b
      induction l with
      | nil => simp [bitsValue]
      | cons a l ih => simp only [List.cons_append, bitsValue, ih, List.length_cons, pow_succ]; ring
    rw [hap, ih, List.length_map, List.length_range, mod_two_pow_succ', Nat.testBit_eq_decide_div_mod_eq, hb]
    cases c f <;> rfl

end Ref

/-- The consistency point is the coin word modulo `2^f` (proof of `thm:short-pcp-ours`). -/
theorem consistPoint_eq {F : Type} [Field F] [DecidableEq F] (q : Request)
    (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (c : ℕ → Bool) (x : ℕ)
    (hx : ∀ i < q.code.f, x / 2 ^ i % 2 = (c i).toNat) :
    q.consistPoint ψ c = ev ψ (x % 2 ^ q.code.f) := by
  unfold Request.consistPoint Request.elt; rw [bitsValue_range_mod c x q.code.f hx]; rfl

/-- The neighbor functions are the encoded affine maps. -/
theorem nbr_eq {F : Type} [Field F] [DecidableEq F] (q : Request) (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (i : Fin q.code.cN) (a : ℕ) :
    (q.acsp ψ).nbr i (ev ψ a) =
      ev ψ (q.code.nbr.getD i.val (0, 0)).1 * ev ψ a + ev ψ (q.code.nbr.getD i.val (0, 0)).2 := rfl

/-- **The consistency test of the join**, from words: `α`, the answers `p0(N_{t,i}(α))` and `p1(α)`. -/
theorem consist_eq {F : Type} [Field F] [DecidableEq F] (q : Request) (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (p0 p1 : F → F) (a z : ℕ) (ys : List ℕ) (hyl : ys.length = q.code.cN)
    (hys : ∀ i : Fin q.code.cN, ev ψ (ys.getD i.val 0) = p0 ((q.acsp ψ).nbr i (ev ψ a)))
    (hz : ev ψ z = p1 (ev ψ a)) :
    consist (q.acsp ψ) p0 p1 (ev ψ a) =
      decide (ev ψ z = cvalF ψ (q.code.cN + 1) (fun j => ev ψ ((a :: ys).getD j 0)) q.code.cons) := by
  unfold consist
  rw [← hz]
  congr 2
  show q.circuitVal ψ (q.code.cN + 1) _ q.code.cons = _
  rw [circuitVal_eq]
  refine cvalF_congr ψ _ _ _ (fun j hj => ?_) _
  rw [dif_pos hj]
  cases j with
  | zero => rfl
  | succ j =>
    have hj' : j < q.code.cN := by omega
    rw [List.getD_cons_succ]
    exact (hys ⟨j, hj'⟩).symm

/-! ## The queries: the point and the neighbors -/

/-- The reduced word of the affine neighbor, with `(0,0)` for an absent pair. -/
noncomputable def nbW (q : Request) (p a i : ℕ) : ℕ :=
  (mulW p q.code.f (q.code.nbr.getD i (0, 0)).1 a ^^^ (q.code.nbr.getD i (0, 0)).2) % 2 ^ q.code.f

theorem nbr_words_lt (q : Request) (hwf : q.code.WellFormed) (i : ℕ) :
    (q.code.nbr.getD i (0, 0)).1 < 2 ^ q.code.f ∧ (q.code.nbr.getD i (0, 0)).2 < 2 ^ q.code.f := by
  rcases Nat.lt_or_ge i q.code.nbr.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact hwf.2.2.2.2.1 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _⟩

theorem nbW_spec {F : Type} [Field F] (q : Request) {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F)
    (hp : GF.ModulusOk p q.code.f) (hwf : q.code.WellFormed) (a i : ℕ) (ha : a < 2 ^ q.code.f) :
    nbW q p a i < 2 ^ q.code.f ∧ ev φ (nbW q p a i) =
      ev φ (q.code.nbr.getD i (0, 0)).1 * ev φ a + ev φ (q.code.nbr.getD i (0, 0)).2 := by
  have hm : mulW p q.code.f (q.code.nbr.getD i (0, 0)).1 a < 2 ^ q.code.f := redW_lt _ _ _
  have hb := (nbr_words_lt q hwf i).2
  unfold nbW
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hm hb), ev_xor, ev_mulW φ _ _ _ hp]
  exact ⟨Nat.xor_lt_two_pow hm hb, rfl⟩

/-- Move the cursor to neighbor pair `20` (record slot 6; loop variable `21`). -/
def seekNbr : S := .seq (.set 14 (recE 6)) (.loop 21 (.v 20) skipPair)

/-- Read the pair and evaluate `slope * alpha + shift`, retaining alpha in `36`. -/
def cqBody : S := .seq seekNbr (.seq readPair (.set 28 (.fadd (.fmul (.v 26) (.v 36)) (.v 27))))

/-- **The queries of the consistency test**: `36 := α`, `37 :=` the packed words of `N_{t,i}(α)`, `i < cN`. -/
def cqP : S :=
  .seq (.set 36 (.md (.v 42) (.shl (.k 1) (.v 23)))) (.seq (.set 25 (recE 5)) (genP 25 20 28 37 23 cqBody))

def cqBodyW : List Var := [5, 6, 8, 9, 14, 21, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
def cqW : List Var := [5, 6, 8, 9, 14, 20, 21, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

theorem PCtx.circ_K {q : Request} {D : ℕ} (c : PCtx G q D) (gates : List CodeGate) (p n : ℕ)
    (hp : p + (listWord gateWord gates).length ≤ q.data.length) (hn : n ≤ q.data.length) :
    q.code.f * (gates.length + n) + 1 ≤ G.K := by
  have h1 := count_le gateWord gates (fun x _ => gateWord_pos x) p _ hp
  have hf := c.f_lt; have hK := c.K
  have h2 := Nat.mul_le_mul (show q.code.f ≤ q.data.length by omega) (show gates.length + n ≤ 2 * q.data.length by omega)
  have h3 : q.data.length * (2 * q.data.length) = 2 * (q.data.length * q.data.length) := by ring
  omega

/-- **The queries of the consistency test.** -/
theorem cqP_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (q : Request)
    (c : PCtx G q (s.env 10)) (h15 : s.env 15 = packW (G.K / 16) (parseRec q)) (h23 : s.env 23 = q.code.f)
    (hfl : s.fl = q.code.f) (hok : fieldOk G s.fl s.fp = true) :
    (evalS G cqP s).env 36 = s.env 42 % 2 ^ q.code.f ∧
      (evalS G cqP s).env 37 = packW q.code.f ((List.range q.code.cN).map (nbW q s.fp (s.env 42 % 2 ^ q.code.f))) ∧
      Wr cqW s (evalS G cqP s) := by
  have hd := c.bd; have hK := c.K32; have hcap := cap_ge G
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  rw [hfl] at hf1 hfK hmod
  have c1 : min 1 G.cap = 1 := by omega
  set a := s.env 42 % 2 ^ q.code.f with ha
  have hal : a < 2 ^ q.code.f := Nat.mod_lt _ (by positivity)
  obtain ⟨a5, e6, l5⟩ := c.piece 4 (listWord Instance.pairWord q.code.nbr)
    (by norm_num) rfl
  rw [listWord_eq] at a5 l5
  obtain ⟨-, a5b⟩ := At.append a5
  simp only [List.length_append] at l5
  have hcN := count_le Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x) (posOf q 4)
    q.data.length (by rw [listWord_eq, List.length_append]; exact l5)
  have hpN : posN q = posOf q 4 + (natWord q.code.nbr.length).length := rfl
  have e36 : evalE G s (.md (.v 42) (.shl (.k 1) (.v 23))) = a := by
    simp only [evalE, h23, c1, one_mul, min_cap_pow (show q.code.f + 1 ≤ G.K by omega)]
    exact ha.symm
  set s1 := (s.setv 36 a).setv 25 q.code.cN with hs1
  have e5 : evalE G (s.setv 36 a) (recE 5) = q.code.cN :=
    recE_parse G (s.setv 36 a) q c (by simpa using h15) 5 (by norm_num)
  have hfK' : q.code.f * q.code.cN ≤ G.K := by
    have := Nat.mul_le_mul (show q.code.f ≤ q.data.length by have := c.f_lt; omega)
      (show q.code.cN ≤ q.data.length by unfold Instance.cN; omega)
    have := c.K; omega
  have hgen := genP_spec G 25 20 28 37 23 cqBody cqBodyW s1 q.code.cN q.code.f (nbW q s.fp a)
    (by simp [s1]; unfold Instance.cN; have := hd.2; omega)
    (by simp (config := { decide := true }) [s1, Function.update_apply, h23]) hfK'
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t tW t20
      have tk : ∀ x : Var, x = 10 ∨ x = 15 ∨ x = 23 ∨ x = 36 → t.env x = s.env x ∨ x = 36 := by
        intro x hx; rcases hx with rfl | rfl | rfl | rfl
        · left; rw [tW.env 10 (by decide)]; simp [s1]
        · left; rw [tW.env 15 (by decide)]; simp [s1]
        · left; rw [tW.env 23 (by decide)]; simp [s1]
        · right; rfl
      have t10 : t.env 10 = s.env 10 := by rw [tW.env 10 (by decide)]; simp [s1]
      have t15 : t.env 15 = s.env 15 := by rw [tW.env 15 (by decide)]; simp [s1]
      have t23 : t.env 23 = q.code.f := by rw [tW.env 23 (by decide)]; simp [s1, h23]
      have t36 : t.env 36 = a := by rw [tW.env 36 (by decide)]; simp [s1]
      have tfl : t.fl = q.code.f := tW.fl.trans hfl
      have tfp : t.fp = s.fp := tW.fp
      have hjN : j < q.code.nbr.length := hj
      -- seek the circuit `j`
      set t1 := t.setv 14 (posN q) with ht1
      have e1 : evalS G (.set 14 (recE 6)) t = t1 := by
        simp only [evalS_set]; rw [recE_parse G t q c (by rw [t15]; exact h15) 6 (by norm_num)]; rfl
      have lp := curLoop_spec G 21 (.v 20) skipPair pNatW Instance.pairWord q.code.nbr t1
        (posN q) q.data.length j (by
          simp only [evalE, t1, FS.setv_env, Function.update_of_ne (show (20 : Var) ≠ 14 by decide), t20]
          have := hd.2; unfold Instance.cN at hj; omega) hj.le
        (by simp only [t1, FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 14 by decide), t10]; exact a5b)
        (by simp [t1]) (by rw [hpN]; omega) (by decide) (by decide) (by decide)
        (fun x _ t' p' ha ht he => skipPair_spec G t' x p' _ ha ht he hd)
      obtain ⟨l14, lW⟩ := lp
      generalize ht2 : evalS G (.loop 21 (.v 20) skipPair) t1 = t2 at l14 lW
      have hA := At.flatten Instance.pairWord q.code.nbr a5b j hjN
      have hle := flatten_take_le Instance.pairWord q.code.nbr (j + 1)
      have hts := flatten_take_succ_length Instance.pairWord q.code.nbr j hjN
      have t2k : ∀ x : Var, x = 10 ∨ x = 23 ∨ x = 36 → t2.env x = t.env x := by
        intro x hx
        have h1 : x ∉ (21 : Var) :: pNatW := by rcases hx with rfl | rfl | rfl <;> decide
        have h2 : x ≠ 14 := by rcases hx with rfl | rfl | rfl <;> decide
        rw [lW.env x h1]; simp [t1, Function.update_of_ne h2]
      have t2fl : t2.fl = q.code.f := by rw [lW.fl]; simp [t1, tfl]
      have t2fp : t2.fp = s.fp := by rw [lW.fp]; simp [t1, tfp]
      obtain ⟨r26, r27, -, rW⟩ := readPair_spec G t2 q.code.nbr[j] _ q.data.length
        (by rw [t2k 10 (by simp), t10, hpN]; exact hA) l14 (by rw [hpN] at *; omega) hd
      generalize ht3 : evalS G readPair t2 = t3 at r26 r27 rW
      have t3fl : t3.fl = q.code.f := rW.fl.trans t2fl
      have t3fp : t3.fp = s.fp := rW.fp.trans t2fp
      have t3_36 : t3.env 36 = a := by rw [rW.env 36 (by decide), t2k 36 (by simp), t36]
      have hp : q.code.nbr[j].1 < 2 ^ q.code.f ∧ q.code.nbr[j].2 < 2 ^ q.code.f :=
        c.wf.2.2.2.2.1 _ (List.getElem_mem hjN)
      have e : evalS G cqBody t = t3.setv 28 (nbW q s.fp a j) := by
        simp only [cqBody, seekNbr, evalS_seq]
        rw [e1, ht2, ht3]
        simp only [evalS_set, evalE, r26, r27, t3_36, t3fl, t3fp,
          Nat.mod_eq_of_lt hp.1, Nat.mod_eq_of_lt hal, nbW, List.getD_eq_getElem _ _ hjN]
      rw [e]
      refine ⟨by simp, (nbW_spec q φ hmod c.wf a j hal).1, ?_⟩
      exact (((Wr.setv _ (by decide) _).trans (lW.mono (by decide))).trans
        (rW.mono (by decide))).trans (Wr.setv _ (by decide) _))

  obtain ⟨g37, gW⟩ := hgen
  have e : evalS G cqP s = evalS G (genP 25 20 28 37 23 cqBody) s1 := by
    simp only [cqP, evalS_seq, evalS_set, e36]; rw [e5]
  rw [e]
  refine ⟨?_, g37, ?_⟩
  · rw [gW.env 36 (by decide)]; simp [s1]
  · exact ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (gW.mono (by decide))

/-! ## The decision -/

/-- **The decision of the consistency test**: `24 := [p1(α) = P_t(α, p0(N_{t,1}(α)), …)]` from `α` (`36`), the
packed answers `p0(N_{t,i}(α))` (`37`) and the answer `p1(α)` (`22`); the constraint circuit is found from record
slot 7. -/
def cdP : S :=
  .seq (.set 26 (.add (.v 36) (.shl (.v 37) (.v 23)))) (.seq (.set 27 (.add (recE 5) (.k 1)))
    (.seq (.set 14 (recE 7)) (.seq circP (.set 24 (.eq (.v 28) (.v 22))))))

def cdW : List Var := [5, 6, 8, 9, 14, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]

/-- **The decision of the consistency test.** -/
theorem cdP_spec {F : Type} [Field F] [DecidableEq F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (q : Request)
    (c : PCtx G q (s.env 10)) (h15 : s.env 15 = packW (G.K / 16) (parseRec q)) (h23 : s.env 23 = q.code.f)
    (hfl : s.fl = q.code.f) (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp))
    (ys : List ℕ) (hys : ∀ a ∈ ys, a < 2 ^ q.code.f) (hyl : ys.length = q.code.cN)
    (h37 : s.env 37 = packW q.code.f ys) (h36 : s.env 36 < 2 ^ q.code.f) (h22 : s.env 22 < 2 ^ q.code.f) :
    (evalS G cdP s).env 24 = (if ev φ (s.env 22) = cvalF φ (q.code.cN + 1)
        (fun j => ev φ ((s.env 36 :: ys).getD j 0)) q.code.cons then 1 else 0) ∧
      Wr cdW s (evalS G cdP s) := by
  have hd := c.bd; have hK := c.K32; have hcap := cap_ge G
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  rw [hfl] at hf1 hfK hmod
  have c1 : min 1 G.cap = 1 := by omega
  obtain ⟨a6, -, l6⟩ := c.piece 5 (listWord gateWord q.code.cons) (by norm_num) rfl
  have hcN : q.code.cN + 1 ≤ q.data.length := by
    obtain ⟨-, -, l5⟩ := c.piece 4 (listWord Instance.pairWord q.code.nbr)
      (by norm_num) rfl
    have := count_le Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x) _ _ l5
    unfold Instance.cN; omega
  have hKc := c.circ_K G q.code.cons (posOf q 5) (q.code.cN + 1) l6 hcN
  -- the inputs `α :: ys`
  have hins : ∀ x ∈ s.env 36 :: ys, x < 2 ^ q.code.f := by
    intro x hx; simp at hx; rcases hx with rfl | hx; exacts [h36, hys x hx]
  have hpl := packW_lt q.code.f (s.env 36 :: ys) hins
  simp only [List.length_cons, hyl, packW] at hpl
  have hpk : 2 ^ (q.code.f * (q.code.cN + 1)) ≤ G.cap + 1 := pow_le_cap (by
    have := Nat.mul_le_mul_left q.code.f (Nat.le_add_left (q.code.cN + 1) q.code.cons.length)
    rw [mul_add] at hKc this; omega)
  have e26 : evalE G s (.add (.v 36) (.shl (.v 37) (.v 23))) = packW q.code.f (s.env 36 :: ys) := by
    have h1 : min (packW q.code.f ys * 2 ^ q.code.f) G.cap = packW q.code.f ys * 2 ^ q.code.f := by
      rw [mul_comm]; omega
    have h2 : min (s.env 36 + 2 ^ q.code.f * packW q.code.f ys) G.cap = s.env 36 + 2 ^ q.code.f * packW q.code.f ys :=
      by omega
    simp only [evalE, h37, h23, h1, packW]; rw [mul_comm (packW _ _), h2]
  set s1 := s.setv 26 (packW q.code.f (s.env 36 :: ys)) with hs1
  have e27 : evalE G s1 (.add (recE 5) (.k 1)) = q.code.cN + 1 := by
    simp only [evalE]; rw [recE_parse G s1 q c (by simpa [s1] using h15) 5 (by norm_num), c1]
    show min (q.code.cN + 1) G.cap = _; have := hd.1; omega
  set s2 := s1.setv 27 (q.code.cN + 1) with hs2
  have e14 : evalE G s2 (recE 7) = posC q := recE_parse G s2 q c (by simpa [s2, s1] using h15) 7 (by norm_num)
  set s3 := s2.setv 14 (posC q) with hs3
  have s3fl : s3.fl = q.code.f := by simp [s3, s2, s1, hfl]
  obtain ⟨l28, v28, -, cW⟩ := circP_spec G s3 φ q.code.cons (s.env 36 :: ys) (q.code.cN + 1) (posOf q 5) q.data.length
    (by simpa [s3, s2, s1] using a6) (by simp [s3]; rfl) l6 hd (by simp [s3, s2, s1, s3fl, hfl])
    (by simp (config := { decide := true }) [s3, s2, s1, Function.update_apply])
    (by rw [s3fl]; exact hins) (by simp (config := { decide := true }) [s3, s2, s1, Function.update_apply, h23, hfl])
    (by simpa [s3, s2, s1] using hok) (by rw [s3fl]; exact c.wf.2.2.2.2.2.1)
    (by rw [s3fl]; simpa [hyl] using hKc)
  generalize hs4 : evalS G circP s3 = s4 at l28 v28 cW
  have s4_22 : s4.env 22 = s.env 22 := by rw [cW.env 22 (by decide)]; simp [s3, s2, s1]
  have e : evalS G cdP s = s4.setv 24 (if s4.env 28 = s4.env 22 then 1 else 0) := by
    simp only [cdP, evalS_seq, evalS_set, e26]
    rw [← hs1, e27, ← hs2, e14, ← hs3, hs4]; rfl
  rw [e]
  refine ⟨?_, ((((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
    (cW.mono (by decide))).trans (Wr.setv _ (by decide) _)⟩
  simp only [FS.setv_env, Function.update_self, s4_22]
  have v28' : ev φ (s4.env 28) = cvalF φ (q.code.cN + 1) (fun j => ev φ ((s.env 36 :: ys).getD j 0)) q.code.cons :=
    v28
  rw [s3fl] at l28
  by_cases h : s4.env 28 = s.env 22
  · have h' : ev φ (s.env 22) = cvalF φ (q.code.cN + 1) (fun j => ev φ ((s.env 36 :: ys).getD j 0)) q.code.cons := by
      rw [← h, v28']
    rw [if_pos h, if_pos h']
  · rw [if_neg h, if_neg]
    intro h'
    exact h (ev_inj φ q.code.f _ _ hmod hirr l28 h22 (by rw [v28', h']))

/-- Neighbor evaluation reads the packed data word without advancing physical input. -/
theorem cqP_ip (s : FS) : (evalS G cqP s).ip = s.ip :=
  ip_rdFree G cqP s (by decide)

/-- Constraint evaluation reads the packed data word without advancing physical input. -/
theorem cdP_ip (s : FS) : (evalS G cdP s).ip = s.ip :=
  ip_rdFree G cdP s (by decide)

end NearCubicGates.Adapters.ShortPCP.Machines.FL
