import SourceAdapters.ShortPCP.Machines.FLangParseMain

/-!
# Single-run time, machine layer 21: the arithmetic circuits of the instance

The constraint polynomial of the affine instance is given by a straight-line arithmetic circuit, serialized as
`listWord gateWord`. Its total semantics evaluates missing inputs and missing prior-gate references to zero;
`Request.circuitVal` returns the last value, or zero for the empty circuit.
`circP` reads the circuit at the cursor (variable `14`) gate by gate from `D` and keeps the values of all gates so far
in one packed list (`29`); the inputs are the packed list in `26` (`m` of them, `27`); the value of the last gate is
left in `28` (`circP_spec`). Constants must be reduced words (`< 2^f`, the join's J7).
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

variable (G : Glob)

/-! ## The circuit value on field elements and on words -/

section Ref

variable {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F)

/-- One gate (`Request.gateVal` with the constant words read by `ev φ`). -/
noncomputable def gvalF (m : ℕ) (env : ℕ → F) (prior : List F) : CodeGate → F
  | .input i => if i < m then env i else 0
  | .const v => ev φ v
  | .add a b => prior.getD a 0 + prior.getD b 0
  | .mul a b => prior.getD a 0 * prior.getD b 0

/-- The values of all gates. -/
noncomputable def cfoldF (m : ℕ) (env : ℕ → F) (gates : List CodeGate) : List F :=
  gates.foldl (fun prior g => prior ++ [gvalF φ m env prior g]) []

/-- The value of a circuit (`Request.circuitVal`). -/
noncomputable def cvalF (m : ℕ) (env : ℕ → F) (gates : List CodeGate) : F := (cfoldF φ m env gates).getLastD 0

/-- The join's circuit value is `cvalF`. -/
theorem circuitVal_eq (q : Request) (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (m : ℕ) (env : ℕ → F)
    (gates : List CodeGate) : q.circuitVal ψ m env gates = cvalF ψ m env gates := by
  unfold Request.circuitVal cvalF cfoldF
  congr 2

end Ref

/-- One gate on words: the machine's computation (inputs from the packed list `ins`). -/
noncomputable def gW (p f m : ℕ) (ins : List ℕ) (prior : List ℕ) : CodeGate → ℕ
  | .input i => (if i < m then 1 else 0) * ins.getD i 0
  | .const v => v
  | .add a b => (prior.getD a 0 ^^^ prior.getD b 0) % 2 ^ f
  | .mul a b => mulW p f (prior.getD a 0 % 2 ^ f) (prior.getD b 0 % 2 ^ f)

noncomputable def wfold (p f m : ℕ) (ins : List ℕ) (gates : List CodeGate) : List ℕ :=
  gates.foldl (fun prior g => prior ++ [gW p f m ins prior g]) []

theorem getD_lt_pow {w : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (j : ℕ) : l.getD j 0 < 2 ^ w := by
  rcases Nat.lt_or_ge j l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; positivity

theorem getD_map_ev {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (l : List ℕ) (j : ℕ) :
    (l.map (ev φ)).getD j 0 = ev φ (l.getD j 0) := by
  rcases Nat.lt_or_ge j l.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h, ev_zero]

/-- **The word fold computes the field fold** (from any matching start). -/
theorem wfold_aux {F : Type} [Field F] {p f : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (hp : GF.ModulusOk p f)
    (m : ℕ) (ins : List ℕ) (hins : ∀ a ∈ ins, a < 2 ^ f) :
    ∀ (gates : List CodeGate), (∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ f) →
    ∀ (pw : List ℕ) (pf : List F), (∀ a ∈ pw, a < 2 ^ f) → pw.map (ev φ) = pf →
      let r := gates.foldl (fun prior g => prior ++ [gW p f m ins prior g]) pw
      (∀ a ∈ r, a < 2 ^ f) ∧ r.length = pw.length + gates.length ∧
        r.map (ev φ) = gates.foldl (fun prior g => prior ++ [gvalF φ m (fun i => ev φ (ins.getD i 0)) prior g]) pf
  | [], _, pw, pf, hpw, h => ⟨hpw, by simp, h⟩
  | g :: gs, hc, pw, pf, hpw, h => by
    have hg : gW p f m ins pw g < 2 ^ f ∧
        ev φ (gW p f m ins pw g) = gvalF φ m (fun i => ev φ (ins.getD i 0)) pf g := by
      have ga := fun a => getD_lt_pow pw hpw a
      cases g with
      | input i =>
        simp only [gW, gvalF]
        split_ifs with hi
        · exact ⟨by rw [one_mul]; exact getD_lt_pow ins hins i, by rw [one_mul]⟩
        · exact ⟨by rw [zero_mul]; positivity, by rw [zero_mul, ev_zero]⟩
      | const v => exact ⟨hc _ (by simp) v rfl, rfl⟩
      | add a b =>
        simp only [gW, gvalF]
        rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (ga a) (ga b)), ← h, getD_map_ev, getD_map_ev, ev_xor]
        exact ⟨Nat.xor_lt_two_pow (ga a) (ga b), rfl⟩
      | mul a b =>
        simp only [gW, gvalF]
        refine ⟨redW_lt _ _ _, ?_⟩
        rw [ev_mulW φ f _ _ hp, Nat.mod_eq_of_lt (ga a), Nat.mod_eq_of_lt (ga b), ← h, getD_map_ev, getD_map_ev]
    have ih := wfold_aux φ hp m ins hins gs (fun g' hg' => hc g' (by simp [hg'])) (pw ++ [gW p f m ins pw g])
      (pf ++ [gvalF φ m (fun i => ev φ (ins.getD i 0)) pf g])
      (by intro a ha; simp at ha; rcases ha with ha | rfl; exacts [hpw a ha, hg.1])
      (by rw [List.map_append, h]; simp [hg.2])
    simp only [List.foldl_cons]
    refine ⟨ih.1, by rw [ih.2.1]; simp; ring, ih.2.2⟩

theorem wfold_take_succ (p f m : ℕ) (ins : List ℕ) (gates : List CodeGate) (j : ℕ) (hj : j < gates.length) :
    wfold p f m ins (gates.take (j + 1)) =
      wfold p f m ins (gates.take j) ++ [gW p f m ins (wfold p f m ins (gates.take j)) gates[j]] := by
  unfold wfold
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

theorem getLastD_eq_getD (l : List ℕ) : l.getLastD 0 = l.getD (l.length - 1) 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-! ## Packed words at any index -/

/-- `getW` at any index (beyond the list: `0`). -/
theorem getW_any (s : FS) (V : Var) (i : E) (w j : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w)
    (hV : s.env V = packW w l) (h23 : s.env 23 = w) (hi : evalE G s i = j) (hlK : w * l.length ≤ G.K)
    (hw : w + 1 ≤ G.K) : evalE G s (getW V i) = l.getD j 0 := by
  rcases Nat.lt_or_ge G.K (j * w) with hj | hj
  · have hc := cap_ge G
    have hjl : l.length ≤ j := by
      by_contra h
      have : j * w ≤ l.length * w := Nat.mul_le_mul_right _ (by omega)
      rw [mul_comm] at hlK; omega
    have h1 : min 1 G.cap = 1 := by omega
    have h2 : min (1 * 2 ^ w) G.cap = 2 ^ w := by rw [one_mul]; exact min_cap_pow hw
    have hlt := packW_lt w l hl
    have hq : packW w l / 2 ^ min (j * w) G.cap = 0 := by
      apply Nat.div_eq_of_lt
      exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp only [getW, evalE, hV, h23, hi, h1, h2, hq, Nat.zero_mod]
    rw [List.getD_eq_default _ _ hjl]
  · exact getW_eval G s V i w j l hl hV h23 hi hj hw

/-! ## The routine -/

/-- Read one gate: `31 := tag`, `32 := x`, `33 := y`. -/
def rdGate : S := .seq pNat (.seq (.set 31 (.v 5)) (.seq pNat (.seq (.set 32 (.v 5)) (.seq pNat (.set 33 (.v 5))))))

/-- The value of the gate just read, into `34`. -/
def gateS : S :=
  .ite (.eq (.v 31) (.k 0)) (.set 34 (.mul (.lt (.v 32) (.v 27)) (getW 26 (.v 32))))
    (.ite (.eq (.v 31) (.k 1)) (.set 34 (.v 32))
      (.ite (.eq (.v 31) (.k 2)) (.set 34 (.fadd (getW 29 (.v 32)) (getW 29 (.v 33))))
        (.set 34 (.fmul (getW 29 (.v 32)) (getW 29 (.v 33))))))

/-- **The circuit evaluator**: `28 :=` the value of the circuit `listWord gateWord gates` at the cursor, inputs in
`26` (`m` in `27`); gate values in `29`, loop variable `30`, count `35`. -/
def circP : S :=
  .seq pNat (.seq (.set 35 (.v 5)) (.seq (.set 29 (.k 0))
    (.seq (.loop 30 (.v 35) (.seq rdGate (.seq gateS (.set 29 (.add (.v 29) (.shl (.v 34) (.mul (.v 30) (.v 23))))))))
      (.set 28 (getW 29 (.sub (.v 35) (.k 1)))))))

/-- The variables `circP` writes. -/
def circW : List Var := [5, 6, 8, 9, 14, 28, 29, 30, 31, 32, 33, 34, 35]

theorem rdGate_spec (s : FS) (g : CodeGate) (p Bd : ℕ) (hat : At (s.env 10) p (gateWord g))
    (hp : s.env 14 = p) (hend : p + (gateWord g).length ≤ Bd) (hB : BdOk G Bd) :
    (evalS G rdGate s).env 31 = gTag g ∧ (evalS G rdGate s).env 32 = gX g ∧ (evalS G rdGate s).env 33 = gY g ∧
      (evalS G rdGate s).env 14 = p + (gateWord g).length ∧
      Wr [5, 6, 8, 9, 14, 31, 32, 33] s (evalS G rdGate s) := by
  rw [gateWord_eq] at hat hend ⊢
  obtain ⟨a12, a3⟩ := At.append hat
  obtain ⟨a1, a2⟩ := At.append a12
  simp only [List.length_append] at hend a3 ⊢
  rw [← add_assoc] at a3
  obtain ⟨n5, n14, nW⟩ := pNat_at G s _ p Bd a1 hp (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at n5 n14 nW
  set s2 := s1.setv 31 (s1.env 5) with hs2
  obtain ⟨m5, m14, mW⟩ := pNat_at G s2 (gX g) _ Bd (by simp [s2]; rw [nW.env 10 (by decide)]; exact a2)
    (by simp [s2, n14]) (by omega) hB
  generalize hs3 : evalS G pNat s2 = s3 at m5 m14 mW
  set s4 := s3.setv 32 (s3.env 5) with hs4
  obtain ⟨k5, k14, kW⟩ := pNat_at G s4 (gY g) _ Bd
    (by simp [s4]; rw [mW.env 10 (by decide)]; simp [s2]; rw [nW.env 10 (by decide)]; exact a3)
    (by simp [s4, m14]) (by omega) hB
  generalize hs5 : evalS G pNat s4 = s5 at k5 k14 kW
  have e : evalS G rdGate s = s5.setv 33 (s5.env 5) := by
    simp only [rdGate, evalS_seq, evalS_set, evalE]
    rw [hs1, show s1.setv 31 (s1.env 5) = s2 from rfl, hs3, show s3.setv 32 (s3.env 5) = s4 from rfl, hs5]
  rw [e]
  refine ⟨?_, ?_, by simp [k5], ?_, ?_⟩
  · simp only [FS.setv_env, Function.update_of_ne (show (31 : Var) ≠ 33 by decide)]
    rw [kW.env 31 (by decide)]; simp only [s4, FS.setv_env, Function.update_of_ne (show (31 : Var) ≠ 32 by decide)]
    rw [mW.env 31 (by decide)]; simp [s2, n5]
  · simp only [FS.setv_env, Function.update_of_ne (show (32 : Var) ≠ 33 by decide)]
    rw [kW.env 32 (by decide)]; simp [s4, m5]
  · simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 33 by decide), k14]; ring
  · exact ((((((nW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (mW.mono (by decide))).trans
      (Wr.setv _ (by decide) _)).trans (kW.mono (by decide))).trans (Wr.setv _ (by decide) _))

theorem gTag_lt (g : CodeGate) : gTag g < 4 := by cases g <;> simp [gTag]

/-- **One gate value.** -/
theorem gateS_spec (t : FS) (g : CodeGate) (ins prior : List ℕ) (m : ℕ) (h31 : t.env 31 = gTag g)
    (h32 : t.env 32 = gX g) (h33 : t.env 33 = gY g) (h26 : t.env 26 = packW t.fl ins) (h27 : t.env 27 = m)
    (h29 : t.env 29 = packW t.fl prior) (h23 : t.env 23 = t.fl) (hok : fieldOk G t.fl t.fp = true)
    (hins : ∀ a ∈ ins, a < 2 ^ t.fl) (hpr : ∀ a ∈ prior, a < 2 ^ t.fl) (hiK : t.fl * ins.length ≤ G.K)
    (hpK : t.fl * prior.length ≤ G.K) (hc : ∀ v, g = .const v → v < 2 ^ t.fl) :
    evalS G gateS t = t.setv 34 (gW t.fp t.fl m ins prior g) := by
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hcap := cap_ge G
  have c0 : min 0 G.cap = 0 := by omega
  have c1 : min 1 G.cap = 1 := by omega
  have c2 : min 2 G.cap = 2 := by omega
  have hpf : 2 ^ t.fl ≤ G.cap := by
    have := pow_le_cap (G := G) (a := t.fl + 1) (by omega); rw [pow_succ] at this
    have := Nat.one_le_two_pow (n := t.fl); omega
  have gw := fun (i : E) (j : ℕ) (hi : evalE G t i = j) =>
    getW_any G t 29 i t.fl j prior hpr h29 h23 hi hpK (by omega)
  have gi := fun (i : E) (j : ℕ) (hi : evalE G t i = j) =>
    getW_any G t 26 i t.fl j ins hins h26 h23 hi hiK (by omega)
  cases g with
  | input i =>
    have hv := getD_lt_pow ins hins i
    have hlt : (if i < m then 1 else 0) * ins.getD i 0 ≤ G.cap := by split_ifs <;> omega
    simp only [gateS, evalS_ite, evalE, h31, gTag, c0, if_true, one_ne_zero, if_false, evalS_set]
    rw [gi (.v 32) i (by simp [evalE, h32, gX])]
    simp only [h32, h27, gX, gW, min_eq_left hlt]
  | const v =>
    simp only [gateS, evalS_ite, evalE, h31, gTag, c0, c1, if_true, if_false, one_ne_zero, evalS_set,
      show (1 : ℕ) ≠ 0 by decide, h32, gX, gW]
  | add a b =>
    simp only [gateS, evalS_ite, evalE, h31, gTag, c0, c1, c2, if_true, if_false, evalS_set,
      show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, one_ne_zero]
    rw [gw (.v 32) a (by simp [evalE, h32, gX]), gw (.v 33) b (by simp [evalE, h33, gY])]
    rfl
  | mul a b =>
    have c3 : min 3 G.cap = 3 := by omega
    simp only [gateS, evalS_ite, evalE, h31, gTag, c0, c1, c2, if_true, if_false, evalS_set,
      show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, one_ne_zero]
    rw [gw (.v 32) a (by simp [evalE, h32, gX]), gw (.v 33) b (by simp [evalE, h33, gY])]
    rfl

/-- The word fold: reduced words, one per gate, matching the field fold. -/
theorem wfold_spec {F : Type} [Field F] {p f : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (hp : GF.ModulusOk p f)
    (m : ℕ) (ins : List ℕ) (hins : ∀ a ∈ ins, a < 2 ^ f) (gates : List CodeGate)
    (hc : ∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ f) :
    (∀ a ∈ wfold p f m ins gates, a < 2 ^ f) ∧ (wfold p f m ins gates).length = gates.length ∧
      (wfold p f m ins gates).map (ev φ) = cfoldF φ m (fun i => ev φ (ins.getD i 0)) gates := by
  have h := wfold_aux φ hp m ins hins gates hc [] [] (by simp) rfl
  unfold wfold
  exact ⟨h.1, by rw [h.2.1]; simp, h.2.2⟩

/-- The word fold without a field: reduced words, one per gate. -/
theorem wfold_aux_w (p f m : ℕ) (ins : List ℕ) (hins : ∀ a ∈ ins, a < 2 ^ f) :
    ∀ (gates : List CodeGate), (∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ f) →
    ∀ (pw : List ℕ), (∀ a ∈ pw, a < 2 ^ f) →
      (∀ a ∈ gates.foldl (fun prior g => prior ++ [gW p f m ins prior g]) pw, a < 2 ^ f) ∧
        (gates.foldl (fun prior g => prior ++ [gW p f m ins prior g]) pw).length = pw.length + gates.length
  | [], _, pw, hpw => ⟨hpw, by simp⟩
  | g :: gs, hc, pw, hpw => by
    have hg : gW p f m ins pw g < 2 ^ f := by
      have ga := fun a => getD_lt_pow pw hpw a
      cases g with
      | input i =>
        have := getD_lt_pow ins hins i
        simp only [gW]; split_ifs
        · rw [one_mul]; exact this
        · rw [zero_mul]; positivity
      | const v => exact hc _ (by simp) v rfl
      | add a b => exact Nat.mod_lt _ (by positivity)
      | mul a b => exact redW_lt _ _ _
    have ih := wfold_aux_w p f m ins hins gs (fun g' hg' => hc g' (by simp [hg'])) (pw ++ [gW p f m ins pw g])
      (by intro a ha; simp at ha; rcases ha with ha | rfl; exacts [hpw a ha, hg])
    simp only [List.foldl_cons]
    exact ⟨ih.1, by rw [ih.2]; simp; ring⟩

theorem wfold_w (p f m : ℕ) (ins : List ℕ) (hins : ∀ a ∈ ins, a < 2 ^ f) (gates : List CodeGate)
    (hc : ∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ f) :
    (∀ a ∈ wfold p f m ins gates, a < 2 ^ f) ∧ (wfold p f m ins gates).length = gates.length := by
  have h := wfold_aux_w p f m ins hins gates hc [] (by simp)
  unfold wfold
  exact ⟨h.1, by rw [h.2]; simp⟩

/-- **The circuit evaluator, on words.** -/
theorem circP_word (s : FS) (gates : List CodeGate)
    (ins : List ℕ) (m p Bd : ℕ)
    (hat : At (s.env 10) p (listWord gateWord gates)) (h14 : s.env 14 = p)
    (hend : p + (listWord gateWord gates).length ≤ Bd) (hB : BdOk G Bd)
    (h26 : s.env 26 = packW s.fl ins) (h27 : s.env 27 = m) (hins : ∀ a ∈ ins, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (hok : fieldOk G s.fl s.fp = true)
    (hconst : ∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ s.fl)
    (hK : s.fl * (gates.length + ins.length) + 1 ≤ G.K) :
    (evalS G circP s).env 28 = (wfold s.fp s.fl m ins gates).getLastD 0 ∧ (evalS G circP s).env 28 < 2 ^ s.fl ∧
      (evalS G circP s).env 14 = p + (listWord gateWord gates).length ∧
      Wr circW s (evalS G circP s) := by
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hcap := cap_ge G
  have c0 : min 0 G.cap = 0 := by omega
  have c1 : min 1 G.cap = 1 := by omega
  rw [listWord_eq] at hat hend ⊢
  obtain ⟨a1, a2⟩ := At.append hat
  simp only [List.length_append] at hend ⊢
  have hlen := length_le_flatten gateWord gates (fun x _ => gateWord_pos x)
  obtain ⟨n5, n14, nW⟩ := pNat_at G s gates.length p Bd a1 h14 (by omega) hB
  generalize hs1 : evalS G pNat s = s1 at n5 n14 nW
  set p1 := p + (natWord gates.length).length with hp1
  set s2 := (s1.setv 35 (s1.env 5)).setv 29 (min 0 G.cap) with hs2
  have hfl : s1.fl = s.fl := nW.fl
  have hfp : s1.fp = s.fp := nW.fp
  have hwf := fun j => wfold_w s.fp s.fl m ins hins (gates.take j)
    (fun g hg => hconst g (List.mem_of_mem_take hg))
  have hmin : min (evalE G s2 (.v 35)) G.N = gates.length := by
    simp (config := { decide := true }) only [s2, evalE, FS.setv_env, Function.update_apply, if_true, if_false, n5]
    have := hB.2; omega
  have hgK : s.fl * gates.length ≤ G.K := by
    have := Nat.mul_le_mul_left s.fl (Nat.le_add_right gates.length ins.length); omega
  have hiK : s.fl * ins.length ≤ G.K := by
    have := Nat.mul_le_mul_left s.fl (Nat.le_add_left ins.length gates.length); omega
  have hpk : 2 ^ (s.fl * gates.length) ≤ G.cap + 1 := pow_le_cap hgK
  have hl := loop_inv G (i := 30) (n := .v 35) (s := s2)
    (body := .seq rdGate (.seq gateS (.set 29 (.add (.v 29) (.shl (.v 34) (.mul (.v 30) (.v 23)))))))
    (fun j t => t.env 14 = p1 + ((gates.take j).map gateWord).flatten.length ∧
      t.env 29 = packW s.fl (wfold s.fp s.fl m ins (gates.take j)) ∧ t.env 35 = gates.length ∧ Wr circW s t) ⟨by
        simp (config := { decide := true }) only [s2, FS.setv_env, Function.update_apply, if_false, n14]; simp,
      by simp [s2, c0, packW, wfold], by simp (config := { decide := true }) [s2, Function.update_apply, n5],
      (nW.mono (by decide)).trans ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))⟩ (by
      rw [hmin]
      rintro j hj t ⟨t14, t29, t35, tW⟩
      have t10 : (t.setv 30 j).env 10 = s.env 10 := by simp; exact tW.env 10 (by decide)
      have hA := At.flatten gateWord gates a2 j hj
      have hle := flatten_take_le gateWord gates (j + 1)
      have hts := flatten_take_succ_length gateWord gates j hj
      obtain ⟨g31, g32, g33, g14, gWr⟩ := rdGate_spec G (t.setv 30 j) gates[j] _ Bd (by rw [t10]; exact hA)
        (by simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 30 by decide)]; exact t14)
        (by omega) hB
      generalize hs3 : evalS G rdGate (t.setv 30 j) = s3 at g31 g32 g33 g14 gWr
      have s3fl : s3.fl = s.fl := gWr.fl.trans tW.fl
      have s3fp : s3.fp = s.fp := gWr.fp.trans tW.fp
      have s3k : ∀ x : Var, x = 23 ∨ x = 26 ∨ x = 27 ∨ x = 29 ∨ x = 35 → s3.env x = t.env x := by
        intro x hx
        have h1 : x ∉ [5, 6, 8, 9, 14, 31, 32, 33] := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
        have h2 : x ≠ 30 := by rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
        rw [gWr.env x h1]; simp [Function.update_of_ne h2]
      have hk := fun x (hx : x = 23 ∨ x = 26 ∨ x = 27) => (s3k x (by tauto)).trans (tW.env x (by
        rcases hx with rfl | rfl | rfl <;> decide))
      obtain ⟨wlt, wlen⟩ := hwf j
      rw [List.length_take, min_eq_left hj.le] at wlen
      have hgs := gateS_spec G s3 gates[j] ins (wfold s.fp s.fl m ins (gates.take j)) m g31 g32 g33
        (by rw [hk 26 (by simp), h26, s3fl]) (by rw [hk 27 (by simp), h27])
        (by rw [s3k 29 (by simp), t29, s3fl]) (by rw [hk 23 (by simp), h23, s3fl])
        (by rw [s3fl, s3fp]; exact hok) (by rw [s3fl]; exact hins) (by rw [s3fl]; exact wlt)
        (by rw [s3fl]; exact hiK) (by rw [s3fl, wlen]; exact le_trans (Nat.mul_le_mul_left _ hj.le) hgK)
        (by rw [s3fl]; exact hconst _ (List.getElem_mem hj))
      rw [s3fp, s3fl] at hgs
      obtain ⟨wlt', -⟩ := hwf (j + 1)
      rw [wfold_take_succ _ _ _ _ _ j hj] at wlt'
      have hgv : gW s.fp s.fl m ins (wfold s.fp s.fl m ins (gates.take j)) gates[j] < 2 ^ s.fl := wlt' _ (by simp)
      have hpj := packW_lt s.fl _ wlt'
      rw [List.length_append, wlen, List.length_singleton, packW_append, wlen] at hpj
      have hjw : j * s.fl ≤ G.K := by rw [mul_comm]; exact le_trans (Nat.mul_le_mul_left _ hj.le) hgK
      have hpw : 2 ^ (s.fl * (j + 1)) ≤ 2 ^ (s.fl * gates.length) := Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ hj)
      set gv := gW s.fp s.fl m ins (wfold s.fp s.fl m ins (gates.take j)) gates[j] with hgvd
      set pv := packW s.fl (wfold s.fp s.fl m ins (gates.take j)) with hpvd
      have hpacks : packW s.fl [gv] = gv := by simp [packW]
      rw [hpacks] at hpj
      have hsum : pv + 2 ^ (s.fl * j) * gv < G.cap + 1 := lt_of_lt_of_le hpj (hpw.trans hpk)
      have e1 : min (j * s.fl) G.cap = s.fl * j := by rw [min_cap hjw, mul_comm]
      have e2 : min (gv * 2 ^ (s.fl * j)) G.cap = gv * 2 ^ (s.fl * j) := by
        rw [mul_comm gv]; omega
      have e3 : min (pv + gv * 2 ^ (s.fl * j)) G.cap = pv + gv * 2 ^ (s.fl * j) := by
        rw [mul_comm gv]; omega
      simp only [evalS_seq, evalS_set, hs3, hgs]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 29 by decide),
          Function.update_of_ne (show (14 : Var) ≠ 34 by decide), g14, hts]; ring
      · simp only [FS.setv_env, Function.update_self, evalE, Function.update_of_ne (show (29 : Var) ≠ 34 by decide),
          s3k 29 (by simp), t29, Function.update_self, Function.update_of_ne (show (30 : Var) ≠ 34 by decide),
          Function.update_of_ne (show (23 : Var) ≠ 34 by decide), hk 23 (by simp), h23]
        rw [gWr.env 30 (by decide)]
        simp only [FS.setv_env, Function.update_self, e1, e2, e3]
        rw [wfold_take_succ _ _ _ _ _ j hj, packW_append, wlen, hpacks]; ring
      · simp only [FS.setv_env, Function.update_of_ne (show (35 : Var) ≠ 29 by decide),
          Function.update_of_ne (show (35 : Var) ≠ 34 by decide), s3k 35 (by simp), t35]
      · exact (((tW.trans (Wr.setv _ (by decide) _)).trans (gWr.mono (by decide))).trans
          (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _))
  rw [hmin] at hl; simp only [List.take_length] at hl
  obtain ⟨f14, f29, f35, fW⟩ := hl
  generalize hs4 : evalS G (.loop 30 (.v 35) (.seq rdGate (.seq gateS (.set 29 (.add (.v 29)
    (.shl (.v 34) (.mul (.v 30) (.v 23)))))))) s2 = s4 at f14 f29 f35 fW
  obtain ⟨wlt, wlen⟩ := wfold_w s.fp s.fl m ins hins gates hconst
  have s4_23 : s4.env 23 = s.fl := by rw [fW.env 23 (by decide), h23]
  have hget := getW_any G s4 29 (.sub (.v 35) (.k 1)) s.fl (gates.length - 1) _ wlt (by rw [f29]) s4_23
    (by simp only [evalE, f35, c1]) (by rw [wlen]; exact hgK) (by omega)
  have e : evalS G circP s = s4.setv 28 (evalE G s4 (getW 29 (.sub (.v 35) (.k 1)))) := by
    simp only [circP, evalS_seq, evalS_set, evalE]
    rw [hs1]
    rw [← hs4]
  rw [e, hget]
  refine ⟨by simp only [FS.setv_env, Function.update_self]; rw [getLastD_eq_getD, wlen],
    by simp; exact getD_lt_pow _ wlt _, ?_, fW.trans (Wr.setv _ (by decide) _)⟩
  simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 28 by decide), f14]; ring

/-- The field value of the circuit word. -/
theorem wfold_last_ev {F : Type} [Field F] {p f : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (hp : GF.ModulusOk p f)
    (m : ℕ) (ins : List ℕ) (hins : ∀ a ∈ ins, a < 2 ^ f) (gates : List CodeGate)
    (hc : ∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ f) :
    ev φ ((wfold p f m ins gates).getLastD 0) = cvalF φ m (fun i => ev φ (ins.getD i 0)) gates := by
  obtain ⟨-, -, wev⟩ := wfold_spec φ hp m ins hins gates hc
  have := List.getLastD_map (f := ev φ) (l := wfold p f m ins gates) (a := 0)
  rw [ev_zero, wev] at this
  exact this.symm

/-- **The circuit evaluator** (proof of `thm:short-pcp-ours`): `28` is a reduced word whose field element is the circuit's value. -/
theorem circP_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (gates : List CodeGate)
    (ins : List ℕ) (m p Bd : ℕ)
    (hat : At (s.env 10) p (listWord gateWord gates)) (h14 : s.env 14 = p)
    (hend : p + (listWord gateWord gates).length ≤ Bd) (hB : BdOk G Bd)
    (h26 : s.env 26 = packW s.fl ins) (h27 : s.env 27 = m) (hins : ∀ a ∈ ins, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (hok : fieldOk G s.fl s.fp = true)
    (hconst : ∀ g ∈ gates, ∀ v, g = .const v → v < 2 ^ s.fl)
    (hK : s.fl * (gates.length + ins.length) + 1 ≤ G.K) :
    (evalS G circP s).env 28 < 2 ^ s.fl ∧
      ev φ ((evalS G circP s).env 28) = cvalF φ m (fun i => ev φ (ins.getD i 0)) gates ∧
      (evalS G circP s).env 14 = p + (listWord gateWord gates).length ∧
      Wr circW s (evalS G circP s) := by
  obtain ⟨w28, l28, c14, cW⟩ := circP_word G s gates ins m p Bd hat h14 hend hB h26 h27 hins h23 hok hconst hK
  refine ⟨l28, ?_, c14, cW⟩
  rw [w28]; exact wfold_last_ev φ (fl_bounds hok).2.2.1 m ins hins gates hconst

end NearCubicGates.Adapters.ShortPCP.Machines.FL
