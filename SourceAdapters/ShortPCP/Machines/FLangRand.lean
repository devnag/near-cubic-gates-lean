import SourceAdapters.ShortPCP.Machines.FLangTrans

/-!
# Single-run time, machine layer 21: the tables of `rand_{RS,=}` and `query_{RS,=}`

BCGT13 Lemma C.9 gives the randomness of `V_{RS,=}` by recursion (27) (`randEqF`, read with fuel `κ`); the query
count `query_{RS,=}` is `2^κ` below `κ0 = 4` and the larger of the two recursive counts above. proof of `thm:short-pcp-ours` bounds
the work of a run by poly(f) field operations; the machine needs these counts at `κ = f` (the sub-verifiers' `rand`,
`query`, `length`). `query_{RS,=}` has the closed form `2^{min κ 4}` (`queryEq_eq`). `rand_{RS,=}` is tabulated for
`κ' ≤ f` like `length_{RS,=}` (`TimeDP.lean`): `tblP` puts both tables in `18` (`TblRep`, `tblP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

/-! ## The recursions with enough fuel -/

theorem randEqF_small (n κ : ℕ) (h : κ ≤ 4) : randEqF T0 n κ = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [randEqF, T0_κ0, h]

theorem randEqF_succ (n κ : ℕ) (h : 5 ≤ κ) :
    randEqF T0 (n + 1) κ = 1 + max ((κ + 1) / 2 + randEqF T0 n (κ / 2 + 2)) (κ / 2 + 1 + randEqF T0 n ((κ + 1) / 2)) := by
  simp only [randEqF, T0_κ0, T0_γ, T0_μ, show ¬ κ ≤ 4 by omega, if_false, Nat.add_zero, Nat.sub_zero]

/-- **Fuel independence** of recursion (27). -/
theorem randEqF_fuel : ∀ (n κ : ℕ), κ ≤ n → randEqF T0 n κ = randEq T0 κ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ hκ
    by_cases h4 : κ ≤ 4
    · rw [randEqF_small n κ h4, randEq, randEqF_small κ κ h4]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
      rw [randEq, hκ', randEqF_succ n' _ (by omega), randEqF_succ κ' _ (by omega), ← hκ']
      rw [ih n' (by omega) (κ / 2 + 2) (by omega), ih n' (by omega) ((κ + 1) / 2) (by omega),
        ih κ' (by omega) (κ / 2 + 2) (by omega), ih κ' (by omega) ((κ + 1) / 2) (by omega)]

theorem randEq_small (κ : ℕ) (h : κ ≤ 4) : randEq T0 κ = 0 := randEqF_small κ κ h

/-- **The table recurrence** (BCGT13 (27) with `(η, κ0, γ, μ) = (2, 4, 0, 1)`). -/
theorem randEq_rec (κ : ℕ) (h : 5 ≤ κ) :
    randEq T0 κ = 1 + max ((κ + 1) / 2 + randEq T0 (κ / 2 + 2)) (κ / 2 + 1 + randEq T0 ((κ + 1) / 2)) := by
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
  conv_lhs => rw [randEq, hκ', randEqF_succ κ' _ (by omega)]
  rw [← hκ', randEqF_fuel κ' _ (by omega), randEqF_fuel κ' _ (by omega)]

/-- `rand_{RS,=}(κ) ≤ 4κ`. -/
theorem randEq_le : ∀ κ : ℕ, randEq T0 κ ≤ 4 * κ := by
  intro κ
  induction κ using Nat.strong_induction_on with
  | _ κ ih =>
    by_cases h4 : κ ≤ 4
    · rw [randEq_small κ h4]; omega
    · rw [randEq_rec κ (by omega)]
      have h1 := ih (κ / 2 + 2) (by omega)
      have h2 := ih ((κ + 1) / 2) (by omega)
      omega

/-- **The query count in closed form**: `query_{RS,=}(κ) = 2^{min κ 4}`. -/
theorem queryEqF_eq : ∀ (n κ : ℕ), κ ≤ n → queryEqF T0 n κ = 2 ^ min κ 4
  | 0, κ, h => by simp [queryEqF, show κ = 0 by omega]
  | n + 1, κ, h => by
    by_cases h4 : κ ≤ 4
    · simp [queryEqF, T0_κ0, h4, min_eq_left h4]
    · simp only [queryEqF, T0_κ0, T0_γ, T0_μ, h4, if_false, Nat.sub_zero, Nat.add_zero]
      rw [queryEqF_eq n (κ / 2 + 1 + 1) (by omega), queryEqF_eq n ((κ + 1) / 2) (by omega),
        min_eq_right (show 4 ≤ κ / 2 + 1 + 1 by omega), min_eq_right (show 4 ≤ κ by omega)]
      exact max_eq_left (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))

theorem queryEq_eq (κ : ℕ) : queryEq T0 κ = 2 ^ min κ 4 := queryEqF_eq κ κ le_rfl

/-! ## The program -/

variable (G : Glob)

/-- Entry `e` of the table in `13` (width in `17`). -/
def getR (e : E) : E := .md (.shr (.v 13) (.mul e (.v 17))) (.shl (.k 1) (.v 17))

/-- Entry `κ'` (in `54`) of `rand_{RS,=}` from the earlier entries: `0` for `κ' ≤ 4`, else recursion (27). -/
def rtBody : S :=
  .ite (.lt (.k 4) (.v 54))
    (.seq (.set 45 (.add (.div (.add (.v 54) (.k 1)) (.k 2)) (getR (.add (.div (.v 54) (.k 2)) (.k 2)))))
    (.seq (.set 46 (.add (.add (.div (.v 54) (.k 2)) (.k 1)) (getR (.div (.add (.v 54) (.k 1)) (.k 2)))))
      (.ite (.lt (.v 45) (.v 46)) (.set 46 (.add (.k 1) (.v 46))) (.set 46 (.add (.k 1) (.v 45))))))
    (.set 46 (.k 0))

/-- **Both tables**: `18 := ` the `length_{RS,=}` table, followed by the `rand_{RS,=}` table (built in `13`). -/
def tblP : S :=
  .seq ltP (.seq (.set 52 (.add (.v 23) (.k 1))) (.seq (genP 52 54 46 13 17 rtBody)
    (.set 18 (.add (.v 18) (.shl (.v 13) (.mul (.add (.v 23) (.k 1)) (.v 17)))))))

/-- The variables `tblP` writes. -/
def tblW : List Var := [13, 17, 18, 45, 46, 52, 54]

theorem getR_eval (t : FS) (e : E) (W j : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ W) (h13 : t.env 13 = packW W l)
    (h17 : t.env 17 = W) (he : evalE G t e = j) (hj : j * W ≤ G.K) (hW : W + 1 ≤ G.K) :
    evalE G t (getR e) = l.getD j 0 := by
  have hc := cap_ge G
  have h1 : min 1 G.cap = 1 := min_cap (by omega)
  have h2 : 2 ^ W ≤ G.cap := by
    have := pow_le_cap (G := G) (a := W + 1) hW; rw [pow_succ] at this; have := Nat.one_le_two_pow (n := W); omega
  simp only [getR, evalE, h13, h17, he, h1, one_mul, min_eq_left h2, min_eq_left (hj.trans hc)]
  exact packW_get W l hl j

/-- **The two tables** (`TblRep`). -/
theorem tblP_spec (s : FS) (f : ℕ) (h23 : s.env 23 = f) (hK : 2 * ((f + 1) * (8 * f + 16)) + 1 ≤ G.K)
    (hN : f + 1 ≤ G.N) :
    let t := evalS G tblP s
    TblRep t f ∧ Wr tblW s t := by
  intro t
  have hc := cap_ge G
  have hK1 : (f + 1) * (8 * f + 16) + 1 ≤ G.K := by omega
  have hW : 8 * f + 16 + 1 ≤ G.K := by
    have := Nat.le_mul_of_pos_left (8 * f + 16) (show 0 < f + 1 by omega); omega
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have hc4 : min 4 G.cap = 4 := min_cap (by omega)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have hRlt : ∀ j ≤ f, randEq T0 j < 2 ^ (8 * f + 16) := fun j hj => by
    have h0 := randEq_le j
    have h1 : 4 * f < 2 ^ (4 * f) := Nat.lt_two_pow_self
    have h2 : 2 ^ (4 * f) ≤ 2 ^ (8 * f + 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hLlt : ∀ j ≤ f, lengthEq T0 j < 2 ^ (8 * f + 16) := fun j hj =>
    lt_of_lt_of_le (lengthEq_lt j) (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨l18, l17, lW⟩ := ltP_spec G s f h23 hK1 hN
  generalize ht1 : evalS G ltP s = t1 at l18 l17 lW
  have t23 : t1.env 23 = f := (lW.env 23 (by decide)).trans h23
  have e3 : min (f + 1) G.cap = f + 1 := min_cap (by omega)
  have hs2 : evalS G (.set 52 (.add (.v 23) (.k 1))) t1 = t1.setv 52 (f + 1) := by
    simp only [evalS_set, evalE, t23, hc1, e3]
  have hgen := genP2_spec G 52 54 46 13 17 rtBody [45, 46] (t1.setv 52 (f + 1)) (f + 1) (8 * f + 16)
    (randEq T0) (by simp; omega) (by simp [l17]) (by rw [mul_comm]; omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun j hj => hRlt j (by omega)) (by
      intro j hj u uW u54 u13
      have u17 : u.env 17 = 8 * f + 16 := by rw [uW.env 17 (by decide)]; simp [l17]
      by_cases h4 : 4 < j
      · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 1 := by simp [evalE, hc4, u54, h4]
        have hl : ∀ a ∈ (List.range j).map (randEq T0), a < 2 ^ (8 * f + 16) := by
          intro a ha; simp only [List.mem_map, List.mem_range] at ha; obtain ⟨b, hb, rfl⟩ := ha; exact hRlt b (by omega)
        have hjW : ∀ i, i ≤ f → i * (8 * f + 16) ≤ G.K := fun i hi => by
          have := Nat.mul_le_mul_right (8 * f + 16) (show i ≤ f + 1 by omega); omega
        have ea : min (j + min 1 G.cap) G.cap = j + 1 := by rw [hc1]; exact min_cap (by omega)
        have g1 := getR_eval G u (.add (.div (.v 54) (.k 2)) (.k 2)) (8 * f + 16) (j / 2 + 2) _ hl u13 u17
          (by simp only [evalE, u54, hc2]; exact min_cap (by omega)) (hjW _ (by omega)) hW
        have g2 := getR_eval G u (.div (.add (.v 54) (.k 1)) (.k 2)) (8 * f + 16) ((j + 1) / 2) _ hl u13 u17
          (by simp only [evalE, u54, hc2, ea]) (hjW _ (by omega)) hW
        rw [packW_map_range_getD (8 * f + 16), if_pos (show j / 2 + 2 < j by omega)] at g1
        rw [packW_map_range_getD (8 * f + 16), if_pos (show (j + 1) / 2 < j by omega)] at g2
        have hrec := randEq_rec j (by omega)
        have hb1 := randEq_le (j / 2 + 2)
        have hb2 := randEq_le ((j + 1) / 2)
        have ea' : min (j + 1) G.cap = j + 1 := min_cap (by omega)
        have b2 : min (j / 2 + 2) G.cap = j / 2 + 2 := min_cap (by omega)
        have b3 : min (j / 2 + 1) G.cap = j / 2 + 1 := min_cap (by omega)
        have hj4 : 4 * j + 8 ≤ G.cap := by omega
        have c1 : min ((j + 1) / 2 + randEq T0 (j / 2 + 2)) G.cap = (j + 1) / 2 + randEq T0 (j / 2 + 2) :=
          min_eq_left (by omega)
        have c2 : min (j / 2 + 1 + randEq T0 ((j + 1) / 2)) G.cap = j / 2 + 1 + randEq T0 ((j + 1) / 2) :=
          min_eq_left (by omega)
        have hs3 : evalS G (.seq (.set 46 (.add (.add (.div (.v 54) (.k 2)) (.k 1)) (getR (.div (.add (.v 54) (.k 1))
            (.k 2))))) (.ite (.lt (.v 45) (.v 46)) (.set 46 (.add (.k 1) (.v 46))) (.set 46 (.add (.k 1) (.v 45)))))
            (evalS G (.set 45 (.add (.div (.add (.v 54) (.k 1)) (.k 2)) (getR (.add (.div (.v 54) (.k 2)) (.k 2))))) u) =
            evalS G (.ite (.lt (.v 45) (.v 46)) (.set 46 (.add (.k 1) (.v 46))) (.set 46 (.add (.k 1) (.v 45))))
              ((u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2))).setv 46 (j / 2 + 1 + randEq T0 ((j + 1) / 2))) := by
          have g2' : evalE G (u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2)))
              (getR (.div (.add (.v 54) (.k 1)) (.k 2))) = randEq T0 ((j + 1) / 2) := by
            rw [← g2]; simp [getR, evalE]
          rw [evalS_seq, evalS_set, evalS_set]
          simp only [evalE, u54, hc1, hc2, ea', b2, b3, g1, c1]
          rw [show evalE G (u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2))) (getR (.div (.add (.v 54) (.k 1)) (.k 2))) =
            randEq T0 ((j + 1) / 2) from g2']
          simp only [FS.setv_env, Function.update_of_ne (show (54 : Var) ≠ 45 by decide), u54, ea, hc1, hc2, b3, c2]
        refine ⟨?_, ?_⟩
        · rw [rtBody, evalS_ite, hcond, if_neg one_ne_zero, evalS_seq, hs3, evalS_ite]
          rw [hrec]
          by_cases hlt : (j + 1) / 2 + randEq T0 (j / 2 + 2) < j / 2 + 1 + randEq T0 ((j + 1) / 2)
          · have hc' : evalE G ((u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2))).setv 46
                (j / 2 + 1 + randEq T0 ((j + 1) / 2))) (.lt (.v 45) (.v 46)) = 1 := by
              simp [evalE, hlt]
            rw [hc', if_neg one_ne_zero, max_eq_right hlt.le]
            simp only [evalS_set, FS.setv_env, Function.update_self, evalE, Function.update_apply]
            simp only [show ((46 : Var) = 45) = False by decide, if_false, if_true, hc1]
            exact min_eq_left (by omega)
          · have hc' : evalE G ((u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2))).setv 46
                (j / 2 + 1 + randEq T0 ((j + 1) / 2))) (.lt (.v 45) (.v 46)) = 0 := by
              simp [evalE, hlt]
            rw [hc', if_pos rfl, max_eq_left (by omega)]
            simp only [evalS_set, FS.setv_env, Function.update_self, evalE, Function.update_apply]
            simp only [show ((45 : Var) = 46) = False by decide, if_false, if_true, hc1]
            exact min_eq_left (by omega)
        · rw [rtBody, evalS_ite, hcond, if_neg one_ne_zero, evalS_seq, hs3, evalS_ite]
          have w0 : Wr [45, 46] u ((u.setv 45 ((j + 1) / 2 + randEq T0 (j / 2 + 2))).setv 46
              (j / 2 + 1 + randEq T0 ((j + 1) / 2))) := (Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)
          split_ifs <;> exact w0.trans (Wr.setv _ (by decide) _)
      · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 0 := by simp [evalE, hc4, u54, h4]
        rw [rtBody, evalS_ite, hcond, if_pos rfl]
        refine ⟨?_, Wr.setv _ (by decide) _⟩
        simp only [evalS_set, FS.setv_env, Function.update_self, evalE, hc0]
        exact (randEq_small j (by omega)).symm)
  obtain ⟨g13, gW⟩ := hgen
  generalize ht2 : evalS G (genP 52 54 46 13 17 rtBody) (t1.setv 52 (f + 1)) = t2 at g13 gW
  have t217 : t2.env 17 = 8 * f + 16 := by rw [gW.env 17 (by decide)]; simp [l17]
  have t218 : t2.env 18 = packW (8 * f + 16) ((List.range (f + 1)).map (lengthEq T0)) := by
    rw [gW.env 18 (by decide)]; simp [l18]
  have t223 : t2.env 23 = f := by rw [gW.env 23 (by decide)]; simp [t23]
  have hLw : ∀ a ∈ (List.range (f + 1)).map (lengthEq T0), a < 2 ^ (8 * f + 16) := by
    intro a ha; simp only [List.mem_map, List.mem_range] at ha; obtain ⟨b, hb, rfl⟩ := ha; exact hLlt b (by omega)
  have hRw : ∀ a ∈ (List.range (f + 1)).map (randEq T0), a < 2 ^ (8 * f + 16) := by
    intro a ha; simp only [List.mem_map, List.mem_range] at ha; obtain ⟨b, hb, rfl⟩ := ha; exact hRlt b (by omega)
  have hLp := packW_lt (8 * f + 16) _ hLw
  have hRp := packW_lt (8 * f + 16) _ hRw
  simp only [List.length_map, List.length_range] at hLp hRp
  have hsum := packW_append (8 * f + 16) ((List.range (f + 1)).map (lengthEq T0)) ((List.range (f + 1)).map (randEq T0))
  simp only [List.length_map, List.length_range] at hsum
  have hall := packW_lt (8 * f + 16) _ (fun a ha => (List.mem_append.mp ha).elim (hLw a) (hRw a))
  simp only [List.length_append, List.length_map, List.length_range] at hall
  have hcapA : 2 ^ ((8 * f + 16) * (f + 1 + (f + 1))) ≤ G.cap + 1 := pow_le_cap (by
    have e : (8 * f + 16) * (f + 1 + (f + 1)) = 2 * ((f + 1) * (8 * f + 16)) := by ring
    omega)
  have hmul : min ((f + 1) * (8 * f + 16)) G.cap = (f + 1) * (8 * f + 16) := min_cap (by omega)
  have ee : (8 * f + 16) * (f + 1) = (f + 1) * (8 * f + 16) := mul_comm _ _
  rw [ee] at hsum
  have hLRcap : packW (8 * f + 16) ((List.range (f + 1)).map (lengthEq T0) ++ (List.range (f + 1)).map (randEq T0)) ≤
      G.cap := by omega
  have hshl : packW (8 * f + 16) ((List.range (f + 1)).map (randEq T0)) * 2 ^ ((f + 1) * (8 * f + 16)) ≤ G.cap := by
    rw [mul_comm]; omega
  have ht : t = t2.setv 18 (packW (8 * f + 16) ((List.range (f + 1)).map (lengthEq T0) ++
      (List.range (f + 1)).map (randEq T0))) := by
    show evalS G tblP s = _
    simp only [tblP, evalS_seq]
    rw [ht1, hs2, ht2]
    simp only [evalS_set, evalE, t223, t217, t218, g13, hc1, e3, hmul]
    rw [min_eq_left hshl, mul_comm (packW _ _) (2 ^ _), ← hsum, min_eq_left hLRcap]
  rw [ht]
  refine ⟨⟨by simp [t217], _, by simp, fun a ha => (List.mem_append.mp ha).elim (hLw a) (hRw a), ?_⟩, ?_⟩
  · intro j hj
    constructor
    · rw [List.getD_append _ _ _ _ (by simp; omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range, hj,
        show j < f + 1 by omega]
    · rw [List.getD_append_right _ _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range,
        show j < f + 1 by omega]
  · exact ((lW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans ((gW.mono (by decide)).trans
      (Wr.setv _ (by decide) _))

end NearCubicGates.Adapters.ShortPCP.Machines.FL
