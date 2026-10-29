import SourceAdapters.ShortPCP.Machines.FLangDeq
import SourceAdapters.ShortPCP.TimeDP

/-!
# Single-run time, machine layer 17: the table of `length_{RS,=}`

The index arithmetic of `Translate` and of `V_{RS,<}`, `V_{RS,>}`, `V_VRS` uses `lengthEq T0 κ'` (BCGT13 Lemma C.10,
recursion (28)) for `κ' ≤ f`. `ltP` fills the table `18 := [lengthEq T0 0, …, lengthEq T0 f]` (word width
`17 := 8f + 16`, `Time.lengthEq_lt`) entry by entry from the smaller entries (`Time.lengthEq_rec`), with the builder
`genP2` (`ltP_spec`). Scratch `46`, `52`, `54`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

variable (G : Glob)

/-- Entry `e` of the table in `18` (width in `17`). -/
def getT (e : E) : E := .md (.shr (.v 18) (.mul e (.v 17))) (.shl (.k 1) (.v 17))

/-- Entry `κ'` (in `54`) from the earlier entries: `0` for `κ' ≤ 4`, else recursion (28). -/
def ltBody : S :=
  .ite (.lt (.k 4) (.v 54))
    (.set 46 (.add (.add (.shl (.k 1) (.add (.div (.add (.v 54) (.k 1)) (.k 2)) (.add (.div (.v 54) (.k 2)) (.k 2))))
        (.mul (.shl (.k 1) (.div (.add (.v 54) (.k 1)) (.k 2))) (getT (.add (.div (.v 54) (.k 2)) (.k 2)))))
      (.mul (.shl (.k 1) (.add (.div (.v 54) (.k 2)) (.k 1))) (getT (.div (.add (.v 54) (.k 1)) (.k 2))))))
    (.set 46 (.k 0))

/-- **The table of `lengthEq T0`** for `κ' ≤ f` (`f` in `23`). -/
def ltP : S :=
  .seq (.set 17 (.add (.mul (.k 8) (.v 23)) (.k 16))) (.seq (.set 52 (.add (.v 23) (.k 1))) (genP 52 54 46 18 17 ltBody))

theorem getT_eval (t : FS) (e : E) (W j : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ W) (h18 : t.env 18 = packW W l)
    (h17 : t.env 17 = W) (he : evalE G t e = j) (hj : j * W ≤ G.K) (hW : W + 1 ≤ G.K) :
    evalE G t (getT e) = l.getD j 0 := by
  have hc := cap_ge G
  have h1 : min 1 G.cap = 1 := min_cap (by omega)
  have h2 : 2 ^ W ≤ G.cap := by
    have := pow_le_cap (G := G) (a := W + 1) hW; rw [pow_succ] at this; have := Nat.one_le_two_pow (n := W); omega
  simp only [getT, evalE, h18, h17, he, h1, one_mul, min_eq_left h2, min_eq_left (hj.trans hc)]
  exact packW_get W l hl j

/-- **The `lengthEq` table.** -/
theorem ltP_spec (s : FS) (f : ℕ) (h23 : s.env 23 = f) (hK : (f + 1) * (8 * f + 16) + 1 ≤ G.K) (hN : f + 1 ≤ G.N) :
    let t := evalS G ltP s
    t.env 18 = packW (8 * f + 16) ((List.range (f + 1)).map (lengthEq T0)) ∧ t.env 17 = 8 * f + 16 ∧
      Wr [17, 18, 46, 52, 54] s t := by
  intro t
  have hc := cap_ge G
  have hW : 8 * f + 16 + 1 ≤ G.K := by
    have := Nat.le_mul_of_pos_left (8 * f + 16) (show 0 < f + 1 by omega); omega
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hc2 : min 2 G.cap = 2 := min_cap (by omega)
  have hc4 : min 4 G.cap = 4 := min_cap (by omega)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have hcapW : 2 ^ (8 * f + 16) ≤ G.cap := by
    have := pow_le_cap (G := G) (a := 8 * f + 16 + 1) hW; rw [pow_succ] at this
    have := Nat.one_le_two_pow (n := 8 * f + 16); omega
  have hLlt : ∀ j ≤ f, lengthEq T0 j < 2 ^ (8 * f + 16) := fun j hj =>
    lt_of_lt_of_le (lengthEq_lt j) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e1 : min (min 8 G.cap * f) G.cap = 8 * f := by rw [min_cap (show 8 ≤ G.K by omega)]; exact min_cap (by omega)
  have e2 : min (8 * f + min 16 G.cap) G.cap = 8 * f + 16 := by rw [min_cap (show 16 ≤ G.K by omega)]; exact min_cap (by omega)
  have e3 : min (f + 1) G.cap = f + 1 := min_cap (by omega)
  have hs2 : evalS G (.set 52 (.add (.v 23) (.k 1))) (evalS G (.set 17 (.add (.mul (.k 8) (.v 23)) (.k 16))) s) =
      (s.setv 17 (8 * f + 16)).setv 52 (f + 1) := by
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false, h23, e1,
      e2, hc1, e3]
  have hgen := genP2_spec G 52 54 46 18 17 ltBody [46] ((s.setv 17 (8 * f + 16)).setv 52 (f + 1)) (f + 1) (8 * f + 16)
    (lengthEq T0) (by simp; omega) (by simp) (by rw [mul_comm]; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun j hj => hLlt j (by omega)) (by
      intro j hj u uW u54 u18
      have u17 : u.env 17 = 8 * f + 16 := by rw [uW.env 17 (by decide)]; simp
      refine ⟨?_, ?_⟩
      · by_cases h4 : 4 < j
        · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 1 := by simp [evalE, hc4, u54, h4]
          have hl : ∀ a ∈ (List.range j).map (lengthEq T0), a < 2 ^ (8 * f + 16) := by
            intro a ha; simp only [List.mem_map, List.mem_range] at ha; obtain ⟨b, hb, rfl⟩ := ha; exact hLlt b (by omega)
          have hjW : ∀ i, i ≤ f → i * (8 * f + 16) ≤ G.K := fun i hi => by
            have := Nat.mul_le_mul_right (8 * f + 16) (show i ≤ f + 1 by omega); omega
          have ea : min (j + min 1 G.cap) G.cap = j + 1 := by rw [hc1]; exact min_cap (by omega)
          have g1 := getT_eval G u (.add (.div (.v 54) (.k 2)) (.k 2)) (8 * f + 16) (j / 2 + 2) _ hl u18 u17
            (by simp only [evalE, u54, hc2]; exact min_cap (by omega)) (hjW _ (by omega)) hW
          have g2 := getT_eval G u (.div (.add (.v 54) (.k 1)) (.k 2)) (8 * f + 16) ((j + 1) / 2) _ hl u18 u17
            (by simp only [evalE, u54, hc2, ea]) (hjW _ (by omega)) hW
          rw [packW_map_range_getD (8 * f + 16), if_pos (show j / 2 + 2 < j by omega)] at g1
          rw [packW_map_range_getD (8 * f + 16), if_pos (show (j + 1) / 2 < j by omega)] at g2
          have hrec := lengthEq_rec j (by omega)
          rw [← pow_add] at hrec
          have hLj := hLlt j (by omega)
          have t2le : 2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2) ≤ lengthEq T0 j := by
            rw [hrec]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
          have t3le : 2 ^ (j / 2 + 1) * lengthEq T0 ((j + 1) / 2) ≤ lengthEq T0 j := by
            rw [hrec]; exact Nat.le_add_left _ _
          have t1le : 2 ^ ((j + 1) / 2 + (j / 2 + 2)) ≤ lengthEq T0 j := by
            rw [hrec]; exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
          have ea' : min (j + 1) G.cap = j + 1 := min_cap (by omega)
          have b1 : min ((j + 1) / 2 + (j / 2 + 2)) G.cap = (j + 1) / 2 + (j / 2 + 2) := min_cap (by omega)
          have b2 : min (j / 2 + 2) G.cap = j / 2 + 2 := min_cap (by omega)
          have b3 : min (j / 2 + 1) G.cap = j / 2 + 1 := min_cap (by omega)
          have c1 : min (2 ^ ((j + 1) / 2 + (j / 2 + 2))) G.cap = 2 ^ ((j + 1) / 2 + (j / 2 + 2)) := by
            apply min_eq_left; omega
          have c2 : min (2 ^ ((j + 1) / 2)) G.cap = 2 ^ ((j + 1) / 2) := min_cap_pow (by omega)
          have c3 : min (2 ^ (j / 2 + 1)) G.cap = 2 ^ (j / 2 + 1) := min_cap_pow (by omega)
          have c4 : min (2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2)) G.cap = 2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2) :=
            min_eq_left (by omega)
          have c5 : min (2 ^ (j / 2 + 1) * lengthEq T0 ((j + 1) / 2)) G.cap = 2 ^ (j / 2 + 1) * lengthEq T0 ((j + 1) / 2) :=
            min_eq_left (by omega)
          have c6 : min (2 ^ ((j + 1) / 2 + (j / 2 + 2)) + 2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2)) G.cap =
              2 ^ ((j + 1) / 2 + (j / 2 + 2)) + 2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2) := min_eq_left (by omega)
          have c7 : min (2 ^ ((j + 1) / 2 + (j / 2 + 2)) + 2 ^ ((j + 1) / 2) * lengthEq T0 (j / 2 + 2) +
              2 ^ (j / 2 + 1) * lengthEq T0 ((j + 1) / 2)) G.cap = lengthEq T0 j := by rw [hrec]; exact min_eq_left (by omega)
          simp only [ltBody, evalS_ite, hcond, one_ne_zero, if_false, evalS_set, FS.setv_env, Function.update_self]
          simp only [evalE, u54, hc1, hc2, one_mul, ea', b1, b2, b3, c1, c2, c3, g1, g2, c4, c5, c6, c7]
        · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 0 := by simp [evalE, hc4, u54, h4]
          rw [ltBody, evalS_ite, hcond, if_pos rfl]
          simp only [evalS_set, FS.setv_env, Function.update_self, evalE, hc0]
          exact (lengthEq_small j (by omega)).symm
      · by_cases h4 : 4 < j
        · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 1 := by simp [evalE, hc4, u54, h4]
          simp only [ltBody, evalS_ite, hcond, one_ne_zero, if_false]; exact Wr.setv _ (by decide) _
        · have hcond : evalE G u (.lt (.k 4) (.v 54)) = 0 := by simp [evalE, hc4, u54, h4]
          simp only [ltBody, evalS_ite, hcond, if_true]; exact Wr.setv _ (by decide) _)
  obtain ⟨g18, gW⟩ := hgen
  have ht : t = evalS G (genP 52 54 46 18 17 ltBody) ((s.setv 17 (8 * f + 16)).setv 52 (f + 1)) := by
    show evalS G ltP s = _
    simp only [ltP, evalS_seq]; rw [hs2]
  rw [ht]
  refine ⟨g18, ?_, ?_⟩
  · rw [gW.env 17 (by decide)]; simp
  · exact ((Wr.setv (W := [17, 18, 46, 52, 54]) (i := 17) s (by decide) _).trans
      (Wr.setv (W := [17, 18, 46, 52, 54]) (i := 52) _ (by decide) _)).trans (gW.mono (by decide))

end NearCubicGates.Adapters.ShortPCP.Machines.FL
