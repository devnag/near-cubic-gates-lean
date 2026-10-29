import SourceAdapters.RAMACSP.GenEmit
import SourceAdapters.Routing.CoordinateMachineOutput

/-!
# Raw natural and gate output for the constraint circuit machine

The construction in `lem:generator`: the ordinary
generator writes the constraint circuit's gate words. These fixed FL programs
write the raw `natWord` fields of each gate, with no outer output framing.
The length calculation reuses `Gen.natLenP`; the output loops emit single bits.
Arguments 7,8,9 hold tag,x,y; 24 counts gates and 31 selects count/output mode.
Only 5,6 are output scratch. The preservation statements include the entire
remaining environment, field, input position, and failed-input flag.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.RAMACSP

variable {G : Glob}

/-- One raw output bit, with complete preservation. -/
theorem emit_spec (s : FS) (e : E) (W : List Var) :
    Appends W s (evalS G (.emit e) s) [evalE G s e != 0] :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concatenate the exact raw words printed by the iterations. -/
theorem appends_loop (i : Var) (n : E) (body : S) (W : List Var) (hi : i ∈ W)
    (s : FS) (m : ℕ) (hm : min (evalE G s n) G.N = m) (g : ℕ → List Bool)
    (hstep : ∀ j < m, ∀ t, Appends W s t ((List.range j).flatMap g) →
      Appends W (t.setv i j) (evalS G body (t.setv i j)) (g j)) :
    Appends W s (evalS G (.loop i n body) s) ((List.range m).flatMap g) := by
  have h := loop_inv G (i := i) (n := n) (body := body) (s := s)
    (fun j t => Appends W s t ((List.range j).flatMap g))
    (by simpa using Appends.refl W s) (by
      rw [hm]
      intro j hj t ht
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact ht.trans ((Appends.setv W t i hi j).trans (hstep j hj t ht)))
  rwa [hm] at h

/-- Raw `natWord` of variable `a`, using only scratch variables 5 and 6. -/
def natOut (a : Var) : S :=
  .seq (Gen.natLenP a) (.seq (.loop 5 (.v 6) (.emit (.k 1)))
    (.seq (.emit (.k 0)) (.loop 5 (.v 6) (.emit (.md (.shr (.v a) (.v 5)) (.k 2))))))

theorem natOut_spec (G : Glob) (s : FS) (a : Var) (ha5 : a ≠ 5) (ha6 : a ≠ 6)
    (hL : natBitLength (s.env a) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Appends [5, 6] s (evalS G (natOut a) s) (natWord (s.env a)) := by
  set v := s.env a with hv
  set L := natBitLength v
  have hcap := cap_add G
  have hKp : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have h2 : 2 ≤ G.cap := by omega
  have ht : evalS G (natOut a) s =
      evalS G (.loop 5 (.v 6) (.emit (.md (.shr (.v a) (.v 5)) (.k 2))))
        (evalS G (.emit (.k 0)) (evalS G (.loop 5 (.v 6) (.emit (.k 1)))
          (evalS G (Gen.natLenP a) s))) := rfl
  rw [ht]
  obtain ⟨l6, e0⟩ := Gen.natLenP_spec (G := G) s a ha6 hL hN
  have e1 : Appends [6] s (evalS G (Gen.natLenP a) s) [] :=
    ⟨e0.env, by simpa only [dbl, List.flatMap_nil] using e0.out,
      e0.fl, e0.fp, e0.ip, e0.bad⟩
  generalize hs1 : evalS G (Gen.natLenP a) s = s1 at l6 e1
  have s1a : s1.env a = v := e1.env a (by simp [ha6])
  have l6L : s1.env 6 = L := l6
  have hm : min (evalE G s1 (.v 6)) G.N = L := by
    rw [eE_v, l6L]
    exact min_eq_left (by omega)
  have e2 := appends_loop 5 (.v 6) (.emit (.k 1)) [5] (by simp) s1 L hm
    (fun _ => [true]) (fun j _ t _ => by
      simpa [evalE, min_eq_left (show 1 ≤ G.cap by omega)] using
        (emit_spec (G := G) (t.setv 5 j) (.k 1) [5]))
  generalize hs2 : evalS G (.loop 5 (.v 6) (.emit (.k 1))) s1 = s2 at e2
  have e3 := emit_spec (G := G) s2 (.k 0) [5]
  generalize hs3 : evalS G (.emit (.k 0)) s2 = s3 at e3
  have s36 : s3.env 6 = L := by
    rw [e3.env 6 (by simp), e2.env 6 (by simp), l6L]
  have s3a : s3.env a = v := by
    rw [e3.env a (by simp [ha5]), e2.env a (by simp [ha5]), s1a]
  have hm' : min (evalE G s3 (.v 6)) G.N = L := by
    rw [eE_v, s36]
    exact min_eq_left (by omega)
  have e4 := appends_loop 5 (.v 6) (.emit (.md (.shr (.v a) (.v 5)) (.k 2)))
    [5] (by simp) s3 L hm' (fun j => [v / 2 ^ j % 2 == 1]) (by
      intro j _ t te
      have ta : t.env a = v := by rw [te.env a (by simp [ha5]), s3a]
      have he : evalE G (t.setv 5 j) (.md (.shr (.v a) (.v 5)) (.k 2)) =
          v / 2 ^ j % 2 := by
        simp only [evalE, FS.setv_env, Function.update_self,
          Function.update_of_ne ha5, ta, min_eq_left h2]
      have hb : (v / 2 ^ j % 2 != 0) = (v / 2 ^ j % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]
      simpa only [he, hb] using
        (emit_spec (G := G) (t.setv 5 j) (.md (.shr (.v a) (.v 5)) (.k 2)) [5]))
  have hall := (e1.mono (W' := [5, 6]) (by simp)).trans
    ((e2.trans (e3.trans e4)).mono (by simp))
  convert hall using 1
  rw [Gen.natWord_eq_bits, Gen.range_flatMap_true', evalE, Nat.zero_min]
  simp [L, List.map_eq_flatMap]

/-- Three raw natural fields of one gate, held in variables 7,8,9. -/
def gateOut : S := .seq (natOut 7) (.seq (natOut 8) (natOut 9))

theorem gateOut_spec (G : Glob) (s : FS)
    (h7 : natBitLength (s.env 7) + 2 ≤ G.K)
    (h8 : natBitLength (s.env 8) + 2 ≤ G.K)
    (h9 : natBitLength (s.env 9) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Appends [5, 6] s (evalS G gateOut s)
      (natWord (s.env 7) ++ natWord (s.env 8) ++ natWord (s.env 9)) := by
  have hA := natOut_spec G s 7 (by decide) (by decide) h7 hN
  let t := evalS G (natOut 7) s
  have t8 : t.env 8 = s.env 8 := hA.env 8 (by decide)
  have t9 : t.env 9 = s.env 9 := hA.env 9 (by decide)
  have hB := natOut_spec G t 8 (by decide) (by decide) (by simpa only [t8] using h8) hN
  let u := evalS G (natOut 8) t
  have u9 : u.env 9 = s.env 9 := (hB.env 9 (by decide)).trans t9
  have hC := natOut_spec G u 9 (by decide) (by decide) (by simpa only [u9] using h9) hN
  simpa only [gateOut, evalS_seq, t, u, t8, u9, List.append_assoc] using hA.trans (hB.trans hC)

/-- Count every gate; append its fields exactly when mode 31 is nonzero. -/
def gateStep : S :=
  .seq (.ite (.v 31) gateOut .skip) (.set 24 (.add (.v 24) (.k 1)))

theorem gateStep_spec (G : Glob) (s : FS)
    (h7 : natBitLength (s.env 7) + 2 ≤ G.K)
    (h8 : natBitLength (s.env 8) + 2 ≤ G.K)
    (h9 : natBitLength (s.env 9) + 2 ≤ G.K) (hN : G.K ≤ G.N)
    (hcounter : s.env 24 + 1 ≤ G.cap) :
    Appends [5, 6, 24] s (evalS G gateStep s)
      (if s.env 31 = 0 then [] else
        natWord (s.env 7) ++ natWord (s.env 8) ++ natWord (s.env 9)) ∧
      (evalS G gateStep s).env 24 = s.env 24 + 1 := by
  let t := evalS G (.ite (.v 31) gateOut .skip) s
  have ha : Appends [5, 6] s t
      (if s.env 31 = 0 then [] else
        natWord (s.env 7) ++ natWord (s.env 8) ++ natWord (s.env 9)) := by
    by_cases hm : s.env 31 = 0
    · simpa only [t, evalS, evalE, hm, if_true] using Appends.refl [5, 6] s
    · simpa only [t, evalS, evalE, hm, if_false] using gateOut_spec G s h7 h8 h9 hN
  have t24 : t.env 24 = s.env 24 := ha.env 24 (by decide)
  have he : evalE G t (.add (.v 24) (.k 1)) = s.env 24 + 1 := by
    simp only [evalE, t24, min_eq_left (show 1 ≤ G.cap by omega), min_eq_left hcounter]
  have hb := Appends.setv [5, 6, 24] t 24 (by simp) (s.env 24 + 1)
  have ht : evalS G gateStep s = t.setv 24 (s.env 24 + 1) := by
    change t.setv 24 (evalE G t (.add (.v 24) (.k 1))) = _
    rw [he]
  refine ⟨?_, by simp only [ht, FS.setv_env, Function.update_self]⟩
  rw [ht]
  simpa only [List.append_nil] using (ha.mono (by simp)).trans hb

theorem natOut_wf (a : Var) (d : ℕ) (hd : d < 8) : wfS (natOut a) d = true := by
  simp [natOut, Gen.natLenP, wfS, dE, hd]

theorem gateOut_wf (d : ℕ) (hd : d < 8) : wfS gateOut d = true := by
  simp only [gateOut, wfS, natOut_wf _ d hd, Bool.and_self]

theorem gateStep_wf (d : ℕ) (hd : d < 8) : wfS gateStep d = true := by
  simp [gateStep, wfS, dE, gateOut_wf d hd]

end NearCubicGates.Adapters.Routing.TermsMachine
