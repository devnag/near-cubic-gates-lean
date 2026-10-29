import SourceAdapters.Compile.CNFInterpG

/-!
# Token interpreter, part H: a run of stored tokens

`runP` interprets `env iLen` consecutive tokens of the token store from its cursor: `runP_spec` takes `IR n k S a`
to `IR n (k + |toks|) (S.run toks)` when the store holds `toks` there and every step is in range (`RunOK`).
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def iCt : Fin VV := ⟨79, by decide⟩
def iLen : Fin VV := ⟨80, by decide⟩

variable {C : Ctx}

/-- Every step of the run is in range: payloads bounded by the step bound and clause codes below `2^Wd`. -/
def RunOK (C : Ctx) (n : ℕ) : ℕ → RS → List RTok → Prop
  | _, _, [] => True
  | k, S, t :: ts => (tpay t ≤ k ∧ ClauseOK C n S t) ∧ RunOK C n (k + 1) (S.step t) ts

def runP : St VV MM := .seq (.op (.zero iCt)) (.loop (.lt iCt iLen) (.seq stepP (.op (.inc iCt))))

theorem stepCost_mono {k l : ℕ} (h : k ≤ l) : stepCost k ≤ stepCost l := by unfold stepCost; omega

theorem runP_spec (n k : ℕ) (toks : List RTok) (S : RS) (a : DS VV MM) (h : IR n k S a)
    (hW : 64 * (n + k + toks.length) + 64 ≤ 2 ^ C.Wd) (hL : a.env iLen = toks.length)
    (hlen : a.rc sTT + toks.length ≤ (a.ram sTT).length)
    (htoks : ∀ (i : ℕ) (hi : i < toks.length), (a.ram sTT).getD (a.rc sTT + i) 0 = tcode toks[i])
    (hok : RunOK C n k S toks) :
    Hs C runP a (toks.length * (stepCost (k + toks.length) + 8) + 4) (fun d =>
      IR n (k + toks.length) (S.run toks) d ∧ d.ram sTT = a.ram sTT ∧ d.rc sTT = a.rc sTT + toks.length ∧
      d.ip = a.ip ∧ d.out = a.out ∧ Fr a d (iCt :: iTk :: iPl :: iK :: irT)) := by
  set L := toks.length with hLdef
  let I : ℕ → DS VV MM → Prop := fun i b => IR n (k + i) (S.run (toks.take i)) b ∧ b.env iCt = i ∧
    b.ram sTT = a.ram sTT ∧ b.rc sTT = a.rc sTT + i ∧ RunOK C n (k + i) (S.run (toks.take i)) (toks.drop i) ∧
    b.ip = a.ip ∧ b.out = a.out ∧ Fr a b (iCt :: iTk :: iPl :: iK :: irT)
  have hloop := Hs.loopN (C := C) (c := .lt iCt iLen) (s := .seq stepP (.op (.inc iCt))) (show iCt ≠ iLen by decide)
    I L (stepCost (k + L) + 6)
    (fun i hi b hb => by
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hb
      have bL : b.env iLen = L := by rw [b8 iLen (by decide), hL]
      refine ⟨by simp [Cnd.eval, b2, bL, hi], ?_⟩
      have hd : toks.drop i = toks[i] :: toks.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hd] at b5
      obtain ⟨⟨p1, p2⟩, p3⟩ := b5
      refine Hs.seqc (t1 := stepCost (k + i) + 4) (t2 := 1) (stepP_spec n (k + i) _ b b1 (by omega) toks[i]
        (a.rc sTT + i) b4 (by rw [b3]; omega) (by rw [b3]; exact htoks i hi) p1 p2) (fun d hd' => ?_)
        (by have := stepCost_mono (show k + i ≤ k + L by omega); omega)
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd'
      have dC : d.env iCt = i := by rw [d6 iCt (by decide), b2]
      refine Hs.op (OpEx.inc iCt d (by rw [dC]; omega)) ⟨?_, by rw [DS.set_env_self, dC], by simp [d2, b3],
        by simp [d3]; omega, ?_, by simp [d4, b6], by simp [d5, b7], ?_⟩
      · have e : S.run (toks.take (i + 1)) = (S.run (toks.take i)).step toks[i] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, RS.run_append]; rfl
        rw [e, show k + (i + 1) = k + i + 1 by omega]
        exact d1.scratch rfl (fun _ _ => rfl) (fun y hy => by
          simp only [DS.set, Function.update_apply]
          have : y ≠ iCt := by revert hy; decide +revert
          simp [this])
      · have e : S.run (toks.take (i + 1)) = (S.run (toks.take i)).step toks[i] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, RS.run_append]; rfl
        rw [e, show k + (i + 1) = k + i + 1 by omega]; exact p3
      · have hF : Fr b (d.set iCt (d.env iCt + 1)) (iCt :: iTk :: iPl :: iK :: irT) :=
          (Fr.weaken d6 (fun y hy => by simp at hy ⊢; tauto)).trans (Fr.set (x := iCt) d _ (by simp))
        exact b8.trans hF)
    (fun b hb => by
      obtain ⟨_, b2, _, _, _, _, _, b8⟩ := hb
      simp [Cnd.eval, b2, b8 iLen (by decide), hL])
  refine Hs.seqc (t1 := 1) (t2 := L * (stepCost (k + L) + 6 + 2) + 2) (hs_zero C iCt a) (fun b hb => ?_)
    (by ring_nf; omega)
  subst hb
  refine Hs.mono (hloop _ ⟨h.scratch rfl (fun _ _ => rfl) (fun y hy => by
      have : y ≠ iCt := by revert hy; decide +revert
      simp [DS.set, Function.update_apply, this]), by simp, rfl, by simp, by simpa using hok, rfl, rfl,
      Fr.set _ _ (by simp)⟩) le_rfl ?_
  rintro d ⟨d1, _, d3, d4, _, d6, d7, d8⟩
  rw [List.take_length] at d1
  exact ⟨d1, d3, d4, d6, d7, d8⟩

end NearCubicGates.Adapters.Compile
