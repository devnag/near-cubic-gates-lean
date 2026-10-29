import SourceAdapters.Compile.CNFMainA

/-!
# The printer, part B: tautologies, the three interpreter phases, the output unit

proof of `lem:multitape-refuter` (Tseitin conversion, three literals per clause, native literal-list codes): `tautP` writes the
input tautologies `circuitInputTautologies n`; `runsP` interprets the stored stream — the initial vector once,
the round template `fuel` times, the tail once — so that the clause store receives exactly the node clauses
`rclFrom n 0` of `RS.init.run (I ++ T^fuel ++ A)` (`runP_spec`); `finP` pops the output wire and appends the
output unit `positiveUnit (n + top)`. With `CNFRpn.requestFormula_rcl` the store then holds
`(requestFormula r).map encode`.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

/-! ## Input tautologies -/

def tautP : St VV MM := forP mT dN (clauseP v1 mT vZ mT v1 mT)

theorem tautP_spec (n : ℕ) (a : DS VV MM) (hk : KC a) (hn : a.env dN = n) (hcl : a.ram sCL = [])
    (hrc : a.rc sCL = 0) (hcode : ∀ i < n, ccode 1 i 0 i 1 i < 2 ^ C.Wd) (hnW : n < 2 ^ C.Wd) :
    Hs C tautP a (n * (70 + 4) + 4) (fun b => b.ram sCL = (circuitInputTautologies n).map Encodable.encode ∧
      b.rc sCL = n) := by
  refine Hs.mono (forP_ind (C := C) mT dN _ (by decide) n 70 (fun i b => KC b ∧ b.env dN = n ∧
      b.ram sCL = (circuitInputTautologies i).map Encodable.encode ∧ b.rc sCL = i) hnW (fun i b h => h.2.1)
    (fun i b v ⟨q1, q2, q3, q4⟩ => ⟨q1.set' mT (by decide) v, by vsimp [q2], q3, q4⟩)
    (fun i hi b ⟨q1, q2, q3, q4⟩ hc => ?_) a ⟨hk, hn, by rw [hcl]; rfl, hrc⟩) le_rfl (fun b h => h.2.2)
  have hend : b.rc sCL = (b.ram sCL).length := by rw [q3, q4]; simp
  refine Hs.mono (clauseP_spec v1 mT vZ mT v1 mT (by decide) (by decide) (by decide) (by decide) b q1.z hend
    (by rw [q1.one, q1.z, hc]; exact hcode i hi)) le_rfl ?_
  rintro d ⟨hE, hF⟩
  refine ⟨⟨q1.of_fr hF (by decide), by rw [hF dN (by decide), q2], ?_, ?_⟩, by rw [hF mT (by decide), hc]⟩
  · rw [hE.st, q3, q1.one, q1.z, hc]
    show _ = (circuitInputTautologies i ++ [circuitInputTautology i]).map Encodable.encode
    simp only [List.map_append, List.map_cons, List.map_nil, circuitInputTautology, positive, negative,
      encode_triple]
    rfl
  · rw [hE.rc, q4]; rfl

/-! ## Helpers -/

theorem IR.set {n k : ℕ} {S : RS} {a : DS VV MM} (h : IR n k S a) (x : Fin VV)
    (hx : ([dN, iIdx, iSp, iWl, iNc] ++ kcRegs).all (fun y => y != x) = true) (v : ℕ) : IR n k S (a.set x v) :=
  h.scratch rfl (fun _ _ => rfl) (fun y hy => DS.set_env_ne a v (by
    have := List.all_eq_true.mp hx y hy; simpa using this))

theorem IR.rew {n k : ℕ} {S : RS} {a : DS VV MM} (h : IR n k S a) : IR n k S (a.rew sTT) :=
  h.scratch rfl (fun _ hm => DS.rew_rc_ne _ hm) (fun _ _ => rfl)

theorem getD_map_seg (pre seg rest : List RTok) (i : ℕ) (hi : i < seg.length) :
    ((pre ++ seg ++ rest).map tcode).getD (pre.length + i) 0 = tcode seg[i] := by
  rw [List.map_append, List.map_append, List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp)]
  simp [hi]

theorem runOK_mid (n k : ℕ) (S : RS) (pre mid post : List RTok) (h : RunOK C n k S (pre ++ mid ++ post)) :
    RunOK C n (k + pre.length) (S.run pre) mid :=
  (((RunOK_append C n (pre ++ mid) post k S).mp h).1 |> (RunOK_append C n pre mid k S).mp).2

theorem rep_split (T : List RTok) (F i : ℕ) (hi : i < F) :
    (List.replicate F T).flatten = (List.replicate i T).flatten ++ T ++ (List.replicate (F - i - 1) T).flatten := by
  conv_lhs => rw [show F = i + 1 + (F - i - 1) by omega]
  rw [List.replicate_add, List.replicate_add, List.flatten_append, List.flatten_append]
  simp

theorem rep_succ (T : List RTok) (i : ℕ) :
    (List.replicate (i + 1) T).flatten = (List.replicate i T).flatten ++ T := by
  rw [List.replicate_succ', List.flatten_append]; simp

theorem len_rep (T : List RTok) (i : ℕ) : (List.replicate i T).flatten.length = i * T.length := by
  simp

/-! ## The three interpreter phases -/

def roundP : St VV MM := .seq (seekP sTT mP2) (.seq (.op (.copy iLen mLT)) runP)

def runsP : St VV MM :=
  .seq (.op (.rwM sTT)) (.seq (.op (.copy iLen mLI)) (.seq runP (.seq (forP mR dF roundP)
    (.seq (seekP sTT mP3) (.seq (.op (.copy iLen mLA)) runP)))))

/-- The stream the interpreter runs: initial vector, `F` template rounds, tail. -/
def runToks (I T A : List RTok) (F : ℕ) : List RTok := I ++ (List.replicate F T).flatten ++ A

def runsCost (I T A : List RTok) (F k : ℕ) : ℕ :=
  (F + 1) * (7 * (I.length + T.length + A.length + 3) + 30) +
    (runToks I T A F).length * (stepCost (k + (runToks I T A F).length) + 8)

theorem runsP_spec (n k F K : ℕ) (I T A : List RTok) (a : DS VV MM) (hIR : IR n k RS.init a)
    (htt : a.ram sTT = (I ++ [RTok.inp K] ++ T ++ [RTok.inp K] ++ A ++ [RTok.inp K]).map tcode)
    (hrc : a.rc sTT ≤ I.length + T.length + A.length + 3)
    (hLI : a.env mLI = I.length) (hLT : a.env mLT = T.length) (hLA : a.env mLA = A.length)
    (hP2 : a.env mP2 = I.length + 1) (hP3 : a.env mP3 = I.length + 1 + T.length + 1) (hF : a.env dF = F)
    (hok : RunOK C n k RS.init (runToks I T A F))
    (hW : 64 * (n + k + (runToks I T A F).length) + 64 + I.length + T.length + A.length + F + 10 ≤ 2 ^ C.Wd) :
    Hs C runsP a (runsCost I T A F k) (fun b => IR n (k + (runToks I T A F).length)
      (RS.init.run (runToks I T A F)) b) := by
  set Z := I.length + T.length + A.length + 3 with hZ
  set N := (runToks I T A F).length with hN
  set B := stepCost (k + N) + 8 with hB
  have hNl : N = I.length + F * T.length + A.length := by rw [hN, runToks]; simp; omega
  have hlenZ : (a.ram sTT).length = Z := by rw [htt]; simp; omega
  have hFW : F < 2 ^ C.Wd := by omega
  have cI : I.length * (stepCost (k + I.length) + 8) + 4 ≤ I.length * B + 4 := by
    have := stepCost_mono (show k + I.length ≤ k + N by omega); gcongr; omega
  -- phase 1: the initial vector
  refine Hs.seqc (t1 := Z + 1) (t2 := 1 + (I.length * B + 4) + (F * (6 * Z + T.length * B + 17) + 4) +
      (6 * Z + 6) + 1 + (A.length * B + 4) + 5)
    (Hs.mono (hs_rwM C sTT a) (by omega) (fun b h => h)) (fun b1 hb1 => ?_)
    (by unfold runsCost; rw [← hN, ← hB, ← hZ, hNl]; ring_nf; omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := (I.length * B + 4) + (F * (6 * Z + T.length * B + 17) + 4) +
      (6 * Z + 6) + 1 + (A.length * B + 4) + 4)
    (hs_copy C iLen mLI _ (by decide)) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  have hok1 : RunOK C n k RS.init I := by
    have := runOK_mid n k RS.init [] I ((List.replicate F T).flatten ++ A) (by simpa [runToks] using hok)
    simpa using this
  refine Hs.seqc (t1 := I.length * B + 4) (t2 := (F * (6 * Z + T.length * B + 17) + 4) +
      (6 * Z + 6) + 1 + (A.length * B + 4) + 3)
    (Hs.mono (runP_spec n k I RS.init _ ((IR.rew hIR).set iLen (by decide) _) (by omega) (by vsimp [DS.rew, hLI])
      (by simp [DS.rew]; omega)
      (fun i hi => by
        simp only [DS.set, DS.rew, Function.update_self, htt]
        have := getD_map_seg [] I ([RTok.inp K] ++ T ++ [RTok.inp K] ++ A ++ [RTok.inp K]) i hi
        simpa [List.append_assoc] using this) hok1) cI (fun b h => h))
    (fun b3 ⟨d1, d2, d3, _, _, d6⟩ => ?_) (by omega)
  -- phase 2: the template rounds
  have e3 : ∀ y ∈ [mLT, mLA, mP2, mP3, dF], b3.env y = a.env y := fun y hy => by
    rw [d6 y (by revert hy; decide +revert)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> rfl
  let Inv : ℕ → DS VV MM → Prop := fun i b => IR n (k + I.length + i * T.length)
    (RS.init.run (I ++ (List.replicate i T).flatten)) b ∧ b.ram sTT = a.ram sTT ∧ b.rc sTT ≤ Z ∧
    ∀ y ∈ [mLT, mLA, mP2, mP3, dF], b.env y = a.env y
  refine Hs.seqc (t1 := F * (6 * Z + T.length * B + 13 + 4) + 4) (t2 := (6 * Z + 6) + 1 + (A.length * B + 4) + 2)
    (forP_ind (C := C) mR dF roundP (by decide) F (6 * Z + T.length * B + 13) Inv hFW
      (fun i b h => by rw [h.2.2.2 dF (by simp), hF])
      (fun i b v ⟨q1, q2, q3, q4⟩ => ⟨q1.set mR (by decide) v, q2, q3, fun y hy => by
        rw [DS.set_env_ne _ _ (by revert hy; decide +revert)]; exact q4 y hy⟩)
      (fun i hi b ⟨q1, q2, q3, q4⟩ hc => ?_) _ ⟨by simpa using d1, by rw [d2]; rfl, by rw [d3]; simp [DS.rew]; omega,
        e3⟩)
    (fun b4 h4 => ?_) (by ring_nf; omega)
  · -- one round
    have qP2 : b.env mP2 = I.length + 1 := by rw [q4 mP2 (by simp), hP2]
    have qLT : b.env mLT = T.length := by rw [q4 mLT (by simp), hLT]
    refine Hs.seqc (t1 := 6 * Z + 6) (t2 := 1 + (T.length * B + 4) + 1)
      (Hs.mono (seekP_spec sTT mP2 (by decide) b (by rw [qP2, q2, hlenZ]; omega) (by omega)) (by omega)
        (fun d h => h)) (fun b5 ⟨s1, s2, s3, _, _, s6⟩ => ?_) (by omega)
    have hIR5 : IR n (k + I.length + i * T.length) (RS.init.run (I ++ (List.replicate i T).flatten)) b5 :=
      q1.scratch s2 s3 (fun y hy => s6 y (by revert hy; decide +revert))
    refine Hs.seqc (t1 := 1) (t2 := T.length * B + 4) (hs_copy C iLen mLT _ (by decide)) (fun b6 hb6 => ?_)
      (by omega)
    subst hb6
    have hsplit : runToks I T A F = (I ++ (List.replicate i T).flatten) ++ T ++
        ((List.replicate (F - i - 1) T).flatten ++ A) := by
      rw [runToks, rep_split T F i hi]; simp
    have hokT := runOK_mid n k RS.init _ T _ (hsplit ▸ hok)
    have hlenpre : (I ++ (List.replicate i T).flatten).length = I.length + i * T.length := by
      rw [List.length_append, len_rep]
    rw [hlenpre, ← Nat.add_assoc] at hokT
    have hiN : I.length + i * T.length + T.length ≤ N := by
      rw [hNl]; have : (i + 1) * T.length ≤ F * T.length := Nat.mul_le_mul_right _ hi
      rw [add_mul, one_mul] at this; omega
    refine Hs.mono (runP_spec n (k + I.length + i * T.length) T _ _ (hIR5.set iLen (by decide) _)
      (by omega) (by vsimp [s6 mLT (by decide), qLT])
      (by simp only [DS.set]; rw [s1, qP2, s2, q2, hlenZ]; omega)
      (fun j hj => by
        simp only [DS.set]; rw [s1, qP2, s2, q2, htt]
        have := getD_map_seg (I ++ [RTok.inp K]) T ([RTok.inp K] ++ A ++ [RTok.inp K]) j hj
        simpa [List.append_assoc] using this) hokT)
      (by have := stepCost_mono (show k + I.length + i * T.length + T.length ≤ k + N by omega)
          gcongr; omega) ?_
    rintro d ⟨r1, r2, r3, _, _, r6⟩
    have hd : ∀ y ∈ [mLT, mLA, mP2, mP3, dF], d.env y = a.env y := fun y hy => by
      rw [r6 y (by revert hy; decide +revert), DS.set_env_ne _ _ (by revert hy; decide +revert),
        s6 y (by revert hy; decide +revert)]; exact q4 y hy
    refine ⟨⟨?_, by rw [r2]; simp only [DS.set]; rw [s2, q2], by rw [r3]; simp only [DS.set]; rw [s1, qP2]; omega,
      hd⟩, by rw [r6 mR (by decide), DS.set_env_ne _ _ (by decide), s6 mR (by decide), hc]⟩
    rw [show k + I.length + (i + 1) * T.length = k + I.length + i * T.length + T.length by ring, rep_succ,
      ← List.append_assoc, RS.run_append]
    exact r1
  -- phase 3: the tail
  obtain ⟨q1, q2, q3, q4⟩ := h4
  have qP3 : b4.env mP3 = I.length + 1 + T.length + 1 := by rw [q4 mP3 (by simp), hP3]
  have qLA : b4.env mLA = A.length := by rw [q4 mLA (by simp), hLA]
  refine Hs.seqc (t1 := 6 * Z + 6) (t2 := 1 + (A.length * B + 4) + 1)
    (Hs.mono (seekP_spec sTT mP3 (by decide) b4 (by rw [qP3, q2, hlenZ]; omega) (by omega)) (by omega)
      (fun d h => h)) (fun b5 ⟨s1, s2, s3, _, _, s6⟩ => ?_) (by omega)
  have hIR5 := q1.scratch s2 s3 (fun y hy => s6 y (by revert hy; decide +revert))
  refine Hs.seqc (t1 := 1) (t2 := A.length * B + 4) (hs_copy C iLen mLA _ (by decide)) (fun b6 hb6 => ?_)
    (by omega)
  subst hb6
  have hokA := runOK_mid n k RS.init (I ++ (List.replicate F T).flatten) A [] (by simpa [runToks] using hok)
  have hlenpre : (I ++ (List.replicate F T).flatten).length = I.length + F * T.length := by
    rw [List.length_append, len_rep]
  rw [hlenpre, ← Nat.add_assoc] at hokA
  refine Hs.mono (runP_spec n (k + I.length + F * T.length) A _ _ (hIR5.set iLen (by decide) _)
    (by rw [hNl] at hW; omega) (by vsimp [s6 mLA (by decide), qLA])
    (by simp only [DS.set]; rw [s1, qP3, s2, q2, hlenZ]; omega)
    (fun j hj => by
      simp only [DS.set]
      rw [s1, qP3, s2, q2, htt, show I.length + 1 + T.length + 1 + j =
        (I ++ [RTok.inp K] ++ T ++ [RTok.inp K]).length + j by simp; omega]
      exact getD_map_seg (I ++ [RTok.inp K] ++ T ++ [RTok.inp K]) A [RTok.inp K] j hj) hokA)
    (by have := stepCost_mono (show k + I.length + F * T.length + A.length ≤ k + N by omega)
        gcongr; omega) ?_
  rintro d ⟨r1, _⟩
  rw [show k + N = k + I.length + F * T.length + A.length by omega, runToks, RS.run_append]
  exact r1

/-! ## The output unit -/

def finP : St VV MM :=
  .seq (popP iX) (.seq (.op (.copy iG dN)) (.seq (.op (.add iG iX)) (clauseP v1 iG v1 iG v1 iG)))

theorem finP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a)
    (hW1 : S.stk.length + 2 < 2 ^ C.Wd) (hW2 : n + (popS S.stk).1 < 2 ^ C.Wd)
    (hcode : ccode 1 (n + (popS S.stk).1) 1 (n + (popS S.stk).1) 1 (n + (popS S.stk).1) < 2 ^ C.Wd) :
    Hs C finP a (a.rc sSK + 5 * S.stk.length + 85) (fun b =>
      b.ram sCL = (circuitInputTautologies n ++ (rclFrom n 0 S.nodes ++
        [positiveUnit (n + (popS S.stk).1)])).map Encodable.encode ∧ b.rc sCL = (b.ram sCL).length ∧ KC b) := by
  set g := n + (popS S.stk).1 with hg
  refine Hs.seqc (t1 := a.rc sSK + 5 * S.stk.length + 10) (t2 := 74)
    (popP_spec iX (by decide) a S.stk h.stk h.kc.z h.kc.one hW1) (fun b1 ⟨p1, _, p3, _, p5, _, _, p8⟩ => ?_)
    (by omega)
  have k1 : KC b1 := h.kc.of_fr p8 (by decide)
  have n1 : b1.env dN = n := by rw [p8 dN (by decide), h.dn]
  refine Hs.seqc (t1 := 1) (t2 := 72) (hs_copy C iG dN b1 (by decide)) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  refine Hs.seqc (t1 := 1) (t2 := 70) (hs_add C iG iX _ (by decide) (by vsimp [n1, p1]; omega))
    (fun b3 hb3 => ?_) (by omega)
  subst hb3
  set b3 := (b1.set iG (b1.env dN)).set iG ((b1.set iG (b1.env dN)).env iG + (b1.set iG (b1.env dN)).env iX)
    with hb3
  have k3 : KC b3 := (k1.set' iG (by decide) _).set' iG (by decide) _
  have gG : b3.env iG = g := by rw [hb3]; vsimp [n1, p1, hg]
  have r3 : b3.ram = a.ram := p3
  have c3 : b3.rc sCL = a.rc sCL := p5 sCL (by decide)
  refine Hs.mono (clauseP_spec v1 iG v1 iG v1 iG (by decide) (by decide) (by decide) (by decide) b3 k3.z
    (by rw [c3, r3]; exact h.rccl) (by rw [k3.one, gG]; exact hcode)) le_rfl ?_
  rintro e ⟨hE, hF⟩
  have hst : e.ram sCL = a.ram sCL ++ [ccode 1 g 1 g 1 g] := by rw [hE.st, k3.one, gG, r3]
  refine ⟨?_, by rw [hE.rc, hE.st, c3, h.rccl, r3]; simp, k3.of_fr hF (by decide)⟩
  rw [hst, h.cl]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, positiveUnit, positive,
    encode_triple]
  rfl

end NearCubicGates.Adapters.Compile
