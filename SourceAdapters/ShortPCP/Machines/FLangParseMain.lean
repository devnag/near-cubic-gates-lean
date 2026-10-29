import SourceAdapters.ShortPCP.Machines.FLangParseRec

/-!
# Single-run time, machine layer 20: the parse of the data word

`parseP` reads the data word (`At D 0 q.data`, `D` in variable `10`) and sets the field-word configuration
`fl := q.code.f`, `fp := q.code.irr`. Under `PCtx`, the parsed modulus satisfies
`GF.ModulusOk q.code.irr q.code.f` (`PCtx.field_ok`). It sets the width variable `23 := q.code.f` and leaves
the record `parseRec q` (`FLangParseRec.lean`) in variable `15` (`parseP_spec`). In Step 2, “Time and queries”, of the proof of `thm:short-pcp-ours`, the instance is already generated;
here its parameters are read from the data in `O(|data|)` passes. The circuits and the masks stay in `D`; the record holds their
positions.

Phases: `parseHead` (`f`, `irr`, the field), `parseH` (`H`: basis, `d_A`, offset), `parseC` (neighbor pairs and the constraint circuit),
`parseT` (skip `I`, read `x̄`, `m = log |x̄|`, `dB`, the masks), `parseI` (the actual input subspace `I`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Close.Cells (natWord_one natWord_zero natWord_bit natWord_length lt_natBitLength)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate listWord gateWord)
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable (G : Glob)

/-! ## Facts from the layout -/

section Ctx

variable {G} {q : Request} {D : ℕ} (c : PCtx G q D)
include c

theorem PCtx.piece (k : ℕ) (w : List Bool) (hk : k < 11) (hw : (pieces q).getD k [] = w) :
    At D (posOf q k) w ∧ posOf q (k + 1) = posOf q k + w.length ∧ posOf q k + w.length ≤ q.data.length := by
  obtain ⟨h1, h2⟩ := piece_at q c.at0 k w hk hw
  exact ⟨h1, h2, h2 ▸ posOf_le q (k + 1)⟩

theorem PCtx.irr_ge : 2 ^ q.code.f ≤ q.code.irr := Nat.ge_two_pow_of_testBit c.wf.1

theorem PCtx.f_lt : q.code.f + 1 ≤ q.data.length := by
  obtain ⟨-, -, h⟩ := c.piece 1 (natWord q.code.irr) (by norm_num) rfl
  have h1 := Nat.le_log_of_pow_le (by norm_num) c.irr_ge
  rw [natWord_len] at h; unfold natBitLength at h; omega

theorem PCtx.field_ok : fieldOk G q.code.f q.code.irr = true := by
  have := c.f_lt; have := c.W; have := Nat.div_le_self G.K 16; have := c.irr_ge; have h2 := c.wf.2.1
  rw [pow_succ] at h2
  simp only [fieldOk, decide_eq_true_eq]
  exact ⟨c.f1, by omega, c.irr_ge, by omega⟩

end Ctx

theorem count_le {α : Type} (g : α → List Bool) (L : List α) (hne : ∀ x ∈ L, 1 ≤ (g x).length) (p : ℕ)
    (d : ℕ) (hp : p + (listWord g L).length ≤ d) : L.length + 1 ≤ d := by
  have := length_le_flatten g L hne
  rw [listWord_eq, List.length_append] at hp; have := natWord_pos L.length; omega

theorem mul_le {a b d : ℕ} (ha : a ≤ d) (hb : b ≤ d) :
    a * b ≤ d * d + d := by
  have := Nat.mul_le_mul ha hb; omega


section Ctx2

variable {G} {q : Request} {D : ℕ} (c : PCtx G q D)
include c

theorem PCtx.iBw_len : (iBw q).length = q.mI := c.mi.symm

theorem PCtx.iBw_lt : ∀ a ∈ iBw q, a < 2 ^ q.code.f := c.wf.2.2.2.2.2.2.1

theorem PCtx.iOw_lt : iOw q < 2 ^ q.code.f := c.wf.2.2.2.2.2.2.2

theorem PCtx.xbar_le : q.xbar.length + 1 ≤ q.data.length := by
  obtain ⟨-, -, l9⟩ := c.piece 8 (frame q.xbar) (by norm_num) rfl
  rw [frame_len] at l9; omega

theorem PCtx.mI_le : q.mI + 1 ≤ q.data.length := by
  have := Nat.log_le_self 2 q.xbar.length; have := c.xbar_le; unfold Request.mI; omega

/-- **Every slot of the record fits the slot width.** -/
theorem PCtx.rec_lt : ∀ a ∈ parseRec q, a < 2 ^ (G.K / 16) := by
  have hf := c.f_lt
  have hmul := Nat.le_mul_self q.data.length
  obtain ⟨-, -, l3⟩ := c.piece 2 (listWord natWord q.code.hBasis) (by norm_num) rfl
  obtain ⟨-, -, l4⟩ := c.piece 3 (natWord q.code.hOffset) (by norm_num) rfl
  obtain ⟨-, -, l5⟩ := c.piece 4 (listWord Instance.pairWord q.code.nbr)
    (by norm_num) rfl
  obtain ⟨-, e7, l6⟩ := c.piece 5 (listWord gateWord q.code.cons) (by norm_num) rfl
  obtain ⟨-, -, l10⟩ := c.piece 9 (natWord q.dB) (by norm_num) rfl
  obtain ⟨-, -, l11⟩ := c.piece 10 (listWord frame q.masks) (by norm_num) rfl
  have hmH := count_le natWord q.code.hBasis (fun x _ => natWord_pos x) _ _ l3
  have hcN := count_le Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x) _ _ l5
  have hnm := count_le frame q.masks (fun x _ => frame_pos x) _ _ l11
  have hx := c.xbar_le
  have hm := c.mI_le
  intro a ha
  simp only [parseRec, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c.slot_le (by omega)
  · exact c.slot_le (by omega)
  · exact c.slot_lt (a := q.code.hBasis.length)
      (by unfold Request.dA; have := Nat.one_le_two_pow (n := q.code.hBasis.length); omega) (by omega)
  · exact c.slot_lt (packW_lt _ _ c.wf.2.2.1) (mul_le (by omega) (by omega))
  · exact c.slot_lt c.wf.2.2.2.1 (by omega)
  · exact c.slot_le (by unfold Instance.cN; omega)
  · refine c.slot_le ?_
    unfold posN; rw [listWord_eq, List.length_append] at l5; unfold Instance.cN; omega
  · exact c.slot_le (by unfold posC; omega)
  · exact c.slot_le (by omega)
  · exact c.slot_lt (bv_lt q.xbar) (by omega)
  · exact c.slot_le (by omega)
  · exact c.slot_lt (lt_natBitLength q.dB) (by have := natBitLength_le_len q.dB; omega)
  · exact c.slot_le (by omega)
  · refine c.slot_le ?_
    unfold posM; rw [listWord_eq, List.length_append] at l11; omega
  · refine c.slot_lt (packW_lt _ _ c.iBw_lt) ?_
    rw [c.iBw_len]; exact mul_le (by omega) (by omega)
  · exact c.slot_lt c.iOw_lt (by omega)

theorem PCtx.take_lt (n : ℕ) : ∀ a ∈ (parseRec q).take n, a < 2 ^ (G.K / 16) :=
  fun a ha => c.rec_lt a (List.mem_of_mem_take ha)

end Ctx2

/-! ## Phase 1: the header and the field -/

def parseHead : S :=
  .seq (.set 14 (.k 0)) (.seq pNat (.seq (.set 23 (.v 5)) (.seq pNat (.seq (.set 37 (.v 5))
    (.seq (.field (.v 23) (.v 37)) (.set 15 (.v 23)))))))

def headW : List Var := [5, 6, 8, 9, 14, 15, 23, 37]

theorem parseHead_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) :
    (evalS G parseHead s).env 14 = posOf q 2 ∧ (evalS G parseHead s).env 15 = packW (G.K / 16) [q.code.f] ∧
      (evalS G parseHead s).env 23 = q.code.f ∧ (evalS G parseHead s).fl = q.code.f ∧
      (evalS G parseHead s).fp = q.code.irr ∧ (∀ j, j ∉ headW → (evalS G parseHead s).env j = s.env j) ∧
      (evalS G parseHead s).out = s.out ∧ (evalS G parseHead s).bad = s.bad := by
  have hd := c.bd
  have hc := cap_ge G; have hK := c.K32
  obtain ⟨a1, e2, l1⟩ := c.piece 0 (natWord q.code.f) (by norm_num) rfl
  obtain ⟨a2, e3, l2⟩ := c.piece 1 (natWord q.code.irr) (by norm_num) rfl
  have p0 : posOf q 0 = 0 := rfl
  rw [p0] at a1 e2 l1
  set s0 := s.setv 14 (min 0 G.cap) with hs0
  have s0_14 : s0.env 14 = 0 := by simp [s0]
  obtain ⟨m5, m14, mW⟩ := pNat_at G s0 q.code.f _ _ (by simpa [s0] using a1) s0_14 (by omega) hd
  generalize hs2 : evalS G pNat s0 = s2 at m5 m14 mW
  set s3 := s2.setv 23 (s2.env 5) with hs3
  have s3_10 : s3.env 10 = s.env 10 := by simp [s3]; rw [mW.env 10 (by decide)]; simp [s0]
  obtain ⟨k5, k14, kW⟩ := pNat_at G s3 q.code.irr _ _ (by rw [s3_10]; exact a2)
    (by simp [s3]; rw [m14, e2]) (by omega) hd
  generalize hs4 : evalS G pNat s3 = s4 at k5 k14 kW
  set s5 := s4.setv 37 (s4.env 5) with hs5
  have s5_23 : s5.env 23 = q.code.f := by
    simp [s5]; rw [kW.env 23 (by decide)]; simp [s3, m5]
  have s5_37 : s5.env 37 = q.code.irr := by simp [s5, k5]
  have hW5 : Wr headW s s5 := by
    refine (((((Wr.setv _ (by decide) _).trans (mW.mono (by decide))).trans
      (Wr.setv _ (by decide) _)).trans (kW.mono (by decide))).trans (Wr.setv _ (by decide) _))
  have e : evalS G parseHead s = ({ s5 with fl := q.code.f, fp := q.code.irr } : FS).setv 15 q.code.f := by
    simp only [parseHead, evalS_seq, evalS_set, evalE]
    rw [show s.setv 14 (min 0 G.cap) = s0 from rfl, hs2, show s2.setv 23 (s2.env 5) = s3 from rfl, hs4,
      show s4.setv 37 (s4.env 5) = s5 from rfl]
    simp only [evalS, evalE, s5_23, s5_37, c.field_ok, if_true]
  rw [e]
  refine ⟨?_, by simp [packW], by simp (config := { decide := true }) [Function.update_apply, s5_23], rfl, rfl,
    fun j hj => ?_, hW5.out, hW5.bad⟩
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false]
    show s5.env 14 = _
    simp [s5, k14, e3]
  · have hj15 : j ≠ 15 := fun h => hj (by simp [headW, h])
    simp only [FS.setv_env, Function.update_of_ne hj15]
    exact hW5.env j hj

/-! ## Phase 2: the subspace `H` -/

def parseH : S :=
  .seq pListW (.seq (addRec 1 (.v 29)) (.seq (addRec 2 (.sub (.shl (.k 1) (.v 29)) (.k 1))) (.seq (addRec 3 (.v 30))
    (.seq pNat (addRec 4 (.v 5))))))

/-- The variables the parse writes. -/
def parseW : List Var := [5, 6, 8, 9, 14, 15, 23, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

/-- The variables the phases after the header write (not the width `23`). -/
def bodyW : List Var := [5, 6, 8, 9, 14, 15, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]

theorem parseRec_take_lt (q : Request) {D : ℕ} (c : PCtx G q D) (n : ℕ) (hn : n ≤ 16)
    (hall : ∀ i < n, (parseRec q).getD i 0 < 2 ^ (G.K / 16)) : ∀ a ∈ (parseRec q).take n, a < 2 ^ (G.K / 16) := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  simp only [List.length_take, parseRec_length] at hi
  have := hall i (by omega)
  rwa [List.getElem_take, ← List.getD_eq_getElem]

theorem parseH_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) (h14 : s.env 14 = posOf q 2)
    (h15 : s.env 15 = packW (G.K / 16) ((parseRec q).take 1)) (h23 : s.env 23 = q.code.f) :
    (evalS G parseH s).env 14 = posOf q 4 ∧ (evalS G parseH s).env 15 = packW (G.K / 16) ((parseRec q).take 5) ∧
      Wr bodyW s (evalS G parseH s) := by
  have hd := c.bd
  have hc := cap_ge G; have hK := c.K32; have hW := c.W; have hf := c.f_lt
  have hKd := Nat.div_le_self G.K 16
  obtain ⟨a3, e4, l3⟩ := c.piece 2 (listWord natWord q.code.hBasis) (by norm_num) rfl
  obtain ⟨a4, e5, l4⟩ := c.piece 3 (natWord q.code.hOffset) (by norm_num) rfl
  have hmH := count_le natWord q.code.hBasis (fun x _ => natWord_pos x) _ _ l3
  have hfm := mul_le (d := q.data.length) (a := q.code.f) (b := q.code.hBasis.length) (by omega) (by omega)
  have hl := c.wf.2.2.1
  obtain ⟨p29, p30, p14, pW⟩ := pListW_spec G s q.code.hBasis q.code.f (posOf q 2) q.data.length a3 h14 h23 hl
    (by have := Nat.le_mul_self q.data.length; omega) l3 hd
  generalize hs1 : evalS G pListW s = s1 at p29 p30 p14 pW
  have s1_15 : s1.env 15 = packW (G.K / 16) [q.code.f] := by rw [pW.env 15 (by decide)]; exact h15
  have hmHs : q.code.hBasis.length < 2 ^ (G.K / 16) := c.slot_le (by omega)
  have r1 := addRec_spec G s1 [q.code.f] 1 (.v 29) q.code.hBasis.length s1_15
    (by simp; exact c.slot_le (by omega)) rfl (by norm_num) p29 hmHs hK
  generalize hs2 : s1.setv 15 (packW (G.K / 16) ([q.code.f] ++ [q.code.hBasis.length])) = s2 at r1
  have hpm : 2 ^ q.code.hBasis.length ≤ G.cap := by
    have := pow_le_cap (G := G) (a := q.code.hBasis.length + 1) (by omega); rw [pow_succ] at this
    have := Nat.one_le_two_pow (n := q.code.hBasis.length); omega
  have hdA : evalE G s2 (.sub (.shl (.k 1) (.v 29)) (.k 1)) = q.dA := by
    simp only [evalE, ← hs2, FS.setv_env, Function.update_of_ne (show (29 : Var) ≠ 15 by decide), p29,
      show min 1 G.cap = 1 by omega, one_mul, min_eq_left hpm]
    rfl
  have hdAs : q.dA < 2 ^ (G.K / 16) := c.slot_lt (a := q.code.hBasis.length)
    (by unfold Request.dA; have := Nat.one_le_two_pow (n := q.code.hBasis.length); omega) (by omega)
  have r2 := addRec_spec G s2 ([q.code.f] ++ [q.code.hBasis.length]) 2 _ q.dA (by rw [← hs2]; simp)
    (by simp; exact ⟨c.slot_le (by omega), hmHs⟩) rfl (by norm_num) hdA hdAs hK
  generalize hs3 : s2.setv 15 (packW (G.K / 16) ([q.code.f] ++ [q.code.hBasis.length] ++ [q.dA])) = s3 at r2
  have hpB : packW q.code.f q.code.hBasis < 2 ^ (G.K / 16) := c.slot_lt (packW_lt _ _ hl) (by omega)
  have r3 := addRec_spec G s3 ([q.code.f] ++ [q.code.hBasis.length] ++ [q.dA]) 3 (.v 30) _ (by rw [← hs3]; simp)
    (by simp; exact ⟨c.slot_le (by omega), hmHs, hdAs⟩) rfl (by norm_num)
    (by simp only [evalE, ← hs3, ← hs2, FS.setv_env, Function.update_of_ne (show (30 : Var) ≠ 15 by decide), p30])
    hpB hK
  generalize hs4 : s3.setv 15 (packW (G.K / 16) ([q.code.f] ++ [q.code.hBasis.length] ++ [q.dA] ++
    [packW q.code.f q.code.hBasis])) = s4 at r3
  have s4_10 : s4.env 10 = s.env 10 := by
    rw [← hs4, ← hs3, ← hs2]; simp only [FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 15 by decide)]
    exact pW.env 10 (by decide)
  have s4_14 : s4.env 14 = posOf q 3 := by
    rw [← hs4, ← hs3, ← hs2]; simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide)]
    rw [p14, e4]
  obtain ⟨n5, n14, nW⟩ := pNat_at G s4 q.code.hOffset _ _ (by rw [s4_10]; exact a4) s4_14 l4 hd
  generalize hs5 : evalS G pNat s4 = s5 at n5 n14 nW
  have hO := c.wf.2.2.2.1
  have hOs : q.code.hOffset < 2 ^ (G.K / 16) :=
    c.slot_lt hO (by omega)
  have r4 := addRec_spec G s5 ([q.code.f] ++ [q.code.hBasis.length] ++ [q.dA] ++ [packW q.code.f q.code.hBasis]) 4
    (.v 5) _ (by rw [nW.env 15 (by decide), ← hs4]; simp)
    (by simp; exact ⟨c.slot_le (by omega), hmHs, hdAs, hpB⟩) rfl (by norm_num) n5 hOs hK
  have e : evalS G parseH s = s5.setv 15 (packW (G.K / 16) ([q.code.f] ++ [q.code.hBasis.length] ++ [q.dA] ++
      [packW q.code.f q.code.hBasis] ++ [q.code.hOffset])) := by
    simp only [parseH, evalS_seq]
    rw [hs1, r1, r2, r3, hs5, r4]
  rw [e]
  refine ⟨by simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide), n14, e5], by simp; rfl,
    ?_⟩
  have w1 : Wr bodyW s s4 := by
    rw [← hs4, ← hs3, ← hs2]
    exact (((pW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)
  exact (w1.trans (nW.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-! ## Phase 3: the circuits -/

def parseC : S :=
  .seq pNat (.seq (addRec 5 (.v 5)) (.seq (addRec 6 (.v 14)) (.seq (.set 33 (.v 5))
    (.seq (.loop 32 (.v 33) skipPair) (.seq (addRec 7 (.v 14)) skipCirc)))))

theorem parseC_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) (h14 : s.env 14 = posOf q 4)
    (h15 : s.env 15 = packW (G.K / 16) ((parseRec q).take 5)) :
    (evalS G parseC s).env 14 = posOf q 6 ∧ (evalS G parseC s).env 15 = packW (G.K / 16) ((parseRec q).take 8) ∧
      Wr bodyW s (evalS G parseC s) := by
  have hd := c.bd
  have hc := cap_ge G; have hK := c.K32
  obtain ⟨a5, e6, l5⟩ := c.piece 4 (listWord Instance.pairWord q.code.nbr)
    (by norm_num) rfl
  obtain ⟨a6, e7, l6⟩ := c.piece 5 (listWord gateWord q.code.cons) (by norm_num) rfl
  rw [listWord_eq] at a5 e6 l5
  obtain ⟨a5a, a5b⟩ := At.append a5
  simp only [List.length_append] at e6 l5
  have hcN := length_le_flatten Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x)
  obtain ⟨n5, n14, nW⟩ := pNat_at G s q.code.nbr.length _ _ a5a h14 (by omega) hd
  generalize hs1 : evalS G pNat s = s1 at n5 n14 nW
  have s1_15 : s1.env 15 = packW (G.K / 16) ((parseRec q).take 5) := by rw [nW.env 15 (by decide)]; exact h15
  have r1 := addRec_spec G s1 ((parseRec q).take 5) 5 (.v 5) q.code.cN s1_15 (c.take_lt 5) rfl (by norm_num) n5
    (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs2 : s1.setv 15 (packW (G.K / 16) ((parseRec q).take 5 ++ [q.code.cN])) = s2 at r1
  have hv14 : evalE G s2 (.v 14) = posN q := by
    simp only [evalE, ← hs2, FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide), n14]; rfl
  have r2 := addRec_spec G s2 ((parseRec q).take 5 ++ [q.code.cN]) 6 (.v 14) (posN q) (by rw [← hs2]; simp)
    (by rw [show (parseRec q).take 5 ++ [q.code.cN] = (parseRec q).take 6 from rfl]; exact c.take_lt 6) rfl
    (by norm_num) hv14 (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs3 : s2.setv 15 (packW (G.K / 16) ((parseRec q).take 5 ++ [q.code.cN] ++ [posN q])) = s3 at r2
  set s4 := s3.setv 33 (s3.env 5) with hs4
  have s4_10 : s4.env 10 = s.env 10 := by
    simp only [s4, ← hs3, ← hs2, FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 33 by decide),
      Function.update_of_ne (show (10 : Var) ≠ 15 by decide)]
    exact nW.env 10 (by decide)
  have s4_14 : s4.env 14 = posN q := by
    simp only [s4, ← hs3, ← hs2, FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 33 by decide),
      Function.update_of_ne (show (14 : Var) ≠ 15 by decide), n14]; rfl
  have hlp := curLoop_spec G 32 (.v 33) skipPair pNatW Instance.pairWord q.code.nbr s4 (posN q)
    q.data.length q.code.nbr.length (by
      simp only [evalE, s4, ← hs3, ← hs2, FS.setv_env, Function.update_self,
        Function.update_of_ne (show (5 : Var) ≠ 15 by decide), n5]; have := hd.2; omega) le_rfl
    (by rw [s4_10]; exact a5b) s4_14 (by unfold posN Instance.cN; omega) (by decide) (by decide) (by decide)
    (fun x _ t p' ha ht he => skipPair_spec G t x p' _ ha ht he hd)
  rw [List.take_length] at hlp
  obtain ⟨l14, lW⟩ := hlp
  generalize hs5 : evalS G (.loop 32 (.v 33) skipPair) s4 = s5 at l14 lW
  have s5_14 : s5.env 14 = posOf q 5 := by rw [l14, e6]; unfold posN Instance.cN; ring
  have s5_15 : s5.env 15 = packW (G.K / 16) ((parseRec q).take 5 ++ [q.code.cN] ++ [posN q]) := by
    rw [lW.env 15 (by decide)]; simp [s4, ← hs3]
  have r3 := addRec_spec G s5 ((parseRec q).take 5 ++ [q.code.cN] ++ [posN q]) 7 (.v 14) (posC q) s5_15
    (by rw [show (parseRec q).take 5 ++ [q.code.cN] ++ [posN q] = (parseRec q).take 7 from rfl]; exact c.take_lt 7)
    rfl (by norm_num) (by simp only [evalE, s5_14]; rfl) (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs6 : s5.setv 15 (packW (G.K / 16) ((parseRec q).take 5 ++ [q.code.cN] ++ [posN q] ++ [posC q])) = s6
    at r3
  have s6_10 : s6.env 10 = s.env 10 := by
    rw [← hs6]; simp only [FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 15 by decide)]
    rw [lW.env 10 (by decide)]; exact s4_10
  obtain ⟨k14, kW⟩ := skipCirc_spec G s6 q.code.cons (posOf q 5) _ (by rw [s6_10]; exact a6)
    (by rw [← hs6]; simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide)]; exact s5_14)
    l6 hd
  have e : evalS G parseC s = evalS G skipCirc s6 := by
    simp only [parseC, evalS_seq, evalS_set, evalE]
    rw [hs1, r1, r2, show s3.setv 33 (s3.env 5) = s4 from rfl, hs5, r3]
  rw [e]
  refine ⟨by rw [k14, e7], ?_, ?_⟩
  · rw [kW.env 15 (by decide), ← hs6]; simp; rfl
  · have w1 : Wr bodyW s s4 := by
      simp only [s4, ← hs3, ← hs2]
      exact (((nW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
        (Wr.setv _ (by decide) _)
    exact (((w1.trans (lW.mono (by decide))).trans (by rw [← hs6]; exact Wr.setv _ (by decide) _))).trans
      (kW.mono (by decide))

/-! ## `m = log |x̄|` -/

def logBody : S := .seq (.set 28 (.div (.v 28) (.k 2))) (.set 37 (.add (.v 37) (.k 1)))

/-- `37 := log₂ (27)` by halving (scratch `28`). -/
def logP : S := .seq (.set 28 (.v 27)) (.seq (.set 37 (.k 0)) (.whl (.lt (.k 1) (.v 28)) logBody))

theorem logP_spec (s : FS) (n : ℕ) (h27 : s.env 27 = n) (hN : n ≤ G.N) (hc : n + 2 ≤ G.cap) :
    (evalS G logP s).env 37 = Nat.log 2 n ∧ Wr [28, 37] s (evalS G logP s) := by
  have hc0 : min 0 G.cap = 0 := by omega
  have hc1 : min 1 G.cap = 1 := by omega
  have hc2 : min 2 G.cap = 2 := by omega
  let P : FS → Prop := fun w => w.env 37 + Nat.log 2 (w.env 28) = Nat.log 2 n ∧ w.env 28 ≤ n ∧ Wr [28, 37] s w
  have hw := whl_inv G (c := .lt (.k 1) (.v 28)) (body := logBody) P (fun w => w.env 28)
    ((s.setv 28 n).setv 37 (min 0 G.cap))
    ⟨by simp (config := { decide := true }) [Function.update_apply, hc0],
      by simp (config := { decide := true }) [Function.update_apply],
      (Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)⟩
    (by simp (config := { decide := true }) [Function.update_apply]; exact hN) (by
      rintro w ⟨w37, w28, wW⟩ hcnd
      have hx : 1 < w.env 28 := by
        simp only [evalE, hc1] at hcnd; by_contra h; simp [h] at hcnd
      have hlog := Nat.log_div_base 2 (w.env 28)
      have hpos := Nat.log_pos (b := 2) (by norm_num) (show 2 ≤ w.env 28 by omega)
      have hl := Nat.log_le_self 2 n
      have e1 : min (w.env 37 + 1) G.cap = w.env 37 + 1 := by omega
      have hb : evalS G logBody w = (w.setv 28 (w.env 28 / 2)).setv 37 (w.env 37 + 1) := by
        simp (config := { decide := true }) only [logBody, evalS_seq, evalS_set, evalE, FS.setv_env,
          Function.update_apply, if_true, if_false, hc1, hc2, e1]
      rw [hb]
      have h28 : ((w.setv 28 (w.env 28 / 2)).setv 37 (w.env 37 + 1)).env 28 = w.env 28 / 2 := by
        simp (config := { decide := true }) [Function.update_apply]
      have h37 : ((w.setv 28 (w.env 28 / 2)).setv 37 (w.env 37 + 1)).env 37 = w.env 37 + 1 := by simp
      refine ⟨⟨by rw [h28, h37, hlog]; omega, by rw [h28]; omega,
        (wW.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)⟩, ?_⟩
      show ((w.setv 28 (w.env 28 / 2)).setv 37 (w.env 37 + 1)).env 28 < w.env 28
      rw [h28]; exact Nat.div_lt_self (by omega) (by norm_num))
  obtain ⟨⟨w37, w28, wW⟩, hcnd⟩ := hw
  have e : evalS G logP s = evalS G (.whl (.lt (.k 1) (.v 28)) logBody) ((s.setv 28 n).setv 37 (min 0 G.cap)) := by
    simp only [logP, evalS_seq, evalS_set, evalE, h27]
  rw [e]
  refine ⟨?_, wW⟩
  generalize evalS G (.whl (.lt (.k 1) (.v 28)) logBody) ((s.setv 28 n).setv 37 (min 0 G.cap)) = w at w37 w28 wW hcnd
  have hx : w.env 28 < 2 := by
    simp only [evalE, hc1] at hcnd; by_contra h; rw [if_pos (by omega)] at hcnd; exact one_ne_zero hcnd
  rw [Nat.log_of_lt hx] at w37
  omega

/-! ## Phase 4: skip `I`, read `x̄`, `dB`, the masks -/

def parseT : S :=
  .seq (.set 35 (.v 14)) (.seq skipList (.seq (.set 36 (.v 14)) (.seq pNat (.seq pFrameD
    (.seq (addRec 8 (.v 27)) (.seq (addRec 9 (.v 26)) (.seq logP (.seq (addRec 10 (.v 37))
    (.seq pNat (.seq (addRec 11 (.v 5)) (.seq pNat (.seq (addRec 12 (.v 5)) (addRec 13 (.v 14))))))))))))))

theorem parseT_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) (h14 : s.env 14 = posOf q 6)
    (h15 : s.env 15 = packW (G.K / 16) ((parseRec q).take 8)) :
    (evalS G parseT s).env 15 = packW (G.K / 16) ((parseRec q).take 14) ∧ (evalS G parseT s).env 35 = posOf q 6 ∧
      (evalS G parseT s).env 36 = posOf q 7 ∧ (evalS G parseT s).env 37 = q.mI ∧ Wr bodyW s (evalS G parseT s) := by
  have hd := c.bd
  have hc := cap_ge G; have hK := c.K32
  obtain ⟨a7, e8, l7⟩ := c.piece 6 (listWord natWord q.code.iBasis) (by norm_num) rfl
  obtain ⟨a8, e9, l8⟩ := c.piece 7 (natWord q.code.iOffset) (by norm_num) rfl
  obtain ⟨a9, e10, l9⟩ := c.piece 8 (frame q.xbar) (by norm_num) rfl
  obtain ⟨a10, e11, l10⟩ := c.piece 9 (natWord q.dB) (by norm_num) rfl
  obtain ⟨a11, e12, l11⟩ := c.piece 10 (listWord frame q.masks) (by norm_num) rfl
  rw [listWord_eq] at a11 l11
  obtain ⟨a11a, -⟩ := At.append a11
  simp only [List.length_append] at l11
  -- skip `I`
  set s1 := s.setv 35 (s.env 14) with hs1
  obtain ⟨k14, kW⟩ := skipList_spec G s1 q.code.iBasis (posOf q 6) _ (by simpa [s1] using a7)
    (by simp [s1, h14]) l7 hd
  generalize hs2 : evalS G skipList s1 = s2 at k14 kW
  set s3 := s2.setv 36 (s2.env 14) with hs3
  have s3_10 : s3.env 10 = s.env 10 := by simp [s3]; rw [kW.env 10 (by decide)]; simp [s1]
  obtain ⟨-, j14, jW⟩ := pNat_at G s3 q.code.iOffset (posOf q 7) _ (by rw [s3_10]; exact a8)
    (by simp [s3, k14, e8]) l8 hd
  generalize hs4 : evalS G pNat s3 = s4 at j14 jW
  have s4_10 : s4.env 10 = s.env 10 := by rw [jW.env 10 (by decide)]; exact s3_10
  -- `x̄`
  obtain ⟨f26, f27, f14, fW⟩ := pFrameD_spec G s4 q.xbar (posOf q 8) _ (by rw [s4_10]; exact a9)
    (by rw [j14, e9]) l9 hd
  generalize hs5 : evalS G pFrameD s4 = s5 at f26 f27 f14 fW
  have w5 : Wr bodyW s s5 := by
    refine (((((Wr.setv _ (by decide) _).trans (kW.mono (by decide))).trans (Wr.setv _ (by decide) _)).trans
      (jW.mono (by decide))).trans (fW.mono (by decide)))
  have s5_15 : s5.env 15 = packW (G.K / 16) ((parseRec q).take 8) := by
    rw [fW.env 15 (by decide), jW.env 15 (by decide)]; simp [s3, s1]; rw [kW.env 15 (by decide)]; simp [s1, h15]
  have r1 := addRec_spec G s5 ((parseRec q).take 8) 8 (.v 27) q.xbar.length s5_15 (c.take_lt 8) rfl (by norm_num)
    f27 (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs6 : s5.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length])) = s6 at r1
  have hv26 : evalE G s6 (.v 26) = bitsValue q.xbar := by
    simp only [evalE, ← hs6, FS.setv_env, Function.update_of_ne (show (26 : Var) ≠ 15 by decide), f26]
  have t9 : ∀ a ∈ (parseRec q).take 8 ++ [q.xbar.length], a < 2 ^ (G.K / 16) := c.take_lt 9
  have r2 := addRec_spec G s6 ((parseRec q).take 8 ++ [q.xbar.length]) 9 (.v 26) (bitsValue q.xbar)
    (by rw [← hs6]; simp) t9 rfl (by norm_num) hv26 (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs7 : s6.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar])) = s7
    at r2
  have hx := c.xbar_le
  obtain ⟨g37, gW⟩ := logP_spec G s7 q.xbar.length (by
    rw [← hs7, ← hs6]; simp only [FS.setv_env, Function.update_of_ne (show (27 : Var) ≠ 15 by decide), f27])
    (by have := hd.2; omega) (by have := hd.1; have := Nat.lt_two_pow_self (n := q.data.length); omega)
  generalize hs8 : evalS G logP s7 = s8 at g37 gW
  have hv37 : evalE G s8 (.v 37) = q.mI := g37
  have t10 : ∀ a ∈ (parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar], a < 2 ^ (G.K / 16) := c.take_lt 10
  have r3 := addRec_spec G s8 ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar]) 10 (.v 37) q.mI
    (by rw [gW.env 15 (by decide), ← hs7]; simp) t10 rfl (by norm_num) hv37 (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs9 : s8.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++
    [q.mI])) = s9 at r3
  have w6 : Wr bodyW s s6 := by rw [← hs6]; exact w5.trans (Wr.setv _ (by decide) _)
  have w7 : Wr bodyW s s7 := by rw [← hs7]; exact w6.trans (Wr.setv _ (by decide) _)
  have w8 : Wr bodyW s s8 := w7.trans (gW.mono (by decide))
  have w9 : Wr bodyW s s9 := by rw [← hs9]; exact w8.trans (Wr.setv _ (by decide) _)
  have s9_10 : s9.env 10 = s.env 10 := w9.env 10 (by decide)
  have s9_14 : s9.env 14 = posOf q 9 := by
    rw [← hs9]; simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide)]
    rw [gW.env 14 (by decide), ← hs7, ← hs6]
    simp only [FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide)]
    rw [f14, e10]
  -- `dB`
  obtain ⟨d5, d14, dW⟩ := pNat_at G s9 q.dB (posOf q 9) _ (by rw [s9_10]; exact a10) s9_14 l10 hd
  generalize hs10 : evalS G pNat s9 = s10 at d5 d14 dW
  have t11 : ∀ a ∈ (parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI], a < 2 ^ (G.K / 16) :=
    c.take_lt 11
  have r4 := addRec_spec G s10 ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI]) 11 (.v 5)
    q.dB (by rw [dW.env 15 (by decide), ← hs9]; simp) t11 rfl (by norm_num) d5 (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs11 : s10.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++
    [q.mI] ++ [q.dB])) = s11 at r4
  have s11_10 : s11.env 10 = s.env 10 := by rw [← hs11]; simp; rw [dW.env 10 (by decide)]; exact s9_10
  have s11_14 : s11.env 14 = posOf q 10 := by rw [← hs11]; simp; rw [d14, e11]
  -- the masks
  obtain ⟨m5, m14, mW⟩ := pNat_at G s11 q.masks.length (posOf q 10) _ (by rw [s11_10]; exact a11a) s11_14
    (by omega) hd
  generalize hs12 : evalS G pNat s11 = s12 at m5 m14 mW
  have t12 : ∀ a ∈ (parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI] ++ [q.dB],
      a < 2 ^ (G.K / 16) := c.take_lt 12
  have r5 := addRec_spec G s12 ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI] ++ [q.dB]) 12
    (.v 5) q.masks.length (by rw [mW.env 15 (by decide), ← hs11]; simp) t12 rfl (by norm_num) m5
    (c.rec_lt _ (by simp [parseRec])) hK
  generalize hs13 : s12.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++
    [q.mI] ++ [q.dB] ++ [q.masks.length])) = s13 at r5
  have t13 : ∀ a ∈ (parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI] ++ [q.dB] ++
      [q.masks.length], a < 2 ^ (G.K / 16) := c.take_lt 13
  have hv14 : evalE G s13 (.v 14) = posM q := by
    simp only [evalE, ← hs13, FS.setv_env, Function.update_of_ne (show (14 : Var) ≠ 15 by decide), m14]; rfl
  have r6 := addRec_spec G s13 ((parseRec q).take 8 ++ [q.xbar.length] ++ [bitsValue q.xbar] ++ [q.mI] ++ [q.dB] ++
    [q.masks.length]) 13 (.v 14) (posM q) (by rw [← hs13]; simp) t13 rfl (by norm_num) hv14
    (c.rec_lt _ (by simp [parseRec])) hK
  have e : evalS G parseT s = s13.setv 15 (packW (G.K / 16) ((parseRec q).take 8 ++ [q.xbar.length] ++
      [bitsValue q.xbar] ++ [q.mI] ++ [q.dB] ++ [q.masks.length] ++ [posM q])) := by
    simp only [parseT, evalS_seq, evalS_set, evalE]
    rw [show s.setv 35 (s.env 14) = s1 from rfl, hs2, show s2.setv 36 (s2.env 14) = s3 from rfl, hs4, hs5, r1, r2,
      hs8, r3, hs10, r4, hs12, r5, r6]
  have w13 : Wr bodyW s s13 := by
    rw [← hs13]
    exact (((w9.trans (dW.mono (by decide))).trans (by rw [← hs11]; exact Wr.setv _ (by decide) _)).trans
      (mW.mono (by decide))).trans (Wr.setv _ (by decide) _)
  -- the variables `35`, `36`, `37` after their last write
  have k35 : s2.env 35 = posOf q 6 := by rw [kW.env 35 (by decide)]; simp [s1, h14]
  have j36 : s4.env 36 = posOf q 7 := by rw [jW.env 36 (by decide)]; simp [s3, k14, e8]
  have j35 : s4.env 35 = posOf q 6 := by rw [jW.env 35 (by decide)]; simp [s3, k35]
  have s8_35 : s8.env 35 = posOf q 6 := by
    rw [gW.env 35 (by decide), ← hs7, ← hs6]; simp only [FS.setv_env, Function.update_of_ne (show (35 : Var) ≠ 15 by decide)]
    rw [fW.env 35 (by decide), j35]
  have s8_36 : s8.env 36 = posOf q 7 := by
    rw [gW.env 36 (by decide), ← hs7, ← hs6]; simp only [FS.setv_env, Function.update_of_ne (show (36 : Var) ≠ 15 by decide)]
    rw [fW.env 36 (by decide), j36]
  have fin : ∀ j : Var, j = 35 ∨ j = 36 ∨ j = 37 → s13.env j = s8.env j := by
    intro j hj
    have h15 : j ≠ 15 := by rcases hj with rfl | rfl | rfl <;> decide
    have hn : j ∉ pNatW := by rcases hj with rfl | rfl | rfl <;> decide
    rw [← hs13]; simp only [FS.setv_env, Function.update_of_ne h15]
    rw [mW.env j hn, ← hs11]; simp only [FS.setv_env, Function.update_of_ne h15]
    rw [dW.env j hn, ← hs9]; simp only [FS.setv_env, Function.update_of_ne h15]
  rw [e]
  refine ⟨by simp; rfl, ?_, ?_, ?_, w13.trans (Wr.setv _ (by decide) _)⟩
  · simp only [FS.setv_env, Function.update_of_ne (show (35 : Var) ≠ 15 by decide)]
    rw [fin 35 (by simp), s8_35]
  · simp only [FS.setv_env, Function.update_of_ne (show (36 : Var) ≠ 15 by decide)]
    rw [fin 36 (by simp), s8_36]
  · simp only [FS.setv_env, Function.update_of_ne (show (37 : Var) ≠ 15 by decide)]
    rw [fin 37 (by simp), g37]; rfl

/-! ## Phase 5: the actual input subspace `I` -/

def parseI : S :=
  .seq (.set 14 (.v 35)) (.seq pListW (.seq (addRec 14 (.v 30))
    (.seq (.set 14 (.v 36)) (.seq pNat (addRec 15 (.v 5))))))

theorem parseI_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) (h35 : s.env 35 = posOf q 6)
    (h36 : s.env 36 = posOf q 7) (h37 : s.env 37 = q.mI) (h23 : s.env 23 = q.code.f)
    (h15 : s.env 15 = packW (G.K / 16) ((parseRec q).take 14)) :
    (evalS G parseI s).env 15 = packW (G.K / 16) (parseRec q) ∧ Wr bodyW s (evalS G parseI s) := by
  have hd := c.bd
  have hK := c.K32; have hf := c.f_lt; have hm := c.mI_le
  obtain ⟨a6, -, l6⟩ := c.piece 6 (listWord natWord q.code.iBasis) (by norm_num) rfl
  obtain ⟨a7, -, l7⟩ := c.piece 7 (natWord q.code.iOffset) (by norm_num) rfl
  set s1 := s.setv 14 (s.env 35) with hs1
  obtain ⟨-, p30, -, pW⟩ := pListW_spec G s1 (iBw q) q.code.f (posOf q 6) q.data.length
    (by simpa [s1, iBw] using a6) (by simp [s1, h35]) (by simp [s1, h23]) c.iBw_lt
    (by
      rw [c.iBw_len]
      have := Nat.mul_le_mul (show q.code.f ≤ q.data.length by omega) (show q.mI ≤ q.data.length by omega)
      have := c.K
      omega) l6 hd
  generalize hs2 : evalS G pListW s1 = s2 at p30 pW
  have r1 := addRec_spec G s2 ((parseRec q).take 14) 14 (.v 30) (packW q.code.f (iBw q))
    (by rw [pW.env 15 (by decide)]; simpa [s1] using h15) (c.take_lt 14) rfl
    (by norm_num) p30 (c.rec_lt _ (by simp [parseRec])) hK
  set s3 := s2.setv 15 (packW (G.K / 16) ((parseRec q).take 14 ++ [packW q.code.f (iBw q)])) with hs3
  set s4 := s3.setv 14 (s3.env 36) with hs4
  have w4 : Wr bodyW s s4 := by
    simp only [s4, s3]
    exact (((Wr.setv _ (by decide) _).trans (pW.mono (by decide))).trans
      (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  have s4_14 : s4.env 14 = posOf q 7 := by
    simp only [s4, FS.setv_env, Function.update_self, s3,
      Function.update_of_ne (show (36 : Var) ≠ 15 by decide)]
    rw [pW.env 36 (by decide)]; simp [s1, h36]
  obtain ⟨n5, -, nW⟩ := pNat_at G s4 (iOw q) (posOf q 7) q.data.length
    (by rw [w4.env 10 (by decide)]; exact a7) s4_14 l7 hd
  generalize hs5 : evalS G pNat s4 = s5 at n5 nW
  have r2 := addRec_spec G s5 ((parseRec q).take 14 ++ [packW q.code.f (iBw q)]) 15 (.v 5) (iOw q)
    (by rw [nW.env 15 (by decide)]; simp [s4, s3]) (c.take_lt 15) rfl
    (by norm_num) n5 (c.rec_lt _ (by simp [parseRec])) hK
  have e : evalS G parseI s = s5.setv 15
      (packW (G.K / 16) ((parseRec q).take 14 ++ [packW q.code.f (iBw q)] ++ [iOw q])) := by
    simp only [parseI, evalS_seq, evalS_set, evalE]
    rw [show s.setv 14 (s.env 35) = s1 from rfl, hs2, r1,
      show s3.setv 14 (s3.env 36) = s4 from rfl, hs5, r2]
  rw [e]
  exact ⟨by simp; rfl, (w4.trans (nW.mono (by decide))).trans (Wr.setv _ (by decide) _)⟩

/-! ## The parse -/

/-- The statement reads no input bit. -/
def rdFree : S → Bool
  | .rd _ => false
  | .seq a b => rdFree a && rdFree b
  | .ite _ a b => rdFree a && rdFree b
  | .loop _ _ b => rdFree b
  | .whl _ b => rdFree b
  | _ => true

theorem ip_rdFree : ∀ (p : S) (s : FS), rdFree p = true → (evalS G p s).ip = s.ip
  | .skip, s, _ => rfl
  | .set i e, s, _ => rfl
  | .seq a b, s, h => by
    simp only [rdFree, Bool.and_eq_true] at h
    simp only [evalS_seq]; rw [ip_rdFree b _ h.2, ip_rdFree a _ h.1]
  | .ite c a b, s, h => by
    simp only [rdFree, Bool.and_eq_true] at h
    rw [evalS_ite]; split_ifs
    exacts [ip_rdFree b _ h.2, ip_rdFree a _ h.1]
  | .loop i n b, s, h => by
    simp only [rdFree] at h
    show ((List.range _).foldl _ s).ip = s.ip
    generalize List.range (min (evalE G s n) G.N) = l
    induction l generalizing s with
    | nil => rfl
    | cons j l ih => simp only [List.foldl_cons]; rw [ih, ip_rdFree b _ h]; rfl
  | .whl c b, s, h => by
    simp only [rdFree] at h
    show (whileN _ _ G.N s).ip = s.ip
    generalize G.N = n
    induction n generalizing s with
    | zero => rfl
    | succ n ih =>
      simp only [whileN]; split_ifs
      · rw [ih, ip_rdFree b _ h]
      · rfl
  | .emit e, s, _ => rfl
  | .field f p, s, _ => by simp only [evalS]; split_ifs <;> rfl
  | .rd i, s, h => by simp [rdFree] at h

/-- **The parse of the data word.** -/
def parseP : S := .seq parseHead (.seq parseH (.seq parseC (.seq parseT parseI)))

/-- **The parse** (proof of `thm:short-pcp-ours`): from the data at bit `0` of `D` (variable `10`), the field is
`𝔽₂[X]/(irr)` of degree `f`, `23 = f`, and variable `15` holds the record `parseRec q`; only the variables `parseW`
change, no input is read, nothing is output. -/
theorem parseP_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) :
    (evalS G parseP s).env 15 = packW (G.K / 16) (parseRec q) ∧ (evalS G parseP s).env 23 = q.code.f ∧
      (evalS G parseP s).fl = q.code.f ∧ (evalS G parseP s).fp = q.code.irr ∧
      fieldOk G q.code.f q.code.irr = true ∧
      (∀ j, j ∉ parseW → (evalS G parseP s).env j = s.env j) ∧
      (evalS G parseP s).out = s.out ∧ (evalS G parseP s).bad = s.bad ∧ (evalS G parseP s).ip = s.ip := by
  obtain ⟨h14, h15, h23, hfl, hfp, hfr, hout, hbad⟩ := parseHead_spec G s q c
  generalize hs1 : evalS G parseHead s = s1 at h14 h15 h23 hfl hfp hfr hout hbad
  have c1 : PCtx G q (s1.env 10) := by rw [hfr 10 (by decide)]; exact c
  obtain ⟨k14, k15, kW⟩ := parseH_spec G s1 q c1 h14 (by rw [h15]; rfl) h23
  generalize hs2 : evalS G parseH s1 = s2 at k14 k15 kW
  have c2 : PCtx G q (s2.env 10) := by rw [kW.env 10 (by decide)]; exact c1
  obtain ⟨m14, m15, mW⟩ := parseC_spec G s2 q c2 k14 k15
  generalize hs3 : evalS G parseC s2 = s3 at m14 m15 mW
  have c3 : PCtx G q (s3.env 10) := by rw [mW.env 10 (by decide)]; exact c2
  obtain ⟨t15, t35, t36, t37, tW⟩ := parseT_spec G s3 q c3 m14 m15
  generalize hs4 : evalS G parseT s3 = s4 at t15 t35 t36 t37 tW
  have c4 : PCtx G q (s4.env 10) := by rw [tW.env 10 (by decide)]; exact c3
  have w4 : Wr bodyW s1 s4 := (kW.trans mW).trans tW
  obtain ⟨i15, iW⟩ := parseI_spec G s4 q c4 t35 t36 t37 (by rw [w4.env 23 (by decide)]; exact h23) t15
  have e : evalS G parseP s = evalS G parseI s4 := by simp only [parseP, evalS_seq, hs1, hs2, hs3, hs4]
  have w5 : Wr bodyW s1 (evalS G parseI s4) := w4.trans iW
  rw [e]
  refine ⟨i15, by rw [w5.env 23 (by decide)]; exact h23, by rw [w5.fl]; exact hfl, by rw [w5.fp]; exact hfp,
    c.field_ok, fun j hj => ?_, by rw [w5.out]; exact hout, by rw [w5.bad]; exact hbad, ?_⟩
  · have hb : ∀ x, x ∈ bodyW → x ∈ parseW := by decide
    have hh : ∀ x, x ∈ headW → x ∈ parseW := by decide
    rw [w5.env j (fun h => hj (hb j h)), hfr j (fun h => hj (hh j h))]
  · rw [← e, ip_rdFree G parseP s (by decide)]

/-- The record slots, read with `recE`. -/
theorem recE_parse (s : FS) (q : Request) {D : ℕ} (c : PCtx G q D)
    (h15 : s.env 15 = packW (G.K / 16) (parseRec q)) (i : ℕ) (hi : i < 16) :
    evalE G s (recE i) = (parseRec q).getD i 0 :=
  recE_eval G s (parseRec q) h15 c.rec_lt i hi c.K32

end NearCubicGates.Adapters.ShortPCP.Machines.FL
