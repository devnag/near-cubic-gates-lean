import SourceAdapters.RAMACSP.GenItemsSpec
import SourceAdapters.RAMACSP.GenTGlue
import SourceAdapters.RAMACSP.GenStageA
import SourceAdapters.RAMACSP.GenMain

/-!
# The item printer's stages before the catalog: request, numbers, modulus, coordinate array, layout masks

Paper: `lem:generator`. The ordinary construction first reads the request
and computes its parameters, obtains the field modulus, then emits the
machine catalog with those values.

- `readVar vN vX`: read `s.env vN + 1` bits of the callee's output into `vX` as a number (`readVar_spec`; the
  generic form of `GenGlue.readBits`);
- `stageRI`: read `frame x`, `frame (bits t)` and compute the numbers `20 … 36` (`stageRI_spec`);
- `lenP`: the lengths `natBitLength` of `f`, `irr`, `mH` into `41, 42, 43` and `mH·mH·f − 1` into `38`
  (`lenP_spec`);
- `setupP`: `k + ℓ`, the fixed guard coordinates `2^{mH} − 2^k`, `η_5 ⊕ η_1`, `areaMask ⊕ η_6` into
  `44, 45, 48, 49` (`setupP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMACSP.Gen
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicWires.RepairRepresentation (natWord)

/-! ## Reading the callee's output into a variable -/

/-- Read `s.env vN + 1` bits of the callee output into `g1` (as `bitsValue`), then `vX := g1`. -/
def readVar (vN vX : Var) : St VV MM :=
  .seq (.op (.zero g1)) (.seq (.op (.copy g2 r1)) (.seq (.op (.zero g0)) (.seq (.op (.copy g3 (FL.uv vN)))
    (.seq (.op (.inc g3)) (.seq (.loop (.lt g0 g3) (.seq (.op (.rdK g4)) (.seq (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6)))
      (.seq (.op (.shl g2)) (.op (.inc g0))))))
      (.op (.copy (FL.uv vX) g1)))))))

theorem readVar_spec (vN vX : Var) (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (f : ℕ)
    (hf : s.env vN = f)
    (u : List Bool) (ho : a.kout = u) (hc : a.kc = 0) (hu : u.length = f + 1)
    (hW : 2 ^ (f + 3) < 2 ^ C.Wd) (hcap : 2 ^ (f + 1) ≤ G.cap + 1) :
    Hs C (readVar vN vX) a (10 * f + 40)
      (fun b => Rel G (s.setv vX (CanonicalBinary.bitsValue u)) b ∧ b.kin = a.kin) := by
  have hpw : ∀ j ≤ f + 1, 2 * 2 ^ j < 2 ^ C.Wd := fun j hj => by
    have : 2 ^ (j + 1) ≤ 2 ^ (f + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  have hfW : f + 3 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self (le_of_lt hW)
  have hF : a.env (FL.uv vN) = f := (r.uv vN).trans hf
  refine hs_step (OpEx.zero g1 a) ?_
  refine hs_step (OpEx.copy g2 r1 _ (by decide)) ?_
  refine hs_step (OpEx.zero g0 _) ?_
  refine hs_step (OpEx.copy g3 (FL.uv vN) _ (g_ne_uv vN (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) ?_
  set a4 := (((a.set g1 0).set g2 ((a.set g1 0).env r1)).set g0 0).set g3
    ((((a.set g1 0).set g2 ((a.set g1 0).env r1)).set g0 0).env (FL.uv vN)) with ha4
  have a4g3 : a4.env g3 = f := by
    simp only [a4, DS.set_env_self]
    rw [DS.set_env_ne _ _ (g_ne_uv vN (Or.inl rfl)).symm, DS.set_env_ne _ _ (g_ne_uv vN (Or.inr (Or.inr (Or.inl rfl)))).symm,
      DS.set_env_ne _ _ (g_ne_uv vN (Or.inr (Or.inl rfl))).symm, hF]
  refine hs_step (OpEx.inc g3 a4 (by rw [a4g3]; omega)) ?_
  set a5 := a4.set g3 (a4.env g3 + 1) with ha5
  have r5 : Rel G s a5 := relSetg (relSetg (relSetg (relSetg (relSetg r g1 _)
    g2 _) g0 _) g3 _)
    g3 _
  have e1 : a5.env g1 = 0 := by simp [a5, a4, DS.set_env_ne _ _ (show g1 ≠ g3 by decide),
    DS.set_env_ne _ _ (show g1 ≠ g0 by decide), DS.set_env_ne _ _ (show g1 ≠ g2 by decide)]
  have e2 : a5.env g2 = 1 := by
    simp only [a5, a4, DS.set_env_ne _ _ (show g2 ≠ g3 by decide), DS.set_env_ne _ _ (show g2 ≠ g0 by decide),
      DS.set_env_self, DS.set_env_ne _ _ (show r1 ≠ g1 by decide), r.env.c1]
  have e0 : a5.env g0 = 0 := by simp [a5, a4, DS.set_env_ne _ _ (show g0 ≠ g3 by decide)]
  have e3 : a5.env g3 = f + 1 := by simp [a5, a4g3]
  -- the read loop
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧
    b.env g1 = CanonicalBinary.bitsValue (u.take j) ∧ b.env g2 = 2 ^ j ∧ b.env g3 = f + 1 ∧ b.kc = j ∧ b.kout = u ∧
    b.kin = a.kin
  have hI0 : I 0 a5 := ⟨r5, e0, by simp [e1, CanonicalBinary.bitsValue], by simp [e2], e3, by simp [a5, a4, hc],
    by simp [a5, a4, ho], by simp [a5, a4]⟩
  have hbody : ∀ j < f + 1, ∀ b, I j b → (Cnd.lt g0 g3).eval b = true ∧
      Hs C (.seq (.op (.rdK g4)) (.seq (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6))) (.seq (.op (.shl g2)) (.op (.inc g0)))))
        b 8 (I (j + 1)) := by
    rintro j hj b ⟨rb, b0, b1, b2, b3, bc, bo, bk⟩
    refine ⟨by simp only [Cnd.eval, b0, b3, decide_eq_true_eq]; omega, ?_⟩
    refine hs_step (OpEx.rdK g4 b (by rw [bc, bo, hu]; omega)) ?_
    set c := ({ b.set g4 (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM) with hcdef
    have rc : Rel G s c := relKc rb g4 _ _ (by decide) (by decide)
    have c4 : c.env g4 = (u.getD j false).toNat := by simp [c, bitOf, bo, bc]
    have c1 : c.env g1 = CanonicalBinary.bitsValue (u.take j) := by
      simp [c, DS.set_env_ne _ _ (show g1 ≠ g4 by decide), b1]
    have c2 : c.env g2 = 2 ^ j := by simp [c, DS.set_env_ne _ _ (show g2 ≠ g4 by decide), b2]
    have c0 : c.env g0 = j := by simp [c, DS.set_env_ne _ _ (show g0 ≠ g4 by decide), b0]
    have c3 : c.env g3 = f + 1 := by simp [c, DS.set_env_ne _ _ (show g3 ≠ g4 by decide), b3]
    have hjl : j < u.length := by omega
    have hbt := bitsValue_take_succ u j hjl
    have hbl : CanonicalBinary.bitsValue (u.take j) < 2 ^ j := by
      have := bv_lt (u.take j); simp only [List.length_take] at this; rwa [min_eq_left (by omega)] at this
    -- after the conditional add: `g1 = bitsValue (take (j+1))`
    have hite : Hs C (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6))) c 2 (fun d => Rel G s d ∧ d.env g0 = j ∧
        d.env g1 = CanonicalBinary.bitsValue (u.take (j + 1)) ∧ d.env g2 = 2 ^ j ∧ d.env g3 = f + 1 ∧
        d.kc = j + 1 ∧ d.kout = u ∧ d.kin = a.kin) := by
      refine Hs.ite (show g4 ≠ r1 by decide) (fun he => ?_) (fun he => ?_)
      · have hb1 : (u.getD j false) = true := by
          simp only [Cnd.eval, c4, rc.env.c1, decide_eq_true_eq] at he
          cases h : u.getD j false <;> simp_all
        refine Hs.op (OpEx.add g1 g2 c (by decide) (by rw [c1, c2]; have := hpw j (by omega); omega)) ?_
        refine ⟨relSetg rc g1 _, by simp [DS.set_env_ne _ _ (show g0 ≠ g1 by decide), c0], ?_,
          by simp [DS.set_env_ne _ _ (show g2 ≠ g1 by decide), c2],
          by simp [DS.set_env_ne _ _ (show g3 ≠ g1 by decide), c3], by simp [c, bc], by simp [c, bo], by simp [c, bk]⟩
        simp only [DS.set_env_self, c1, c2, hbt, hb1]; simp
      · have hb0 : (u.getD j false) = false := by
          simp only [Cnd.eval, c4, rc.env.c1, decide_eq_false_iff_not] at he
          cases h : u.getD j false <;> simp_all
        refine Hs.op (OpEx.zero g6 c) ⟨relSetg rc g6 _,
          by simp [DS.set_env_ne _ _ (show g0 ≠ g6 by decide), c0], ?_,
          by simp [DS.set_env_ne _ _ (show g2 ≠ g6 by decide), c2],
          by simp [DS.set_env_ne _ _ (show g3 ≠ g6 by decide), c3], by simp [c, bc], by simp [c, bo], by simp [c, bk]⟩
        simp only [DS.set_env_ne _ _ (show g1 ≠ g6 by decide), c1, hbt, hb0]; simp
    refine Hs.mono (Hs.seq (t2 := 3) hite (fun d ⟨rd, d0, d1, d2, d3, dc, dout, dk⟩ => ?_)) (by omega) (fun _ h => h)
    refine hs_step (OpEx.shl g2 d (by rw [d2]; exact hpw j (by omega))) ?_
    have hjl2 : j < 2 ^ j := Nat.lt_two_pow_self
    refine Hs.op (OpEx.inc g0 _ (by
      rw [DS.set_env_ne _ _ (show g0 ≠ g2 by decide), d0]; have := hpw j (by omega); omega)) ?_
    refine ⟨relSetg (relSetg rd g2 _) g0 _, ?_, ?_, ?_, ?_, by simp [dc],
      by simp [dout], by simp [dk]⟩
    · simp [DS.set_env_ne _ _ (show g0 ≠ g2 by decide), d0]
    · simp [DS.set_env_ne _ _ (show g1 ≠ g0 by decide), DS.set_env_ne _ _ (show g1 ≠ g2 by decide), d1]
    · simp [DS.set_env_ne _ _ (show g2 ≠ g0 by decide), d2, pow_succ]; ring
    · simp [DS.set_env_ne _ _ (show g3 ≠ g0 by decide), DS.set_env_ne _ _ (show g3 ≠ g2 by decide), d3]
  refine Hs.mono (Hs.seq (t2 := 1) (Hs.loopN (c := .lt g0 g3) (show g0 ≠ g3 by decide) I (f + 1) 8 hbody
    (fun b ⟨_, b0, _, _, b3, _⟩ => by simp only [Cnd.eval, b0, b3, decide_eq_false_iff_not]; omega) a5 hI0)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  obtain ⟨rb, b0, b1, b2, b3, bc, bo, bk⟩ := hb
  refine Hs.op (OpEx.copy (FL.uv vX) g1 b (g_ne_uv vX (Or.inr (Or.inl rfl))).symm) ?_
  rw [b1, ← hu, List.take_length]
  have hbu : CanonicalBinary.bitsValue u ≤ G.cap := by have := bv_lt u; rw [hu] at this; omega
  exact ⟨rb.setv vX hbu, by simp [bk]⟩


/-! ## The request and the numbers -/

variable (V : Verifier) {G : Glob}

/-- Read the request and compute the G2 numbers. -/
def stageRI : S := .seq readP (paramsP V)

theorem wf_stageRI : wfS (stageRI V) 0 = true := rfl

theorem stageRI_spec (s : FS) (r : ClockRequest) (rest : List Bool)
    (hin : G.inp.drop s.ip = ClockRequest.word r ++ rest) (hfit : ParamFit V r G) :
    let u := evalS G (stageRI V) s
    PV V r u ∧ u.out = s.out ∧ u.bad = s.bad ∧ u.fl = s.fl ∧ u.fp = s.fp := by
  intro u
  obtain ⟨hK, hKN⟩ := hfit
  obtain ⟨a20, a21, a22, a23, aW⟩ := readP_spec (G := G) s r rest hin (pow_le_cap' (by omega))
    (pow_le_cap' (by omega)) (by omega) (by omega)
  generalize hs1 : evalS G readP s = s1 at a20 a21 a22 a23 aW
  obtain ⟨pv2, w2⟩ := paramsP_spec V (G := G) r s1 a20 a21 a22 a23 ⟨hK, hKN⟩
  have hu : u = evalS G (paramsP V) s1 := by show evalS G (stageRI V) s = _; rw [← hs1]; rfl
  rw [hu]
  exact ⟨pv2, by rw [w2.out, aW.out], by rw [w2.bad, aW.bad], by rw [w2.fl, aW.fl], by rw [w2.fp, aW.fp]⟩

/-! ## The lengths of the coordinate request and the size of the coordinate array -/

/-- `41, 42, 43 :=` the lengths of `f`, `irr`, `mH`; `38 := mH·mH·f − 1`. -/
def lenP : S :=
  .seq (natLenP 36) (.seq (.set 41 (.v 6)) (.seq (natLenP 37) (.seq (.set 42 (.v 6)) (.seq (natLenP 35)
    (.seq (.set 43 (.v 6)) (.set 38 (.sub (.mul (.mul (.v 35) (.v 35)) (.v 36)) (.k 1))))))))

theorem wf_lenP : wfS lenP 0 = true := by decide

/-- The variables `lenP` writes. -/
def LHW : List Var := [5, 6, 38, 41, 42, 43]

theorem lenP_spec (s : FS) (r : ClockRequest) (h : PV V r s) (irr : ℕ) (h37 : s.env 37 = irr)
    (hirr : irr < 2 ^ (fieldExp V r.2 + 1)) (hK : fieldExp V r.2 + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hD : domExp V r.2 * domExp V r.2 * fieldExp V r.2 ≤ G.cap) :
    let u := evalS G lenP s
    PV V r u ∧ u.env 37 = irr ∧ u.env 41 = natBitLength (fieldExp V r.2) ∧ u.env 42 = natBitLength irr ∧
      u.env 43 = natBitLength (domExp V r.2) ∧
      u.env 38 = domExp V r.2 * domExp V r.2 * fieldExp V r.2 - 1 ∧ Em LHW s u [] := by
  intro u
  have hmf := domExp_add_two_le_fieldExp V r.2
  have nf : natBitLength (fieldExp V r.2) + 2 ≤ G.K := by have := natBitLength_le (fieldExp V r.2); omega
  have nm : natBitLength (domExp V r.2) + 2 ≤ G.K := by have := natBitLength_le (domExp V r.2); omega
  have ni : natBitLength irr + 2 ≤ G.K := by
    have := natBitLength_le_of_lt (v := irr) (L := fieldExp V r.2 + 1) (by omega) hirr; omega
  have m6 : ∀ x ∈ ([6] : List Var), x ∈ LHW := by decide
  obtain ⟨l1, e1⟩ := natLenP_spec (G := G) s 36 (by decide) (by rw [h.f]; exact nf) hKN
  generalize hs1 : evalS G (natLenP 36) s = s1 at l1 e1
  have s1e : ∀ i : Var, i ∉ LHW → s1.env i = s.env i := fun i hi => e1.env i (fun h' => hi (m6 i h'))
  set s2 := s1.setv 41 (evalE G s1 (.v 6)) with hs2
  have e2 : Em LHW s1 s2 [] := Em.setv s1 (by decide) _
  have s2_37 : s2.env 37 = irr := by simp [hs2, s1e 37 (by decide), h37]
  obtain ⟨l3, e3⟩ := natLenP_spec (G := G) s2 37 (by decide) (by rw [s2_37]; exact ni) hKN
  generalize hs3 : evalS G (natLenP 37) s2 = s3 at l3 e3
  set s4 := s3.setv 42 (evalE G s3 (.v 6)) with hs4
  have e4 : Em LHW s3 s4 [] := Em.setv s3 (by decide) _
  have s4e : ∀ i : Var, i ∉ LHW → s4.env i = s.env i := fun i hi =>
    (e4.env i hi).trans ((e3.env i (fun h' => hi (m6 i h'))).trans ((e2.env i hi).trans (s1e i hi)))
  obtain ⟨l5, e5⟩ := natLenP_spec (G := G) s4 35 (by decide) (by rw [s4e 35 (by decide), h.mH]; exact nm) hKN
  generalize hs5 : evalS G (natLenP 35) s4 = s5 at l5 e5
  set s6 := s5.setv 43 (evalE G s5 (.v 6)) with hs6
  have e6 : Em LHW s5 s6 [] := Em.setv s5 (by decide) _
  have s6e : ∀ i : Var, i ∉ LHW → s6.env i = s.env i := fun i hi =>
    (e6.env i hi).trans ((e5.env i (fun h' => hi (m6 i h'))).trans (s4e i hi))
  set s7 := s6.setv 38 (evalE G s6 (.sub (.mul (.mul (.v 35) (.v 35)) (.v 36)) (.k 1))) with hs7
  have e7 : Em LHW s6 s7 [] := Em.setv s6 (by decide) _
  have hu : u = s7 := by
    show evalS G lenP s = s7
    rw [hs7, hs6, ← hs5, hs4, ← hs3, hs2, ← hs1]; rfl
  rw [hu]
  have s7e : ∀ i : Var, i ∉ LHW → s7.env i = s.env i := fun i hi => (e7.env i hi).trans (s6e i hi)
  have s7_41 : s7.env 41 = natBitLength (fieldExp V r.2) := by
    rw [hs7, FS.setv_env, Function.update_of_ne (by decide), hs6, FS.setv_env, Function.update_of_ne (by decide),
      e5.env 41 (by decide), hs4, FS.setv_env, Function.update_of_ne (by decide), e3.env 41 (by decide), hs2]
    simp [eE_v, l1, h.f]
  have s7_42 : s7.env 42 = natBitLength irr := by
    rw [hs7, FS.setv_env, Function.update_of_ne (by decide), hs6, FS.setv_env, Function.update_of_ne (by decide),
      e5.env 42 (by decide), hs4]
    simp [eE_v, l3, s2_37]
  have s7_43 : s7.env 43 = natBitLength (domExp V r.2) := by
    rw [hs7, FS.setv_env, Function.update_of_ne (by decide), hs6]
    simp [eE_v, l5, s4e 35 (by decide), h.mH]
  have s7_38 : s7.env 38 = domExp V r.2 * domExp V r.2 * fieldExp V r.2 - 1 := by
    have a35 : s6.env 35 = domExp V r.2 := by rw [s6e 35 (by decide), h.mH]
    have a36 : s6.env 36 = fieldExp V r.2 := by rw [s6e 36 (by decide), h.f]
    have hmm : domExp V r.2 * domExp V r.2 ≤ domExp V r.2 * domExp V r.2 * fieldExp V r.2 :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hc1 : 1 ≤ G.cap := by
      have := cap_add G; have : 8 ≤ G.K := by omega
      have : 2 ^ 8 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) this
      omega
    rw [hs7]
    simp only [FS.setv_env, Function.update_self, evalE, a35, a36]
    rw [min_eq_left (show domExp V r.2 * domExp V r.2 ≤ G.cap by omega), min_eq_left hD, min_eq_left hc1]
  refine ⟨h.keep V (fun i h1 h2 => s7e i (notmem_hi (by decide) h1 h2)),
    by rw [s7e 37 (by decide), h37], s7_41, s7_42, s7_43, s7_38, ?_⟩
  have E := ((e1.mono m6).trans (e2.trans ((e3.mono m6).trans (e4.trans ((e5.mono m6).trans (e6.trans e7))))))
  simpa using E

/-! ## The layout masks -/

theorem upperKnown_add_k (l : Routing.Layout) : upperKnown l + 2 ^ l.k = 2 ^ l.m := by
  unfold upperKnown Routing.cellMask Routing.Layout.m
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ l.ell = b + 1 := ⟨2 ^ l.ell - 1, by have := Nat.one_le_two_pow (n := l.ell); omega⟩
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ l.q = c + 1 := ⟨2 ^ l.q - 1, by have := Nat.one_le_two_pow (n := l.q); omega⟩
  rw [pow_add, pow_add, pow_add, hb, hc, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

theorem eta_eq (l : Routing.Layout) (r : ℕ) : Routing.eta l r = r * 2 ^ (l.k + l.ell + l.q) := by
  unfold Routing.eta Routing.cellMask; rw [pow_add, pow_add]; ring

theorem areaMask_eq (l : Routing.Layout) : Routing.areaMask l = 8 * 2 ^ (l.k + l.ell + l.q) := by
  unfold Routing.areaMask Routing.cellMask; rw [pow_add, pow_add]; ring

/-- `44 := k + ℓ`, `45 := 2^{mH} − 2^k`, `48 := η_5 ⊕ η_1`, `49 := areaMask ⊕ η_6`. -/
def setupP : S :=
  .seq (.set 44 (.add (.v 31) (.v 32))) (.seq (.set 45 (.sub (.shl (.k 1) (.v 35)) (.shl (.k 1) (.v 31))))
    (.seq (.set 48 (.bxor (.shl (.k 5) (.add (.v 44) (.v 34))) (.shl (.k 1) (.add (.v 44) (.v 34)))))
      (.set 49 (.bxor (.shl (.k 8) (.add (.v 44) (.v 34))) (.shl (.k 6) (.add (.v 44) (.v 34)))))))

theorem wf_setupP : wfS setupP 0 = true := by decide

/-- The variables `setupP` writes. -/
def SHW : List Var := [44, 45, 48, 49]

theorem setupP_spec (s : FS) (r : ClockRequest) (h : PV V r s) (hcap : 2 ^ (domExp V r.2 + 8) ≤ G.cap) :
    let u := evalS G setupP s
    u.env 44 = laneExp V r.2 + stageExp V r.2 ∧ u.env 45 = upperKnown (ownLayout V r.2) ∧
      u.env 48 = Routing.eta (ownLayout V r.2) 5 ^^^ Routing.eta (ownLayout V r.2) 1 ∧
      u.env 49 = Routing.areaMask (ownLayout V r.2) ^^^ Routing.eta (ownLayout V r.2) 6 ∧ Em SHW s u [] := by
  intro u
  set l := ownLayout V r.2 with hl
  have hk : s.env 31 = l.k := h.k
  have hell : s.env 32 = l.ell := h.ell
  have hq : s.env 34 = l.q := h.q
  have hm : s.env 35 = l.m := h.mH
  have hmE : l.m = (l.k + l.ell + l.q) + 4 := by unfold Routing.Layout.m; ring
  set E := l.k + l.ell + l.q with hE
  have hcK := cap_add G
  have hpm : 2 ^ l.m ≤ 2 ^ (domExp V r.2 + 8) := Nat.pow_le_pow_right (by norm_num) (by rw [ownLayout_m]; omega)
  have h16 : 2 ^ (E + 4) = 16 * 2 ^ E := by rw [pow_add 2 E 4]; norm_num; ring
  have hE8 : 8 * 2 ^ E ≤ 2 ^ l.m := by rw [hmE, h16]; omega
  have hEK : 2 ^ (E + 3) ≤ 2 ^ G.K := by
    have : 2 ^ (E + 3) ≤ 2 ^ l.m := by rw [hmE]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hkm : 2 ^ l.k ≤ 2 ^ l.m := Nat.pow_le_pow_right (by norm_num) (by unfold Routing.Layout.m; omega)
  have hpos := Nat.two_pow_pos E
  have c1 : min 1 G.cap = 1 := min_eq_left (by omega)
  -- the four values
  set s1 := s.setv 44 (evalE G s (.add (.v 31) (.v 32))) with hs1
  have v44 : evalE G s (.add (.v 31) (.v 32)) = l.k + l.ell := by
    simp only [evalE, hk, hell]; exact min_eq_left (by
      have : l.k + l.ell ≤ E := by omega
      have : E < 2 ^ E := Nat.lt_two_pow_self
      omega)
  set s2 := s1.setv 45 (evalE G s1 (.sub (.shl (.k 1) (.v 35)) (.shl (.k 1) (.v 31)))) with hs2
  have v45 : evalE G s1 (.sub (.shl (.k 1) (.v 35)) (.shl (.k 1) (.v 31))) = 2 ^ l.m - 2 ^ l.k := by
    simp only [evalE, hs1, FS.setv_env, Function.update_of_ne (show (35 : Var) ≠ 44 by decide),
      Function.update_of_ne (show (31 : Var) ≠ 44 by decide), hm, hk, c1, one_mul]
    rw [min_eq_left (by omega), min_eq_left (by omega)]
  have eE1 : ∀ t : FS, t.env 44 = l.k + l.ell → t.env 34 = l.q → evalE G t (.add (.v 44) (.v 34)) = E := by
    intro t h44 h34
    simp only [evalE, h44, h34]; exact min_eq_left (by have : E < 2 ^ E := Nat.lt_two_pow_self; omega)
  have eSh : ∀ (t : FS) (c : ℕ), c ≤ 8 → t.env 44 = l.k + l.ell → t.env 34 = l.q →
      evalE G t (.shl (.k c) (.add (.v 44) (.v 34))) = c * 2 ^ E := by
    intro t c hc h44 h34
    show min (evalE G t (.k c) * 2 ^ evalE G t (.add (.v 44) (.v 34))) G.cap = _
    rw [eE1 t h44 h34, show evalE G t (.k c) = c from min_eq_left (show c ≤ G.cap by omega)]
    exact min_eq_left (by have : c * 2 ^ E ≤ 8 * 2 ^ E := Nat.mul_le_mul_right _ hc; omega)
  have hxor : ∀ a b : ℕ, a ≤ 8 → b ≤ 8 → (a * 2 ^ E ^^^ b * 2 ^ E) < 2 ^ G.K := by
    intro a b ha hb
    have h1 : a * 2 ^ E < 2 ^ (E + 4) := by
      rw [h16]; have : a * 2 ^ E ≤ 8 * 2 ^ E := Nat.mul_le_mul_right _ ha; omega
    have h2 : b * 2 ^ E < 2 ^ (E + 4) := by
      rw [h16]; have : b * 2 ^ E ≤ 8 * 2 ^ E := Nat.mul_le_mul_right _ hb; omega
    have h3 := Nat.xor_lt_two_pow h1 h2
    have : 2 ^ (E + 4) ≤ 2 ^ G.K := by
      have : 2 ^ (E + 4) ≤ 2 ^ l.m := by rw [hmE]
      omega
    omega
  have s2_44 : s2.env 44 = l.k + l.ell := by simp [hs2, hs1, v44]
  have s2_34 : s2.env 34 = l.q := by simp [hs2, hs1, hq]
  set s3 := s2.setv 48 (evalE G s2 (.bxor (.shl (.k 5) (.add (.v 44) (.v 34))) (.shl (.k 1) (.add (.v 44) (.v 34)))))
    with hs3
  have v48 : evalE G s2 (.bxor (.shl (.k 5) (.add (.v 44) (.v 34))) (.shl (.k 1) (.add (.v 44) (.v 34)))) =
      Routing.eta l 5 ^^^ Routing.eta l 1 := by
    show (evalE G s2 (.shl (.k 5) (.add (.v 44) (.v 34))) ^^^ evalE G s2 (.shl (.k 1) (.add (.v 44) (.v 34)))) % 2 ^ G.K = _
    rw [eSh s2 5 (by norm_num) s2_44 s2_34, eSh s2 1 (by norm_num) s2_44 s2_34, Nat.mod_eq_of_lt (hxor 5 1 (by norm_num)
      (by norm_num)), eta_eq, eta_eq]
  have s3_44 : s3.env 44 = l.k + l.ell := by simp [hs3, s2_44]
  have s3_34 : s3.env 34 = l.q := by simp [hs3, s2_34]
  set s4 := s3.setv 49 (evalE G s3 (.bxor (.shl (.k 8) (.add (.v 44) (.v 34))) (.shl (.k 6) (.add (.v 44) (.v 34)))))
    with hs4
  have v49 : evalE G s3 (.bxor (.shl (.k 8) (.add (.v 44) (.v 34))) (.shl (.k 6) (.add (.v 44) (.v 34)))) =
      Routing.areaMask l ^^^ Routing.eta l 6 := by
    show (evalE G s3 (.shl (.k 8) (.add (.v 44) (.v 34))) ^^^ evalE G s3 (.shl (.k 6) (.add (.v 44) (.v 34)))) % 2 ^ G.K = _
    rw [eSh s3 8 le_rfl s3_44 s3_34, eSh s3 6 (by norm_num) s3_44 s3_34, Nat.mod_eq_of_lt (hxor 8 6 le_rfl
      (by norm_num)), areaMask_eq, eta_eq]
  have hu : u = s4 := rfl
  rw [hu]
  have uk : upperKnown l = 2 ^ l.m - 2 ^ l.k := by have := upperKnown_add_k l; omega
  refine ⟨by simp [hs4, hs3, hs2, hs1, v44]; rfl, by simp [hs4, hs3, hs2, v45, uk], by simp [hs4, hs3, v48],
    by simp [hs4, v49], ?_⟩
  exact (Em.setv s (by decide) _).trans ((Em.setv s1 (by decide) _).trans ((Em.setv s2 (by decide) _).trans
    (Em.setv s3 (by decide) _)))

end NearCubicGates.Adapters.RAMACSP.Gen.Items
