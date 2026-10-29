import SourceAdapters.ShortPCP.AssemblyMid

/-!
# Phases B–F of the middle program of P07

Continuation of `AssemblyMid` (proof of `thm:short-pcp-ours`; `app:short-pcp-proof`, "The exact Lean interface"):

* B: print `dfr code`, then `dfr (frame x̄)` (the data word starts with P03's output);
* C: print `dfr (natWord 2^{f−2})`, the H-test degree parameter `d_H`;
* D: call the mask machine on `natWord f ++ natWord n` (P05);
* E: print `dfr (listWord frame S)` from the callee's output;
* F: close the data frame, compute `ℓ` and the fuel, print `frame 1^ℓ` and `frame 1^fuel` (doubly framed).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-! ## Phase B: the code word and `frame x̄` -/

def phaseB : St VV MM := .seq (rewindTo p1R) (.seq (copyTo endR) (.seq (rewindTo p0R) (copyTo p1R)))

namespace Run

variable (R : Run)

/-- After phase B. -/
structure PostB (b : DS VV MM) : Prop where
  cst : Cst b
  n : b.env nR = R.n
  f : b.env fR = R.f
  k : b.env kR = natBitLength R.f
  d : b.env dR = R.cw.length + (frame R.xb).length
  out : b.out = dfr R.cw ++ dfr (frame R.xb)
  kin : b.kin = []
  kc : b.kc = 0

end Run

theorem bound_facts (R : Run) {U : ℕ} (hg : R.Good C U) :
    50 * C.inp.length + 500 ≤ U ∧ 50 * R.data.length ≤ U ∧ 50 * R.ell ≤ U ∧ 50 * R.fuel ≤ U ∧ 50 * R.c0 ≤ U ∧
      50 * R.bL ≤ U ∧ 50 * R.KT ≤ U ∧ 50 * R.eT ≤ U ∧ 50 * C.Lk ≤ U ∧ 50 * C.Bk ≤ U := by
  have hB := hg.hU
  unfold Run.bound at hB
  rw [hg.inp]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem data_length (R : Run) (hf : 2 ≤ R.f) : R.data.length =
    R.cw.length + (frame R.xb).length + (2 * R.f - 1) + (natWord R.S.length).length + (framesWord R.S).length := by
  simp only [Run.data, Run.sWord, List.length_append, natWord_dB_length R.f hf]; omega

theorem phaseB_spec (R : Run) (U : ℕ) (hg : R.Good C U) (a : DS VV MM) (ha : R.PostA a) :
    Hs C phaseB a (4 * (U + 1)) R.PostB := by
  obtain ⟨hiU, hdU, -, -, -, -, -, -, -, -⟩ := bound_facts R hg
  have hW := hg.hW
  have hinp := hg.inp
  have hcw := hg.cw
  have hf := hg.f
  have hlen : C.inp.length = R.P1 + R.cw.length := by
    rw [hinp]; simp [Run.w, Run.P1, Run.P0]; omega
  have hcwl : R.cw.length = (natWord R.f).length + R.rest.length := by
    rw [hcw]; simp
  have hDl := data_length R hf
  have hP1 : R.P1 = R.P0 + (frame R.xb).length := rfl
  -- back to the code word
  refine hs_step (Hs.mono (rewindTo_spec p1R (by decide) a ha.cst ha.ip (by rw [ha.p1, ha.ipv]; omega)) (by
      rw [ha.ipv, ha.p1]; omega) (fun _ h => h)) (fun b1 hb1 => ?_)
  obtain ⟨h11, h12, h13, h14, h15, h16, h17⟩ := hb1
  have hc1 : Cst b1 := Cst.of_fr ha.cst h17 (by decide)
  have g1 : ∀ y, y ≠ ipR → b1.env y = a.env y := fun y hy => h17 y (by simp [hy])
  -- copy the code word
  have he1 : b1.env endR = C.inp.length := by rw [g1 _ (by decide), ha.e, hinp]
  refine hs_step (Hs.mono (copyTo_spec endR (by decide) b1 hc1 (by rw [h11, h12]) (by rw [h11, he1, ha.p1]; omega)
    (by rw [he1]) (by rw [g1 _ (by decide), ha.d, he1, h11, ha.p1]; omega) (by omega)) (by
      rw [he1, h11, ha.p1]; omega) (fun _ h => h)) (fun b2 hb2 => ?_)
  obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩ := hb2
  have hc2 : Cst b2 := Cst.of_fr hc1 h28 (by decide)
  have g2 : ∀ y, y ∉ copyT → b2.env y = b1.env y := h28
  have hcwo : (C.inp.drop b1.ip).take (b1.env endR - b1.ip) = R.cw := by
    rw [h11, ha.p1, he1, hlen, Nat.add_sub_cancel_left, hinp, hP1, ← List.drop_drop, Run.P0, List.drop_left, Run.w,
      List.drop_left, List.take_length]
  -- back to `frame x̄`
  have hp02 : b2.env p0R = R.P0 := by rw [g2 _ (by decide), g1 _ (by decide), ha.p0]
  refine hs_step (Hs.mono (rewindTo_spec p0R (by decide) b2 hc2 (by rw [h21, h22]) (by
      rw [hp02, h21, he1, hlen, hP1]; omega)) (by rw [h21, hp02, he1]; omega) (fun _ h => h)) (fun b3 hb3 => ?_)
  obtain ⟨h31, h32, h33, h34, h35, h36, h37⟩ := hb3
  have hc3 : Cst b3 := Cst.of_fr hc2 h37 (by decide)
  have g3 : ∀ y, y ≠ ipR → b3.env y = b2.env y := fun y hy => h37 y (by simp [hy])
  -- copy `frame x̄`
  have hp13 : b3.env p1R = R.P1 := by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), ha.p1]
  refine hs_one (Hs.mono (copyTo_spec p1R (by decide) b3 hc3 (by rw [h31, h32]) (by rw [h31, hp02, hp13]; omega)
    (by rw [hp13]; omega) (by
      rw [g3 _ (by decide), h23, g1 _ (by decide), ha.d, hp13, h31, hp02, he1, h11, ha.p1, hP1]; omega) (by omega))
    (by rw [hp13, h31, hp02, hP1]; omega) (fun b4 hb4 => ?_))
  obtain ⟨h41, h42, h43, h44, h45, h46, h47, h48⟩ := hb4
  have g4 : ∀ y, y ∉ copyT → b4.env y = b3.env y := h48
  have hxo : (C.inp.drop b3.ip).take (b3.env p1R - b3.ip) = frame R.xb := by
    rw [h31, hp02, hp13, hP1, Nat.add_sub_cancel_left, hinp, Run.P0, List.drop_left, Run.w,
      List.take_left]
  refine ⟨Cst.of_fr hc3 h48 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), ha.n]
  · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), ha.f]
  · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), ha.k]
  · rw [h43, g3 _ (by decide), h23, g1 _ (by decide), ha.d, hp13, h31, hp02, he1, h11, ha.p1, hlen, hP1]; omega
  · rw [h44, hxo, h33, h24, hcwo, h13, ha.out]; simp
  · rw [h45, h34, h25, h14, ha.kin]
  · rw [h47, h36, h27, h16, ha.kc]

/-! ## Phase C: `natWord 2^{f−2}` -/

def phaseC : St VV MM :=
  .seq (.op (.copy sH fR)) (.seq (.op (.sub sH v1)) (.seq (repL [true, true, true, true] sH)
  (.seq (lit [true, true, true, false]) (.seq (.op (.copy sH fR)) (.seq (.op (.sub sH v2))
  (.seq (repL [true, true, true, false] sH) (.seq (lit [true, true, true, true])
  (.seq (.op (.add dR fR)) (.seq (.op (.add dR fR)) (.op (.sub dR v1)))))))))))

namespace Run

variable (R : Run)

/-- After phase C. -/
structure PostC (b : DS VV MM) : Prop where
  cst : Cst b
  n : b.env nR = R.n
  f : b.env fR = R.f
  k : b.env kR = natBitLength R.f
  d : b.env dR = R.cw.length + (frame R.xb).length + (2 * R.f - 1)
  out : b.out = dfr R.cw ++ dfr (frame R.xb) ++ dfr (natWord (2 ^ (R.f - 2)))
  kin : b.kin = []
  kc : b.kc = 0

end Run

theorem phaseC_spec (R : Run) (U : ℕ) (hg : R.Good C U) (a : DS VV MM) (ha : R.PostB a) :
    Hs C phaseC a (11 * (U + 1)) R.PostC := by
  obtain ⟨hiU, hdU, hlU, -, -, -, -, -, -, -⟩ := bound_facts R hg
  have hW := hg.hW
  have hf := hg.f
  have hDl := data_length R hf
  have hfl : R.f ≤ R.ell := by unfold Run.ell; omega
  have hfx := frame_length' R.xb
  have hc := ha.cst
  refine hs_step (Hs.mono (hs_copy C sH fR a (by decide)) (by omega) (fun _ h => h)) (fun b1 hb1 => ?_)
  subst hb1
  refine hs_step (Hs.mono (hs_sub C sH v1 _ (by decide) (by vsimp [ha.f, hc.one]; omega)) (by omega)
    (fun _ h => h)) (fun b2 hb2 => ?_)
  subst hb2
  set b2 := (a.set sH (a.env fR)).set sH ((a.set sH (a.env fR)).env sH - (a.set sH (a.env fR)).env v1) with hb2
  have c2 : Cst b2 := ⟨by rw [hb2]; vsimp [hc.z], by rw [hb2]; vsimp [hc.one], by rw [hb2]; vsimp [hc.two]⟩
  have s2 : b2.env sH = R.f - 1 := by rw [hb2]; vsimp [ha.f, hc.one]
  have g2 : ∀ y, y ≠ sH → b2.env y = a.env y := fun y hy => by rw [hb2]; vsimp [hy]
  refine hs_step (Hs.mono (repL_spec [true, true, true, true] sH (by decide) b2 c2 (by rw [s2]; omega)) (by
      rw [s2]; simp; omega) (fun _ h => h)) (fun b3 hb3 => ?_)
  obtain ⟨h31, h32, h33, h34, h35, h36⟩ := hb3
  have c3 : Cst b3 := Cst.of_fr c2 h36 (by decide)
  refine hs_step (Hs.mono (lit_spec [true, true, true, false] b3 c3.z) (by simp; omega) (fun _ h => h))
    (fun b4 hb4 => ?_)
  subst hb4
  refine hs_step (Hs.mono (hs_copy C sH fR _ (by decide)) (by omega) (fun _ h => h)) (fun b5 hb5 => ?_)
  subst hb5
  have e5f : b3.env fR = R.f := by rw [h36 fR (by decide), g2 fR (by decide), ha.f]
  refine hs_step (Hs.mono (hs_sub C sH v2 _ (by decide) (by vsimp [e5f, c3.two]; omega)) (by omega)
    (fun _ h => h)) (fun b6 hb6 => ?_)
  subst hb6
  set b6 := ({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).set sH
    (({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).env fR) |>.set sH
    ((({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).set sH
    (({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).env fR)).env sH -
    (({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).set sH
    (({ b3 with out := b3.out ++ [true, true, true, false] } : DS VV MM).env fR)).env v2) with hb6
  have c6 : Cst b6 := ⟨by rw [hb6]; vsimp [c3.z], by rw [hb6]; vsimp [c3.one], by rw [hb6]; vsimp [c3.two]⟩
  have s6 : b6.env sH = R.f - 2 := by rw [hb6]; vsimp [e5f, c3.two]
  have g6 : ∀ y, y ≠ sH → b6.env y = b3.env y := fun y hy => by rw [hb6]; vsimp [hy]
  refine hs_step (Hs.mono (repL_spec [true, true, true, false] sH (by decide) b6 c6 (by rw [s6]; omega)) (by
      rw [s6]; simp; omega) (fun _ h => h)) (fun b7 hb7 => ?_)
  obtain ⟨h71, h72, h73, h74, h75, h76⟩ := hb7
  have c7 : Cst b7 := Cst.of_fr c6 h76 (by decide)
  refine hs_step (Hs.mono (lit_spec [true, true, true, true] b7 c7.z) (by simp; omega) (fun _ h => h))
    (fun b8 hb8 => ?_)
  subst hb8
  have g7 : ∀ y, y ≠ sH → y ≠ sD → b7.env y = a.env y := fun y h1 h2 => by
    rw [h76 y (by simp [h2]), g6 y h1, h36 y (by simp [h2]), g2 y h1]
  have d7 : b7.env dR = R.cw.length + (frame R.xb).length := by rw [g7 _ (by decide) (by decide), ha.d]
  have f7 : b7.env fR = R.f := by rw [g7 _ (by decide) (by decide), ha.f]
  refine hs_step (Hs.mono (hs_add C dR fR _ (by decide) (by vsimp [d7, f7]; omega)) (by omega) (fun _ h => h))
    (fun b9 hb9 => ?_)
  subst hb9
  refine hs_step (Hs.mono (hs_add C dR fR _ (by decide) (by vsimp [d7, f7]; omega)) (by omega) (fun _ h => h))
    (fun b10 hb10 => ?_)
  subst hb10
  refine hs_one (Hs.mono (hs_sub C dR v1 _ (by decide) (by vsimp [d7, f7, c7.one]; omega)) (by omega)
    (fun b hb => ?_))
  subst hb
  refine ⟨⟨by vsimp [c7.z], by vsimp [c7.one], by vsimp [c7.two]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · vsimp []; rw [g7 _ (by decide) (by decide), ha.n]
  · vsimp [f7]
  · vsimp []; rw [g7 _ (by decide) (by decide), ha.k]
  · vsimp [d7, f7, c7.one]; omega
  · simp only [DS.set_out]
    rw [h71, s6, hb6]; simp only [DS.set_out]
    rw [h31, s2, hb2]; simp only [DS.set_out]
    rw [ha.out, dfr_dB R.f hf]; simp [List.append_assoc]
  · simp only [DS.set_kin]; rw [h73, hb6]; simp [h33, hb2, ha.kin]
  · simp only [DS.set_kc]; rw [h75, hb6]; simp [h35, hb2, ha.kc]


/-! ## Phase D: the call of the mask machine -/

def phaseD : St VV MM :=
  .seq (.op (.copy t3 fR)) (.seq emitNatK (.seq (.op (.copy t3 nR)) (.seq emitNatK (.op .kcall))))

namespace Run

variable (R : Run)

/-- After phase D. -/
structure PostD (b : DS VV MM) : Prop where
  cst : Cst b
  f : b.env fR = R.f
  k : b.env kR = natBitLength R.f
  d : b.env dR = R.cw.length + (frame R.xb).length + (2 * R.f - 1)
  out : b.out = dfr R.cw ++ dfr (frame R.xb) ++ dfr (natWord (2 ^ (R.f - 2)))
  kout : b.kout = R.sWord
  kc : b.kc = 0

end Run

theorem phaseD_spec (R : Run) (U : ℕ) (hg : R.Good C U) (a : DS VV MM) (ha : R.PostC a) :
    Hs C phaseD a (5 * (U + 1)) R.PostD := by
  obtain ⟨hiU, hdU, hlU, -, -, -, -, -, hLk, hBk⟩ := bound_facts R hg
  have hW := hg.hW
  have hf := hg.f
  have hfl : R.f ≤ R.ell := by unfold Run.ell; omega
  have hc := ha.cst
  have h1U : 1 ≤ U := by omega
  have hW2 : 2 ≤ C.Wd := by have := nbl_add_two (v := 0) (Nat.zero_le U) h1U hW; omega
  have hnI : R.n ≤ C.inp.length := by
    have := lastTrue_le R.xb 0 0; rw [hg.n] at this
    have h1 : (frame R.xb).length ≤ C.inp.length := by rw [hg.inp]; simp [Run.w]; omega
    have := frame_length' R.xb; omega
  have hnU : R.n ≤ U := by omega
  have hlk := hg.lk
  have hvf : natBitLength R.f + 2 < 2 ^ C.Wd := by
    have := nbl_add_two (v := R.f) (by omega) h1U hW; have := Nat.lt_two_pow_self (n := C.Wd); omega
  have hvn : natBitLength R.n + 2 < 2 ^ C.Wd := by
    have := nbl_add_two (v := R.n) hnU h1U hW; have := Nat.lt_two_pow_self (n := C.Wd); omega
  have e1 : (a.set t3 (a.env fR)).env t3 = R.f := by vsimp [ha.f]
  have e1k : (a.set t3 (a.env fR)).kin = [] := by simp [ha.kin]
  refine hs_step (Hs.mono (hs_copy C t3 fR a (by decide)) (by omega) (fun _ h => h)) (fun b1 hb1 => ?_)
  subst hb1
  refine hs_step (Hs.mono (emitNatK_spec _ (Cst.of_fr hc (T := [t3]) (Fr.set a _ (by simp)) (by decide)) hW2
    (by rw [e1]; exact hvf) (by rw [e1, e1k]; have := natWord_length R.f; have := natWord_length R.n; simp; omega)) (by rw [e1]; have := nbl_le' R.f; omega) (fun _ h => h))
    (fun b2 hb2 => ?_)
  obtain ⟨h21, h22, hc2, h24⟩ := hb2
  simp only [Prod.mk.injEq] at h22
  have g2 : ∀ y, y ∉ emitNatT → y ≠ t3 → b2.env y = a.env y := fun y h1 h2 => by rw [h24 y h1]; vsimp [h2]
  refine hs_step (Hs.mono (hs_copy C t3 nR b2 (by decide)) (by omega) (fun _ h => h)) (fun b3 hb3 => ?_)
  subst hb3
  have hn2 : b2.env nR = R.n := by rw [g2 _ (by decide) (by decide), ha.n]
  have e3 : (b2.set t3 (b2.env nR)).env t3 = R.n := by vsimp [hn2]
  have e3k : (b2.set t3 (b2.env nR)).kin = natWord R.f := by simp only [DS.set_kin]; rw [h21, e1, e1k]; rfl
  refine hs_step (Hs.mono (emitNatK_spec _ (Cst.of_fr hc2 (T := [t3]) (Fr.set b2 _ (by simp)) (by decide)) hW2
    (by rw [e3]; exact hvn) (by rw [e3, e3k]; have := natWord_length R.f; have := natWord_length R.n; omega)) (by rw [e3]; have := nbl_le' R.n; omega) (fun _ h => h))
    (fun b4 hb4 => ?_)
  obtain ⟨h41, h42, hc4, h44⟩ := hb4
  simp only [Prod.mk.injEq] at h42
  obtain ⟨s, hs1, hs2, hs3⟩ := hg.call
  have hkin4 : b4.kin = C.K.inw s := by rw [h41, hs1, e3, e3k]
  refine hs_one (Hs.mono (Hs.op (OpEx.kcall s b4 hkin4 hs3) (R := fun x => x = b4.called (C.K.outw s)) rfl)
    (by omega) (fun b hb => ?_))
  subst hb
  have g4 : ∀ y, y ∉ emitNatT → y ≠ t3 → b4.env y = a.env y := fun y h1 h2 => by
    rw [h44 y h1]; vsimp [h2]; exact g2 y h1 h2
  refine ⟨⟨hc4.z, hc4.one, hc4.two⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show b4.env fR = R.f; rw [g4 _ (by decide) (by decide), ha.f]
  · show b4.env kR = _; rw [g4 _ (by decide) (by decide), ha.k]
  · show b4.env dR = _; rw [g4 _ (by decide) (by decide), ha.d]
  · show b4.out = _; rw [h42.2.1]; simp only [DS.set_out]; rw [h22.2.1]; simp only [DS.set_out]; exact ha.out
  · show C.K.outw s = _; exact hs2
  · rfl

/-! ## Phase E: copying `listWord frame S` -/

def phaseE : St VV MM := .seq copyNatK copyFrames

namespace Run

variable (R : Run)

/-- After phase E. -/
structure PostE (b : DS VV MM) : Prop where
  cst : Cst b
  f : b.env fR = R.f
  k : b.env kR = natBitLength R.f
  d : b.env dR = R.data.length
  out : b.out = dfr R.data

end Run

theorem framesWord_length_ge (L : List (List Bool)) : L.length ≤ (framesWord L).length := by
  induction L with
  | nil => simp
  | cons u L ih => simp only [framesWord_cons, List.length_append, List.length_cons, frame_length']; omega

theorem phaseE_spec (R : Run) (U : ℕ) (hg : R.Good C U) (a : DS VV MM) (ha : R.PostD a) :
    Hs C phaseE a (2 * (U + 1)) R.PostE := by
  obtain ⟨hiU, hdU, -, -, -, -, -, -, -, -⟩ := bound_facts R hg
  have hW := hg.hW
  have hf := hg.f
  have hDl := data_length R hf
  have hc := ha.cst
  have h1U : 1 ≤ U := by omega
  have hSl := framesWord_length_ge R.S
  have hko : a.kout.drop a.kc = natWord R.S.length ++ framesWord R.S := by rw [ha.kout, ha.kc]; rfl
  refine hs_step (Hs.mono (copyNatK_spec a hc R.S.length _ hko (nbl_add_two (by omega) h1U hW)
    (by rw [ha.d]; omega)) (by have := nbl_le' R.S.length; omega) (fun _ h => h)) (fun b1 hb1 => ?_)
  obtain ⟨h11, h12, h13, h14, h15, h16, h17, h18⟩ := hb1
  have hc1 : Cst b1 := Cst.of_fr hc h18 (by decide)
  have hk1 : b1.kout.drop b1.kc = framesWord R.S ++ [] := by
    rw [h17, h12, ← List.drop_drop, hko, List.drop_left, List.append_nil]
  refine hs_one (Hs.mono (copyFrames_spec b1 hc1 R.S [] hk1 h11 (by rw [h14, ha.d]; omega) (by omega)) (by omega)
    (fun b hb => ?_))
  obtain ⟨h21, h22, h23, h24, h25, h26, h27⟩ := hb
  refine ⟨Cst.of_fr hc1 h27 (by decide), ?_, ?_, ?_, ?_⟩
  · rw [h27 _ (by decide), h18 _ (by decide), ha.f]
  · rw [h27 _ (by decide), h18 _ (by decide), ha.k]
  · rw [h23, h14, ha.d, hDl]
  · rw [h22, h13, ha.out]; simp [Run.data, Run.sWord, List.append_assoc]


end NearCubicGates.Adapters.ShortPCP.Assembly
