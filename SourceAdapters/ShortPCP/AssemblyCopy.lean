import SourceAdapters.ShortPCP.AssemblyParse

/-!
# Copying the callee's output (the multiset `S`) into the data word

proof of `thm:short-pcp-ours` (P05: the multiset `S` of `2^{2m}` masks) and proof of `thm:short-pcp-ours` (Step 4: the compilation request carries
`S` in its data word). The callee of the middle program is the mask machine (`MaskMachine`), whose output is
`listWord frame S = natWord |S| ++ frame σ_1 ++ ⋯`. The routines below copy it to the output, doubly framed and
counted, reading the callee's output once:

* `copyNatK`: one `natWord`, keeping its value in `sE`;
* `copyFrameK`: one framed word; `copyFrames`: `sE` framed words.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

theorem kbit {l u rest : List Bool} {p : ℕ} (h : l.drop p = u ++ rest) (j : ℕ) (hj : j < u.length) :
    decide (bitOf l (p + j) = 1) = u.getD j false := by
  rw [decide_bitOf, getD_of_drop h j hj]

theorem kbit' {l u rest : List Bool} {p : ℕ} (h : l.drop p = u ++ rest) (j : ℕ) (hj : j < u.length) :
    bitOf l (p + j) = (u.getD j false).toNat := bitOf_drop h j hj

theorem klen {l u rest : List Bool} {p : ℕ} (h : l.drop p = u ++ rest) (hu : 0 < u.length) :
    p + u.length ≤ l.length := by
  have := congrArg List.length h; simp only [List.length_drop, List.length_append] at this; omega

/-! ## One framed word -/

/-- Copy one framed word from the callee's output. -/
def copyFrameK : St VV MM :=
  .seq (.op (.rdK sA)) (.seq (emitD sA) (.loop (.eq sA v1) (.seq (.op (.rdK sB)) (.seq (emitD sB)
    (.seq (.op (.rdK sA)) (emitD sA))))))

/-- The registers `copyFrameK` may change. -/
def copyKT : List (Fin VV) := [sA, sB, dR]

theorem copyFrameK_spec (a : DS VV MM) (hc : Cst a) (u rest : List Bool) (hko : a.kout.drop a.kc = frame u ++ rest)
    (hW : a.env dR + (frame u).length < 2 ^ C.Wd) :
    Hs C copyFrameK a (u.length * (29 + 2) + 17) (fun b => b.kc = a.kc + (frame u).length ∧
      b.out = a.out ++ dfr (frame u) ∧ b.env dR = a.env dR + (frame u).length ∧ b.ip = a.ip ∧ b.kin = a.kin ∧
      b.kout = a.kout ∧ Fr a b copyKT) := by
  have hfl := frame_length' u
  have hlen := klen hko (by omega)
  let I : ℕ → DS VV MM → Prop := fun k b => b.kc = a.kc + 2 * k + 1 ∧ b.env sA = (decide (k < u.length)).toNat ∧
    b.out = a.out ++ dfr ((frame u).take (2 * k + 1)) ∧ b.env dR = a.env dR + 2 * k + 1 ∧ b.ip = a.ip ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ Fr a b copyKT
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq sA v1) (.seq (.op (.rdK sB)) (.seq (emitD sB)
      (.seq (.op (.rdK sA)) (emitD sA))))) b (u.length * (29 + 2) + 2) (I u.length) := by
    refine Hs.loopN (c := .eq sA v1) (show sA ≠ v1 by decide) I u.length 29 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      have hb1 : b.env v1 = 1 := by rw [h8 v1 (by decide)]; exact hc.one
      have hcb : Cst b := Cst.of_fr hc h8 (by decide)
      refine ⟨by simp [Cnd.eval, h2, hb1, hk], ?_⟩
      have hk' : b.kout.drop a.kc = frame u ++ rest := by rw [h7]; exact hko
      refine Hs.seq (t1 := 1) (t2 := 27) (hs_rdK C sB b (by rw [h1, h7]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 12) (t2 := 14) (emitD_spec sB (by decide) _ (Cst.of_fr hcb (T := [sB])
        (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; vsimp [hy]) (by decide))
        (by vsimp [h4]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 12) (hs_rdK C sA _ (by simp [dState, h1, h7]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (emitD_spec sA (by decide) _ (Cst.of_fr hcb (T := [sA, sB, dR])
        (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
                        vsimp [dState, hy.1, hy.2.1, hy.2.2]) (by decide))
        (by vsimp [dState, h4]; omega)) le_rfl ?_
      rintro g rfl
      have e1 : decide (bitOf b.kout b.kc = 1) = (frame u).getD (2 * k + 1) false := by
        rw [h1, show a.kc + 2 * k + 1 = a.kc + (2 * k + 1) by ring, kbit hk' _ (by omega)]
      have e2 : decide (bitOf b.kout (b.kc + 1) = 1) = (frame u).getD (2 * k + 2) false := by
        rw [h1, show a.kc + 2 * k + 1 + 1 = a.kc + (2 * k + 2) by ring, kbit hk' _ (by omega)]
      have e3 : bitOf b.kout (b.kc + 1) = (decide (k + 1 < u.length)).toNat := by
        rw [h1, show a.kc + 2 * k + 1 + 1 = a.kc + 2 * (k + 1) by ring, kbit' hk' _ (by omega),
          frame_even u (k + 1) (by omega)]
      refine ⟨by simp [dState, h1]; ring, by vsimp [dState, e3], ?_, by vsimp [dState, h4]; ring,
        by simp [dState, h5], by simp [dState, h6], by simp [dState, h7], ?_⟩
      · simp only [dState]
        vsimp []
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, take_succ _ _ (by omega), take_succ _ _ (by omega), h3]
        rw [e1, e2]
        simp [List.append_assoc]
      · intro y hy
        simp only [copyKT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        vsimp [dState, hy.1, hy.2.1, hy.2.2]
        exact h8 y (by simp [copyKT, hy.1, hy.2.1, hy.2.2])
    · intro b hb
      obtain ⟨-, h2, -, -, -, -, -, h8⟩ := hb
      have hb1 : b.env v1 = 1 := by rw [h8 v1 (by decide)]; exact hc.one
      simp [Cnd.eval, h2, hb1]
  have e0 : bitOf a.kout a.kc = (decide (0 < u.length)).toNat := by
    have := kbit' hko 0 (by omega); rw [Nat.add_zero] at this
    rw [this, show (0 : ℕ) = 2 * 0 by rfl, frame_even u 0 (by omega)]
  have e0' : decide (bitOf a.kout a.kc = 1) = (frame u).getD 0 false := by
    have := kbit hko 0 (by omega); rwa [Nat.add_zero] at this
  refine Hs.mono (t := 1 + (12 + (u.length * (29 + 2) + 2) + 1) + 1)
    (Hs.seq (hs_rdK C sA a (by omega)) (fun d hd => ?_)) (by omega) (fun _ h => h)
  subst hd
  refine Hs.seq (emitD_spec sA (by decide) _ (Cst.of_fr hc (T := [sA])
    (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; vsimp [hy]) (by decide))
    (by vsimp []; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hloop _ ⟨by simp [dState], by vsimp [dState, e0], ?_, by vsimp [dState], rfl, rfl, rfl, ?_⟩) le_rfl ?_
  · simp only [dState]; vsimp [e0']
    cases u <;> simp [frame, dfr]
  · intro y hy
    simp only [copyKT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    vsimp [dState, hy.1, hy.2.1, hy.2.2]
  · rintro b ⟨h1, -, h3, h4, h5, h6, h7, h8⟩
    refine ⟨by rw [h1, hfl]; ring, by rw [h3, show 2 * u.length + 1 = (frame u).length by omega,
      List.take_length], by rw [h4, hfl]; ring, h5, h6, h7, h8⟩

/-! ## A list of framed words -/

/-- The words of a list, each framed. -/
def framesWord (L : List (List Bool)) : List Bool := (L.map frame).flatten

@[simp] theorem framesWord_nil : framesWord [] = [] := rfl
@[simp] theorem framesWord_cons (u : List Bool) (L : List (List Bool)) :
    framesWord (u :: L) = frame u ++ framesWord L := rfl

/-- Copy `sE` framed words from the callee's output. -/
def copyFrames : St VV MM := .seq (.op (.zero sG)) (.loop (.lt sG sE) (.seq copyFrameK (.op (.inc sG))))

/-- The registers `copyFrames` may change. -/
def copyFT : List (Fin VV) := [sA, sB, dR, sG]

theorem copyFrames_loop (L : List (List Bool)) : ∀ (b : DS VV MM) (rest : List Bool), Cst b →
    b.env sE = b.env sG + L.length → b.kout.drop b.kc = framesWord L ++ rest →
    b.env dR + (framesWord L).length < 2 ^ C.Wd → b.env sE < 2 ^ C.Wd →
    Hs C (.loop (.lt sG sE) (.seq copyFrameK (.op (.inc sG)))) b (40 * (framesWord L).length + 2) (fun d =>
      d.kc = b.kc + (framesWord L).length ∧ d.out = b.out ++ dfr (framesWord L) ∧
      d.env dR = b.env dR + (framesWord L).length ∧ d.ip = b.ip ∧ d.kin = b.kin ∧ d.kout = b.kout ∧
      Fr b d copyFT) := by
  induction L with
  | nil =>
    intro b rest _ hE _ _ _
    exact Hs.mono (hs_loopF (show sG ≠ sE by decide) (by simp [Cnd.eval, hE]) ⟨by simp, by simp, by simp, rfl, rfl,
      rfl, Fr.refl _ _⟩) (by simp) (fun _ h => h)
  | cons u L ih =>
    intro b rest hc hE hk hW hWE
    have hk1 : b.kout.drop b.kc = frame u ++ (framesWord L ++ rest) := by rw [hk]; simp [List.append_assoc]
    have hfl := frame_length' u
    have hlen : (framesWord (u :: L)).length = (frame u).length + (framesWord L).length := by simp
    refine Hs.mono (hs_loopT (t := (u.length * (29 + 2) + 17) + 1 + 1) (t' := 40 * (framesWord L).length + 2)
      (show sG ≠ sE by decide) (by simp [Cnd.eval, hE]) ?_) (by rw [hlen, hfl]; nlinarith) (fun _ h => h)
    refine Hs.seq (t1 := u.length * (29 + 2) + 17) (t2 := 1)
      (copyFrameK_spec (C := C) b hc u (framesWord L ++ rest) hk1 (by rw [hlen] at hW; omega))
      (fun d hd => ?_)
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hd
    have dG : d.env sG = b.env sG := d7 sG (by decide)
    have dE : d.env sE = b.env sE := d7 sE (by decide)
    have hl1 : (u :: L).length = L.length + 1 := rfl
    refine Hs.mono (hs_inc C sG d (by rw [dG]; omega)) le_rfl ?_
    rintro e rfl
    have hce : Cst (d.set sG (d.env sG + 1)) := Cst.of_fr hc (T := copyFT) (fun y hy => by
      by_cases h : y = sG
      · subst h; simp [copyFT] at hy
      · vsimp [h]; exact d7 y (fun h' => hy (by simp only [copyKT, copyFT, List.mem_cons] at h' ⊢; tauto)))
      (by decide)
    refine Hs.mono (ih (d.set sG (d.env sG + 1)) rest hce (by vsimp [dE, dG, hE]; ring)
      (by show d.kout.drop d.kc = _; rw [d6, d1, ← List.drop_drop, hk1, List.drop_left])
      (by vsimp [d3]; rw [hlen] at hW; omega) (by vsimp [dE]; omega)) le_rfl ?_
    rintro g ⟨g1, g2, g3, g4, g5, g6, g7⟩
    refine ⟨by rw [g1, hlen]; simp [d1]; ring, by rw [g2]; simp [d2, List.append_assoc], ?_, by rw [g4]; simp [d4],
      by rw [g5]; simp [d5], by rw [g6]; simp [d6], ?_⟩
    · rw [g3, hlen]; vsimp [d3]; ring
    · intro y hy
      rw [g7 y hy]
      have hyG : y ≠ sG := fun h => hy (by simp [copyFT, h])
      vsimp [hyG]
      exact d7 y (fun h => hy (by simp only [copyKT, copyFT, List.mem_cons] at h ⊢; tauto))

theorem copyFrames_spec (a : DS VV MM) (hc : Cst a) (L : List (List Bool)) (rest : List Bool)
    (hk : a.kout.drop a.kc = framesWord L ++ rest) (hE : a.env sE = L.length)
    (hW : a.env dR + (framesWord L).length < 2 ^ C.Wd) (hWE : L.length < 2 ^ C.Wd) :
    Hs C copyFrames a (40 * (framesWord L).length + 4) (fun d =>
      d.kc = a.kc + (framesWord L).length ∧ d.out = a.out ++ dfr (framesWord L) ∧
      d.env dR = a.env dR + (framesWord L).length ∧ d.ip = a.ip ∧ d.kin = a.kin ∧ d.kout = a.kout ∧
      Fr a d copyFT) := by
  refine Hs.mono (t := 1 + (40 * (framesWord L).length + 2) + 1) (Hs.seq (hs_zero C sG a) (fun d hd => ?_)) (by omega)
    (fun _ h => h)
  subst hd
  refine Hs.mono (copyFrames_loop L (a.set sG 0) rest (Cst.of_fr (T := copyFT) hc
    (Fr.set a (x := sG) 0 (by simp [copyFT])) (by decide)) (by vsimp [hE]) (by simpa using hk) (by vsimp []; omega) (by vsimp [hE]; omega)) le_rfl ?_
  rintro g ⟨g1, g2, g3, g4, g5, g6, g7⟩
  refine ⟨by simpa using g1, by simpa using g2, by vsimp [g3], by simpa using g4, by simpa using g5, by simpa using g6,
    Fr.trans (Fr.set a (x := sG) 0 (by simp [copyFT])) g7⟩

/-! ## One number -/

/-- Copy one `natWord` from the callee's output; `sE :=` its value. -/
def copyNatK : St VV MM :=
  .seq (.op (.zero sC)) (.seq (.op (.rdK sA)) (.seq (emitD sA)
    (.seq (.loop (.eq sA v1) (.seq (.op (.inc sC)) (.seq (.op (.rdK sA)) (emitD sA))))
    (.seq (.op (.zero sE)) (.seq (.op (.copy sF v1)) (.seq (.op (.zero sD))
      (.loop (.lt sD sC) (.seq (.op (.rdK sB)) (.seq (emitD sB) (.seq (.ite (.eq sB v1) (.op (.add sE sF)) skipS)
        (.seq (.op (.shl sF)) (.op (.inc sD)))))))))))))

/-- The registers `copyNatK` may change. -/
def copyNT : List (Fin VV) := [sA, sB, sC, sD, sE, sF, dR, vJ]

theorem copyNatK_spec (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hko : a.kout.drop a.kc = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd)
    (hW2 : a.env dR + (natWord v).length < 2 ^ C.Wd) :
    Hs C copyNatK a (natBitLength v * 41 + 28) (fun b => b.env sE = v ∧ b.kc = a.kc + (natWord v).length ∧
      b.out = a.out ++ dfr (natWord v) ∧ b.env dR = a.env dR + (natWord v).length ∧ b.ip = a.ip ∧ b.kin = a.kin ∧
      b.kout = a.kout ∧ Fr a b copyNT) := by
  set ℓ := natBitLength v with hℓ
  have hnw : (natWord v).length = 2 * ℓ + 1 := natWord_length v
  have hlen := klen hko (by omega)
  have hpw : 2 ^ (ℓ + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvl : v < 2 ^ ℓ := lt_natBitLength v
  have hℓW : ℓ + 1 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self hpw
  have frT : ∀ y, y ∉ copyNT → y ≠ sA ∧ y ≠ sB ∧ y ≠ sC ∧ y ≠ sD ∧ y ≠ sE ∧ y ≠ sF ∧ y ≠ dR ∧ y ≠ vJ := by
    intro y hy
    simp only [copyNT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact hy
  -- phase 1: the leading ones
  let I1 : ℕ → DS VV MM → Prop := fun k b => b.env sC = k ∧ b.env sA = bitOf a.kout (a.kc + k) ∧
    b.kc = a.kc + k + 1 ∧ b.out = a.out ++ dfr ((natWord v).take (k + 1)) ∧ b.env dR = a.env dR + k + 1 ∧
    b.ip = a.ip ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ Fr a b copyNT
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.eq sA v1) (.seq (.op (.inc sC)) (.seq (.op (.rdK sA)) (emitD sA)))) b
      (ℓ * (16 + 2) + 2) (I1 ℓ) := by
    refine Hs.loopN (c := .eq sA v1) (show sA ≠ v1 by decide) I1 ℓ 16 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      have hb1 : b.env v1 = 1 := by rw [h9 v1 (by decide)]; exact hc.one
      have hcb : Cst b := Cst.of_fr hc h9 (by decide)
      refine ⟨?_, ?_⟩
      · simp only [Cnd.eval, h2, hb1, decide_eq_true_eq]
        rw [kbit' hko k (by omega), natWord_one v k hk]; rfl
      refine Hs.seq (t1 := 1) (t2 := 14) (hs_inc C sC b (by rw [h1]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 12) (hs_rdK C sA _ (by simp [h3, h8]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (emitD_spec sA (by decide) _ (Cst.of_fr hcb (T := [sA, sC])
        (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; vsimp [hy.1, hy.2])
        (by decide)) (by vsimp [h5]; omega)) le_rfl ?_
      rintro g rfl
      have e1 : decide (bitOf b.kout b.kc = 1) = (natWord v).getD (k + 1) false := by
        rw [h3, h8, show a.kc + k + 1 = a.kc + (k + 1) by ring, kbit hko _ (by omega)]
      refine ⟨by vsimp [dState, h1], by vsimp [dState, h3, h8]; ring_nf, by dsimp only [dState, DS.set]; omega, ?_,
        by vsimp [dState, h5]; ring, by simp [dState, h6], by simp [dState, h7], by simp [dState, h8], ?_⟩
      · simp only [dState]
        vsimp []
        rw [take_succ _ (k + 1) (by omega), h4, e1]
        simp [List.append_assoc]
      · intro y hy
        obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := frT y hy
        vsimp [dState, y1, y3, y7]
        exact h9 y hy
    · intro b hb
      obtain ⟨-, h2, -, -, -, -, -, -, h9⟩ := hb
      have hb1 : b.env v1 = 1 := by rw [h9 v1 (by decide)]; exact hc.one
      simp only [Cnd.eval, h2, hb1, decide_eq_false_iff_not]
      rw [kbit' hko ℓ (by omega), natWord_zero v]; simp
  -- phase 2: the bits
  let I2 : ℕ → DS VV MM → Prop := fun k b => b.env sD = k ∧ b.env sC = ℓ ∧ b.env sE = v % 2 ^ k ∧
    b.env sF = 2 ^ k ∧ b.kc = a.kc + ℓ + 1 + k ∧ b.out = a.out ++ dfr ((natWord v).take (ℓ + 1 + k)) ∧
    b.env dR = a.env dR + ℓ + 1 + k ∧ b.ip = a.ip ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ Fr a b copyNT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt sD sC) (.seq (.op (.rdK sB)) (.seq (emitD sB) (.seq (.ite (.eq sB v1)
      (.op (.add sE sF)) skipS) (.seq (.op (.shl sF)) (.op (.inc sD))))))) b (ℓ * (21 + 2) + 2) (I2 ℓ) := by
    refine Hs.loopN (c := .lt sD sC) (show sD ≠ sC by decide) I2 ℓ 21 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      have hcb : Cst b := Cst.of_fr hc h11 (by decide)
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      have hpk : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
      refine Hs.seq (t1 := 1) (t2 := 19) (hs_rdK C sB b (by simp [h5, h10]; omega)) (fun d hd => ?_)
      subst hd
      have hbit : bitOf b.kout b.kc = (v.testBit k).toNat := by
        rw [h5, h10, show a.kc + ℓ + 1 + k = a.kc + (ℓ + 1 + k) by ring, kbit' hko _ (by omega), hℓ,
          natWord_bit v k hk]
      refine Hs.seq (t1 := 12) (t2 := 6) (emitD_spec sB (by decide) _ (Cst.of_fr hcb (T := [sB])
        (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; vsimp [hy]) (by decide))
        (by vsimp [h7]; omega)) (fun d hd => ?_)
      subst hd
      set d := dState ({ b.set sB (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM)
        (decide ((({ b.set sB (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM)).env sB = 1)) with hd
      have dB : d.env sB = (v.testBit k).toNat := by rw [hd]; vsimp [dState, hbit]
      have dE : d.env sE = v % 2 ^ k := by rw [hd]; vsimp [dState, h3]
      have dF : d.env sF = 2 ^ k := by rw [hd]; vsimp [dState, h4]
      have dv1 : d.env v1 = 1 := by rw [hd]; vsimp [dState, hcb.one]
      have hmod : v % 2 ^ (k + 1) = v % 2 ^ k + (v.testBit k).toNat * 2 ^ k := by
        rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with hm | hm
        · rw [hm]; simp
        · rw [hm]; simp
      have hsum : v % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
        have := Nat.mod_lt v (show 0 < 2 ^ k by positivity)
        have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
        have : 2 ^ ℓ < 2 ^ C.Wd := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) hpw
        omega
      refine Hs.seq (t1 := 2) (t2 := 3)
        (R1 := fun e => e.env sE = v % 2 ^ (k + 1) ∧ e.kc = d.kc ∧ e.out = d.out ∧ e.ip = d.ip ∧ e.kin = d.kin ∧
          e.kout = d.kout ∧ Fr d e [sE, vJ])
        (Hs.ite (c := .eq sB v1) (show sB ≠ v1 by decide) (fun he => ?_) (fun he => ?_)) (fun e he => ?_)
      · have hb : v.testBit k = true := by
          revert he; simp only [Cnd.eval, dB, dv1]; cases v.testBit k <;> simp
        refine Hs.mono (hs_add C sE sF d (by decide) (by rw [dE, dF]; exact hsum)) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [dE, dF, hmod, hb], rfl, rfl, rfl, rfl, rfl, Fr.set d _ (by simp)⟩
      · have hb : v.testBit k = false := by
          revert he; simp only [Cnd.eval, dB, dv1]; cases v.testBit k <;> simp
        refine Hs.mono (skip_spec d) le_rfl ?_
        rintro e rfl
        exact ⟨by vsimp [dE, hmod, hb], rfl, rfl, rfl, rfl, rfl, Fr.set d _ (by simp)⟩
      · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he
        have eF : e.env sF = 2 ^ k := by rw [e7 sF (by decide), dF]
        have eD : e.env sD = k := by rw [e7 sD (by decide), hd]; vsimp [dState, h1]
        have eC : e.env sC = ℓ := by rw [e7 sC (by decide), hd]; vsimp [dState, h2]
        have eR : e.env dR = a.env dR + ℓ + 1 + k + 1 := by rw [e7 dR (by decide), hd]; vsimp [dState, h7]
        have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
        refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C sF e (by rw [eF]; omega)) (fun f hf => ?_)
        subst hf
        refine Hs.mono (hs_inc C sD _ (by vsimp [eD]; omega)) le_rfl ?_
        rintro g rfl
        have e1' : decide (bitOf b.kout b.kc = 1) = (natWord v).getD (ℓ + 1 + k) false := by
          rw [h5, h10, show a.kc + ℓ + 1 + k = a.kc + (ℓ + 1 + k) by ring, kbit hko _ (by omega)]
        refine ⟨by vsimp [eD], by vsimp [eC], by vsimp [e1], by vsimp [eF]; ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show e.kc = _
          rw [e2, hd]
          show b.kc + 1 = _
          omega
        · have hbd : decide ((({ b.set sB (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM)).env sB = 1) =
              (natWord v).getD (ℓ + 1 + k) false := by simp only [DS.env_set, Function.update_self]; exact e1'
          show e.out = _
          rw [e3, hd]
          simp only [dState, DS.set_out, hbd]
          rw [show ℓ + 1 + (k + 1) = ℓ + 1 + k + 1 by ring, take_succ _ _ (by omega), h6]
          simp [List.append_assoc]
        · vsimp [eR]; ring
        · simp [e4, hd, dState, h8]
        · simp [e5, hd, dState, h9]
        · simp [e6, hd, dState, h10]
        · intro y hy
          obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := frT y hy
          vsimp [y4, y6]
          rw [e7 y (by simp [y5, y8]), hd]
          vsimp [dState, y2, y7]
          exact h11 y hy
    · intro b hb
      obtain ⟨h1, h2, -⟩ := hb
      simp [Cnd.eval, h1, h2]
  -- the whole
  have e0 : decide (bitOf a.kout a.kc = 1) = (natWord v).getD 0 false := by
    have := kbit hko 0 (by omega); rwa [Nat.add_zero] at this
  refine Hs.mono (t := 1 + (1 + (12 + (ℓ * (16 + 2) + 2 + (1 + (1 + (1 + (ℓ * (21 + 2) + 2) + 1) + 1) + 1) + 1) + 1) + 1)
      + 1) (Hs.seq (hs_zero C sC a) (fun d hd => ?_)) (by omega) (fun _ h => h)
  subst hd
  refine Hs.seq (hs_rdK C sA _ (by simp; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.seq (emitD_spec sA (by decide) _ (Cst.of_fr hc (T := [sA, sC])
    (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; vsimp [hy.1, hy.2])
    (by decide)) (by vsimp []; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.seq (l1 _ ⟨by vsimp [dState], by vsimp [dState], by simp [dState], ?_, by vsimp [dState], rfl, rfl, rfl,
    ?_⟩) (fun d hd => ?_)
  · rw [take_succ _ 0 (by omega), List.take_zero, List.nil_append, ← e0]
    simp [dState]
  · intro y hy
    obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := frT y hy
    vsimp [dState, y1, y3, y7]
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hd
  have dcb : Cst d := Cst.of_fr hc d9 (by decide)
  refine Hs.seq (hs_zero C sE d) (fun e he => ?_)
  subst he
  refine Hs.seq (hs_copy C sF v1 _ (by decide)) (fun e he => ?_)
  subst he
  refine Hs.seq (hs_zero C sD _) (fun e he => ?_)
  subst he
  refine Hs.mono (l2 _ ⟨by vsimp [], by vsimp [d1], by vsimp [Nat.mod_one], by vsimp [dcb.one], by simp [d3],
    by simp [d4], by vsimp [d5], by simp [d6], by simp [d7], by simp [d8], ?_⟩) le_rfl ?_
  · intro y hy
    obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := frT y hy
    vsimp [y4, y5, y6]
    exact d9 y hy
  · rintro b ⟨b1, -, b3, -, b5, b6, b7, b8, b9, b10, b11⟩
    have htk : ℓ + 1 + ℓ = (natWord v).length := by omega
    refine ⟨by rw [b3, Nat.mod_eq_of_lt hvl], by rw [b5, hnw]; ring, by rw [b6, htk, List.take_length],
      by rw [b7, hnw]; ring, b8, b9, b10, b11⟩

end NearCubicGates.Adapters.ShortPCP.Assembly
