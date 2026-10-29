import SourceAdapters.Amplification.EncLag

/-!
# The inner value at a point and its Hadamard bit, in the cell language

* `valP`: `YY := valAt p t h m n T c = Σ_{i < 2^n, T(i)} prodAt i c`, reading the message truth table `T`
  sequentially from the input (`rdI`) at the position `base` (STV Lemma 25: the low-degree extension takes the
  value `msg(i)` at the grid point of `i`), then moving back to `base`;
* `hadP`: `HP := [hadBit t YY c]`, the parity of the common low `t` bits (the Hadamard block, STV Lemma 28).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

theorem Glob.of_frI {g : Prm} {S : List Var} {w : List Bool} {a b : Ds} (h : Glob g a) (hf : FrI S w a b)
    (hS : ∀ x ∈ globs, x ∉ S) : Glob g b := by
  have e : ∀ x ∈ globs, b.env x = a.env x := fun x hx => hf.env x (hS x hx)
  obtain ⟨⟨h0, h1, h2⟩, ht, htb, hpt, hh, hph, hn, hpn, hm, hL, hpl, hp, he⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [e _ (by simp [globs])]; assumption)

/-- The message truth table `T` sits in the input at `base`. -/
def TableAt (C : Ctx) (base n : ℕ) (T : ℕ → Bool) : Prop :=
  base + 2 ^ n ≤ C.inp.length ∧ ∀ i < 2 ^ n, C.inp.getD (base + i) false = T i

abbrev vYI : Var := 61
abbrev vYB : Var := 62
abbrev vYY : Var := 63

def valS : List Var := [vYI, vYB, vYY, vQI] ++ prodS

def valAdd : Sc :=
  .seq (.op (.copy vQI vYI)) <| .seq prodP <| .seq (.op (.copy vXA vYY)) <| .seq (.op (.copy vXB vQP)) <|
  .seq xorP (.op (.copy vYY vXR))

def valBody : Sc := .seq (.op (.rdI vYB)) <| .seq (.ite (.eq vYB vONE) valAdd (.op (.zero vMQ))) (.op (.inc vYI))

def valBack : Sc := .seq (.op .bkI) (.op (.sub vYI vONE))

def valP : Sc :=
  .seq (.op (.zero vYY)) <| .seq (.op (.zero vYI)) <|
  .seq (.loop (.lt vYI vPOWN) valBody) (.loop (.lt vZ vYI) valBack)

def valAddCost (t h m : ℕ) : ℕ := prodCost t h m + 25 * t + 60

def valCost (t h m n : ℕ) : ℕ := 2 ^ n * (valAddCost t h m + 10 + 2) + 2 ^ n * (3 + 2) + 20

theorem valAdd_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (i c y : ℕ) (hai : a.env vYI = i) (hac : a.env vQC = c) (hay : a.env vYY = y) (hyl : y < 2 ^ g.t) :
    Runs C valAdd a (valAddCost g.t g.h g.m) valS []
      (fun b => b.env vYY = y ^^^ prodAt g.p g.t g.h g.m i c ∧ b.env vYY < 2 ^ g.t ∧ b.env vYI = i) := by
  have ht1 : 2 ^ g.t ≤ 2 ^ (g.t + 1) := two_pow_mono (by omega)
  have hW2 : g.t + 1 + 2 ≤ C.Wd := by have := hw.1; have := hw.2.1; omega
  refine Runs.op1 (run_copy C valS a vQI vYI (by decide) (by decide)) ?_ (by unfold valAddCost; omega)
  have hg1 : Glob g (a.set vQI (a.env vYI)) := hg.of_fr (Fr.set valS a vQI _ (by decide)) (by decide)
  refine Runs.callS (prodP_spec C g hw hp _ hg1 i c (by norm_env; exact hai) (by norm_env; exact hac))
    (by decide) ?_ (by unfold valAddCost; omega)
  rintro b hb ⟨hbv, hbl⟩
  have hgb : Glob g b := hg1.of_fr hb (by decide)
  refine Runs.op1 (run_copy C valS _ vXA vYY (by decide) (by decide)) ?_ (by unfold valAddCost; omega)
  refine Runs.op1 (run_copy C valS _ vXB vQP (by decide) (by decide)) ?_ (by unfold valAddCost; omega)
  have hbY : b.env vYY = y := by rw [hb.env vYY (by decide)]; norm_env; exact hay
  refine Runs.callS (xorP_spec C _ ⟨by norm_env; exact hgb.c.1, by norm_env; exact hgb.c.2.1,
      by norm_env; exact hgb.c.2.2⟩ (g.t + 1) (by norm_env; exact hgb.tb) y (prodAt g.p g.t g.h g.m i c)
      (by norm_env; exact hbY) (by norm_env; exact hbv) (lt_of_lt_of_le hyl ht1) (lt_of_lt_of_le (hbv ▸ hbl) ht1) hW2)
    (by decide) ?_ (by unfold valAddCost; omega)
  intro d hd hdv
  refine Runs.last (run_copy C valS _ vYY vXR (by decide) (by decide)) ?_ (by unfold valAddCost; omega)
  intro _
  norm_env
  refine ⟨hdv, by rw [hdv]; exact Nat.xor_lt_two_pow hyl (hbv ▸ hbl), ?_⟩
  rw [hd.env vYI (by decide)]; norm_env; rw [hb.env vYI (by decide)]; norm_env; exact hai

theorem valAt_succ (p t h m : ℕ) (T : ℕ → Bool) (c j : ℕ) :
    (List.range (j + 1)).foldl (fun Y i => if T i then Y ^^^ prodAt p t h m i c else Y) 0 =
      (if T j then (List.range j).foldl (fun Y i => if T i then Y ^^^ prodAt p t h m i c else Y) 0 ^^^
        prodAt p t h m j c else (List.range j).foldl (fun Y i => if T i then Y ^^^ prodAt p t h m i c else Y) 0) := by
  rw [List.range_succ, List.foldl_append]; rfl

/-- The state of the reading loop of `valP` before round `j`. -/
def ValInv (g : Prm) (a0 : Ds) (base : ℕ) (T : ℕ → Bool) (c j : ℕ) (b : Ds) : Prop :=
  FrI valS [] a0 b ∧ b.ip = base + j ∧
    b.env vYY = (List.range j).foldl (fun Y i => if T i then Y ^^^ prodAt g.p g.t g.h g.m i c else Y) 0 ∧
    b.env vYY < 2 ^ g.t ∧ b.env vYI = j

/-- The state of the rewinding loop of `valP` after `j` rounds. -/
def BackInv (a0 : Ds) (base N : ℕ) (Y : ℕ) (j : ℕ) (b : Ds) : Prop :=
  FrI valS [] a0 b ∧ b.ip = base + N - j ∧ b.env vYY = Y ∧ b.env vYI = N - j

theorem valP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (T : ℕ → Bool) (c base : ℕ) (hT : TableAt C base g.n T) (hip : a.ip = base) (hac : a.env vQC = c) :
    Runs C valP a (valCost g.t g.h g.m g.n) valS []
      (fun b => b.env vYY = valAt g.p g.t g.h g.m g.n T c ∧ b.env vYY < 2 ^ g.t) := by
  have hNW : 2 ^ g.n < 2 ^ C.Wd := pow_lt_W hw (by have := hw.2.2.2.1; omega)
  have hone : 0 < 2 ^ g.t := Nat.two_pow_pos _
  -- the two initial operations
  set a1 := (a.set vYY 0).set vYI 0 with ha1
  have e0 : Ex C (.seq (.op (.zero vYY)) (.op (.zero vYI))) a a1 3 :=
    Ex.seq (Ex.op (OpEx.zero vYY a)) (Ex.op (OpEx.zero vYI _))
  have hga1 : Glob g a1 := hg.of_fr ((Fr.set valS a vYY 0 (by decide)).set_right vYI 0 (by decide)) (by decide)
  -- the reading loop
  have hstop : ∀ b, ValInv g a base T c (2 ^ g.n) b → (Cnd.lt vYI vPOWN).eval b = false := by
    rintro b ⟨hf, -, -, -, hI⟩
    have hgb : Glob g b := hg.of_frI hf (by decide)
    simp [Cnd.eval, hI, hgb.pown]
  have hstep : ∀ j < 2 ^ g.n, ∀ b, ValInv g a base T c j b → (Cnd.lt vYI vPOWN).eval b = true ∧
      ∃ b', Ex C valBody b b' (valAddCost g.t g.h g.m + 10) ∧ ValInv g a base T c (j + 1) b' := by
    rintro j hj b ⟨hf, hbip, hY, hYl, hI⟩
    have hgb : Glob g b := hg.of_frI hf (by decide)
    refine ⟨by simp [Cnd.eval, hI, hgb.pown, hj], ?_⟩
    have hrd : b.ip < C.inp.length := by rw [hbip]; have := hT.1; omega
    set b1 : Ds := { b.set vYB (bitOf C.inp b.ip) with ip := b.ip + 1 } with hb1
    have e1 : Ex C (.op (.rdI vYB)) b b1 1 := Ex.op (OpEx.rdI vYB b hrd)
    have hbit : bitOf C.inp b.ip = (T j).toNat := by rw [bitOf, hbip, hT.2 j hj]
    have hg1 : Glob g b1 := hgb.of_frI (FrI.rd valS b vYB (by decide) _ _) (by decide)
    have hb1Y : b1.env vYY = b.env vYY := by simp (config := { decide := true }) [b1, env_set]
    have hb1I : b1.env vYI = j := by simp (config := { decide := true }) [b1, env_set, hI]
    have hb1C : b1.env vQC = c := by
      simp (config := { decide := true }) only [b1, env_set, ite_false]; rw [hf.env vQC (by decide)]; exact hac
    -- the conditional addition
    have hite : Runs C (.ite (.eq vYB vONE) valAdd (.op (.zero vMQ))) b1 (valAddCost g.t g.h g.m + 1) valS []
        (fun d => d.env vYY = (if T j then b.env vYY ^^^ prodAt g.p g.t g.h g.m j c else b.env vYY) ∧
          d.env vYY < 2 ^ g.t ∧ d.env vYI = j) := by
      by_cases hTj : T j
      · refine Runs.iteT (by unfold Cnd.wf; decide) (by simp (config := { decide := true }) [Cnd.eval, b1, env_set, hbit, hTj, hgb.c.2.1]) ?_
        refine (valAdd_spec C g hw hp b1 hg1 j c (b.env vYY) hb1I hb1C hb1Y hYl).mono le_rfl
          (List.Subset.refl _) ?_
        rintro d - ⟨hdv, hdl, hdI⟩
        exact ⟨by rw [if_pos hTj]; exact hdv, hdl, hdI⟩
      · refine Runs.iteF (by unfold Cnd.wf; decide) (by simp (config := { decide := true }) [Cnd.eval, b1, env_set, hbit, hTj, hgb.c.2.1]) ?_
        refine (run_zero C valS b1 vMQ (by decide)).mono (by unfold valAddCost; omega) (List.Subset.refl _) ?_
        rintro d - rfl
        refine ⟨?_, ?_, ?_⟩ <;> norm_env
        · rw [if_neg hTj, hb1Y]
        · rw [hb1Y]; exact hYl
        · exact hb1I
    obtain ⟨d, ed, hfd, hdY, hdl, hdI⟩ := hite
    have hjW : j + 1 < 2 ^ C.Wd := by omega
    have e3 : Ex C (.op (.inc vYI)) d (d.set vYI (d.env vYI + 1)) 1 := Ex.op (OpEx.inc vYI d (by rw [hdI]; exact hjW))
    refine ⟨_, (Ex.seq e1 (Ex.seq ed e3)).mono (by unfold valAddCost; omega), ?_, ?_, ?_, ?_, ?_⟩
    · exact ((hf.trans0 (FrI.rd valS b vYB (by decide) _ _)).trans0 hfd.toI).set_right _ _ (by decide)
    · simp only [DS.set]; rw [hfd.ip]; simp [b1, hbip]; omega
    · norm_env; rw [hdY, valAt_succ, hY]
    · norm_env; exact hdl
    · norm_env; rw [hdI]
  have hinit : ValInv g a base T c 0 a1 := by
    refine ⟨((Fr.set valS a vYY 0 (by decide)).set_right vYI 0 (by decide)).toI, by simp [a1, hip], ?_, ?_, ?_⟩
    · simp (config := { decide := true }) [a1, env_set]
    · simp (config := { decide := true }) [a1, env_set, hone]
    · simp (config := { decide := true }) [a1, env_set]
  obtain ⟨b, eb, hbinv⟩ := ex_loopN (C := C) (c := .lt vYI vPOWN) (body := valBody) (by unfold Cnd.wf; decide)
    (2 ^ g.n) (valAddCost g.t g.h g.m + 10) (ValInv g a base T c) hstep hstop a1 hinit
  -- the rewinding loop
  obtain ⟨hfb, hbip, hbY, hbl, hbI⟩ := hbinv
  have hgb : Glob g b := hg.of_frI hfb (by decide)
  have bstop : ∀ d, BackInv a base (2 ^ g.n) (b.env vYY) (2 ^ g.n) d → (Cnd.lt vZ vYI).eval d = false := by
    rintro d ⟨hf, -, -, hI⟩
    have hgd : Glob g d := hg.of_frI hf (by decide)
    simp [Cnd.eval, hI, hgd.c.1]
  have bstep : ∀ j < 2 ^ g.n, ∀ d, BackInv a base (2 ^ g.n) (b.env vYY) j d → (Cnd.lt vZ vYI).eval d = true ∧
      ∃ d', Ex C valBack d d' 3 ∧ BackInv a base (2 ^ g.n) (b.env vYY) (j + 1) d' := by
    rintro j hj d ⟨hf, hdip, hdY, hdI⟩
    have hgd : Glob g d := hg.of_frI hf (by decide)
    refine ⟨by simp [Cnd.eval, hdI, hgd.c.1]; omega, ?_⟩
    have e1 : Ex C (.op .bkI) d { d with ip := d.ip - 1 } 1 := Ex.op (OpEx.bkI d (by rw [hdip]; omega))
    have e2 : Ex C (.op (.sub vYI vONE)) { d with ip := d.ip - 1 }
        ({ d with ip := d.ip - 1 }.set vYI ({ d with ip := d.ip - 1 }.env vYI - { d with ip := d.ip - 1 }.env vONE)) 1 :=
      Ex.op (OpEx.sub vYI vONE _ (by decide) (by simp [hgd.c.2.1, hdI]; omega))
    refine ⟨_, Ex.seq e1 e2, ?_, ?_, ?_, ?_⟩
    · exact (hf.ip_right _).set_right _ _ (by decide)
    · simp only [DS.set]; rw [hdip]; omega
    · simp (config := { decide := true }) [env_set, hdY]
    · simp (config := { decide := true }) [env_set, hdI, hgd.c.2.1]; omega
  have binit : BackInv a base (2 ^ g.n) (b.env vYY) 0 b := ⟨hfb, by rw [hbip]; omega, rfl, by rw [hbI]; omega⟩
  obtain ⟨d, ed, hdinv⟩ := ex_loopN (C := C) (c := .lt vZ vYI) (body := valBack) (by unfold Cnd.wf; decide)
    (2 ^ g.n) 3 (BackInv a base (2 ^ g.n) (b.env vYY)) bstep bstop b binit
  obtain ⟨hfd, hdip, hdY, -⟩ := hdinv
  refine ⟨d, (Ex.seq (Ex.op (OpEx.zero vYY a)) (Ex.seq (Ex.op (OpEx.zero vYI _)) (Ex.seq eb ed))).mono
    (by unfold valCost; omega), hfd.toFr (by rw [hdip, hip]; omega), ?_, ?_⟩
  · rw [hdY, hbY]; rfl
  · rw [hdY]; exact hbl

end NearCubicGates.Adapters.Amplification.Enc
