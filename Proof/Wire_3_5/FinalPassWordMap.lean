import Proof.Wire_3_5.FinalPassWordLib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- The bits of a word with their `true` markers: `frame w = frameP w ++ [false]`. -/
def frameP (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

theorem frame_eq_frameP (w : List Bool) : frame w = frameP w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, frameP, ih]

@[simp] theorem frameP_nil : frameP [] = [] := rfl
@[simp] theorem frameP_cons (b : Bool) (w : List Bool) : frameP (b :: w) = true :: b :: frameP w := rfl
@[simp] theorem frameP_length (w : List Bool) : (frameP w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; omega

/-- The state-carrying map: outputs `out a b c`, next state `nxt a b c`, low bit first. -/
def mapS (out nxt : Bool → Bool → Bool → Bool) : List Bool → List Bool → Bool → List Bool × Bool
  | a :: as, b :: bs, c => (out a b c :: (mapS out nxt as bs (nxt a b c)).1, (mapS out nxt as bs (nxt a b c)).2)
  | _, _, c => ([], c)

/-- Close an equality of word states with variable registers and streams. -/
syntax "wgen_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wgen_eq) => `(tactic| wgen_eq [])
  | `(tactic| wgen_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext x
           simp only [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_sh, WState.seth_sh,
             WState.sets_sh, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
           split_ifs <;> subst_vars <;> (try simp_all [$ts,*]) <;> omega)
        | rfl
        | simp))

variable {ns nr : ℕ} (cap : ℕ)

theorem wsets_same (σ : WState ns nr) (i : Fin (ns + 1)) : σ.sets i (σ.st i) = σ :=
  WState.eq rfl (by simp) rfl rfl

theorem wseth_same (σ : WState ns nr) (i : Fin (ns + 1)) : σ.seth i (σ.sh i) = σ :=
  WState.eq (by simp) rfl rfl rfl

/-! ## One bit -/

/-- Set a flag register to `v`. -/
def setFlag (F : Fin nr) (v : Bool) : WM ns nr := if v then .ifr F .skip (.inc F) else .ifr F (.dec F) .skip

def leaf (out nxt : Bool → Bool → Bool → Bool) (A : Fin (ns + 1)) (F : Fin nr) (a b : Bool) : WM ns nr :=
  .ifr F (.seq (.wr A (out a b true)) (setFlag F (nxt a b true)))
    (.seq (.wr A (out a b false)) (setFlag F (nxt a b false)))

/-- The bit operation: branch on the bits of `A` and `B`. -/
def bitOp (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F : Fin nr) : WM ns nr :=
  .ifs A (.ifs B (leaf out nxt A F true true) (leaf out nxt A F true false))
    (.ifs B (leaf out nxt A F false true) (leaf out nxt A F false false))

theorem setFlag_spec (F : Fin nr) (v c : Bool) (σ : WState ns nr) (hF : σ.val F = c.toNat) (hcap : 1 ≤ cap) :
    WExec cap (setFlag F v) σ (σ.setv F v.toNat) 4 := by
  cases v <;> cases c <;> simp only [setFlag, Bool.toNat_false, Bool.toNat_true, if_true] at hF ⊢
  · have e : σ.setv F 0 = σ := by rw [← hF]; exact wsetv_same σ F
    rw [e]; exact WExec.mono (WExec.ifrF hF (WExec.skip σ)) (by omega)
  · have h := WExec.dec (cap := cap) F σ (by omega)
    rw [hF] at h
    exact WExec.mono (WExec.ifrT (by omega) h) (by omega)
  · have h := WExec.inc (cap := cap) F σ (by omega)
    rw [hF] at h
    exact WExec.ifrF hF h
  · have e : σ.setv F 1 = σ := by rw [← hF]; exact wsetv_same σ F
    rw [e]; exact WExec.mono (WExec.ifrT (by omega) (WExec.skip σ)) (by omega)

theorem leaf_spec (out nxt : Bool → Bool → Bool → Bool) (A : Fin (ns + 1)) (F : Fin nr) (a b c : Bool)
    (σ : WState ns nr) (hF : σ.val F = c.toNat) (hcap : 1 ≤ cap) :
    WExec cap (leaf out nxt A F a b) σ
      ((σ.sets A (writeTapeBit (σ.st A) (σ.sh A) (out a b c))).setv F (nxt a b c).toNat) 7 := by
  have hw := WExec.wr (cap := cap) A (out a b c) σ
  have hs := setFlag_spec cap F (nxt a b c) c (σ.sets A (writeTapeBit (σ.st A) (σ.sh A) (out a b c)))
    (by simpa using hF) hcap
  cases c
  · exact WExec.mono (WExec.ifrF (by simpa using hF) (WExec.seq hw hs)) (by omega)
  · exact WExec.mono (WExec.ifrT (by simp at hF; omega) (WExec.seq hw hs)) (by omega)

theorem bitOp_spec (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F : Fin nr) (a b c : Bool)
    (σ : WState ns nr) (ha : wbit σ A = a) (hb : wbit σ B = b) (hF : σ.val F = c.toNat) (hcap : 1 ≤ cap) :
    WExec cap (bitOp out nxt A B F) σ
      ((σ.sets A (writeTapeBit (σ.st A) (σ.sh A) (out a b c))).setv F (nxt a b c).toNat) 9 := by
  have hl := leaf_spec cap out nxt A F a b c σ hF hcap
  cases a <;> cases b
  · exact WExec.mono (WExec.ifsF ha (WExec.ifsF hb hl)) (by omega)
  · exact WExec.mono (WExec.ifsF ha (WExec.ifsT hb hl)) (by omega)
  · exact WExec.mono (WExec.ifsT ha (WExec.ifsF hb hl)) (by omega)
  · exact WExec.mono (WExec.ifsT ha (WExec.ifsT hb hl)) (by omega)

/-! ## The pass -/

/-- One coordinate of the pass. -/
def mapStep (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (.fwd A) (.seq (.fwd B) (.seq (bitOp out nxt A B F) (.seq (.fwd A) (.seq (.fwd B) (.seq (.inc R) (.inc R))))))

/-- Move both streams back by the counter. -/
def rewind2 (A B : Fin (ns + 1)) (R : Fin nr) : WM ns nr := .whr R (.seq (.dec R) (.seq (.bwd A) (.bwd B)))

/-- **The pass**: map the framed word on `A` against the framed word on `B`, then return both heads. -/
def mapPass (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr :=
  .seq (.whs A (mapStep out nxt A B F R)) (rewind2 A B R)

theorem writeTapeBit_mid' (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem readTapeBit_mid (pre tail : List Bool) (b : Bool) : readTapeBit (pre ++ b :: tail) pre.length = b := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

/-- The state after mapping `n` coordinates. -/
def mapState (A B : Fin (ns + 1)) (F R : Fin nr) (newA : List Bool) (n : ℕ) (c : Bool) (σ : WState ns nr) :
    WState ns nr :=
  ((((σ.sets A newA).seth A (σ.sh A + 2 * n)).seth B (σ.sh B + 2 * n)).setv F c.toNat).setv R (σ.val R + 2 * n)

theorem mapLoop_spec (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F R : Fin nr) (hAB : A ≠ B)
    (hFR : F ≠ R) (hcap : 1 ≤ cap) (restA restB : List Bool) :
    ∀ (as bs preA preB : List Bool) (c : Bool) (σ : WState ns nr), as.length = bs.length →
      σ.st A = preA ++ frameP as ++ false :: restA → σ.sh A = preA.length →
      σ.st B = preB ++ frameP bs ++ restB → σ.sh B = preB.length →
      σ.val F = c.toNat → σ.val R + 2 * as.length ≤ cap →
      WExec cap (.whs A (mapStep out nxt A B F R)) σ
        (mapState A B F R (preA ++ frameP (mapS out nxt as bs c).1 ++ false :: restA) as.length
          (mapS out nxt as bs c).2 σ) (as.length * 27 + 1)
  | [], bs, preA, preB, c, σ, hl, hA, hhA, _, _, hF, _ => by
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hbs
    simp only [frameP_nil, List.append_nil] at hA
    have e : mapState A B F R (preA ++ frameP (mapS out nxt [] [] c).1 ++ false :: restA) ([] : List Bool).length
        (mapS out nxt [] [] c).2 σ = σ := by
      unfold mapState
      simp only [mapS, frameP_nil, List.append_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
      rw [← hA, ← hF, wsets_same, wseth_same, wseth_same, wsetv_same, wsetv_same]
    rw [e]
    refine WExec.whsF ?_
    unfold wbit
    rw [hA, hhA]
    exact readTapeBit_mid preA restA false
  | a :: as', bs, preA, preB, c, σ, hl, hA, hhA, hB, hhB, hF, hR => by
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs' => exact ⟨b, bs', rfl⟩
    have hl' : as'.length = bs'.length := by simpa using hl
    simp only [List.length_cons] at hR ⊢
    have hread0 : wbit σ A = true := by
      unfold wbit; rw [hA, hhA]; simpa using readTapeBit_mid preA (a :: (frameP as' ++ false :: restA)) true
    -- forward on both streams
    have s1 := WExec.fwd (cap := cap) A σ
    have s2 := WExec.fwd (cap := cap) B (σ.seth A (σ.sh A + 1))
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = (σ.seth A (σ.sh A + 1)).seth B ((σ.seth A (σ.sh A + 1)).sh B + 1) :=
      ⟨_, rfl⟩
    rw [← hσ2] at s2
    have h2A : σ2.sh A = preA.length + 1 := by rw [hσ2]; simp [Function.update_of_ne hAB, hhA]
    have h2B : σ2.sh B = preB.length + 1 := by rw [hσ2]; simp [Function.update_of_ne (Ne.symm hAB), hhB]
    have h2stA : σ2.st A = (preA ++ [true]) ++ a :: (frameP as' ++ false :: restA) := by rw [hσ2]; simp [hA]
    have h2stB : σ2.st B = (preB ++ [true]) ++ b :: (frameP bs' ++ restB) := by rw [hσ2]; simp [hB]
    have ha : wbit σ2 A = a := by
      unfold wbit; rw [h2stA, h2A]; simpa using readTapeBit_mid (preA ++ [true]) (frameP as' ++ false :: restA) a
    have hb : wbit σ2 B = b := by
      unfold wbit; rw [h2stB, h2B]; simpa using readTapeBit_mid (preB ++ [true]) (frameP bs' ++ restB) b
    have hF2 : σ2.val F = c.toNat := by rw [hσ2]; simp [hF]
    -- the bit
    have s3 := bitOp_spec cap out nxt A B F a b c σ2 ha hb hF2 hcap
    obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr,
        τ = (σ2.sets A (writeTapeBit (σ2.st A) (σ2.sh A) (out a b c))).setv F (nxt a b c).toNat := ⟨_, rfl⟩
    rw [← hσ3] at s3
    have h3stA : σ3.st A = (preA ++ [true, out a b c]) ++ frameP as' ++ false :: restA := by
      rw [hσ3]; simp only [WState.setv_st, WState.sets_st, Function.update_self]
      rw [h2stA, h2A]
      have := writeTapeBit_mid' (preA ++ [true]) (frameP as' ++ false :: restA) a (out a b c)
      simp only [List.length_append, List.length_singleton] at this
      rw [this]; simp
    -- forward on both streams, count two
    have s4 := WExec.fwd (cap := cap) A σ3
    have s5 := WExec.fwd (cap := cap) B (σ3.seth A (σ3.sh A + 1))
    obtain ⟨σ5, hσ5⟩ : ∃ τ : WState ns nr, τ = (σ3.seth A (σ3.sh A + 1)).seth B ((σ3.seth A (σ3.sh A + 1)).sh B + 1) :=
      ⟨_, rfl⟩
    rw [← hσ5] at s5
    have hR5 : σ5.val R = σ.val R := by
      rw [hσ5, hσ3, hσ2]; simp [Function.update_of_ne (Ne.symm hFR)]
    have s6 := WExec.inc (cap := cap) R σ5 (by omega)
    have s7 := WExec.inc (cap := cap) R (σ5.setv R (σ5.val R + 1)) (by simp; omega)
    obtain ⟨σ7, hσ7⟩ : ∃ τ : WState ns nr,
        τ = (σ5.setv R (σ5.val R + 1)).setv R ((σ5.setv R (σ5.val R + 1)).val R + 1) := ⟨_, rfl⟩
    rw [← hσ7] at s7
    have h7A : σ7.sh A = (preA ++ [true, out a b c]).length := by
      rw [hσ7, hσ5, hσ3]; simp [Function.update_of_ne hAB, h2A]
    have h7B : σ7.sh B = (preB ++ [true, b]).length := by
      rw [hσ7, hσ5, hσ3]; simp [Function.update_of_ne (Ne.symm hAB), h2B]
    have h7stA : σ7.st A = (preA ++ [true, out a b c]) ++ frameP as' ++ false :: restA := by
      rw [hσ7, hσ5]; simp [h3stA]
    have h7stB : σ7.st B = (preB ++ [true, b]) ++ frameP bs' ++ restB := by
      rw [hσ7, hσ5, hσ3, hσ2]; simp [Function.update_of_ne (Ne.symm hAB), hB]
    have h7F : σ7.val F = (nxt a b c).toNat := by
      rw [hσ7, hσ5, hσ3]; simp [Function.update_of_ne hFR]
    have h7R : σ7.val R = σ.val R + 2 := by rw [hσ7]; simp [hR5]
    have ih := mapLoop_spec out nxt A B F R hAB hFR hcap restA restB as' bs' (preA ++ [true, out a b c])
      (preB ++ [true, b]) (nxt a b c) σ7 hl' h7stA h7A h7stB h7B h7F (by rw [h7R]; omega)
    have body := WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7)))))
    refine WExec.cast cap (WExec.whsT hread0 body ih) ?_ (by omega)
    unfold mapState
    simp only [mapS, frameP_cons]
    refine WState.eq ?_ ?_ ?_ (by rw [hσ7, hσ5, hσ3, hσ2]; rfl)
    · funext j
      simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [h7B, hhB]; omega
      · by_cases hjA : j = A
        · subst hjA; simp [hjB, h7A, hhA]; omega
        · simp only [hjB, hjA, if_false]
          rw [hσ7, hσ5, hσ3, hσ2]; simp [Function.update_of_ne hjA, Function.update_of_ne hjB]
    · funext j
      simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      by_cases hjA : j = A
      · subst hjA; simp
      · simp only [hjA, if_false]
        rw [hσ7, hσ5, hσ3, hσ2]; simp [Function.update_of_ne hjA]
    · funext j
      simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases hjR : j = R
      · subst hjR; simp only [if_true]; rw [h7R]; omega
      · by_cases hjF : j = F
        · subst hjF; simp [hjR]
        · simp only [hjR, hjF, if_false]
          rw [hσ7, hσ5, hσ3, hσ2]; simp [Function.update_of_ne hjR, Function.update_of_ne hjF]

theorem rewind2_spec (A B : Fin (ns + 1)) (R : Fin nr) (hAB : A ≠ B) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val R = n → n ≤ cap →
      WExec cap (rewind2 A B R) σ (((σ.setv R 0).seth A (σ.sh A - n)).seth B (σ.sh B - n)) (7 * n + 1)
  | 0, σ, h0, _ => by
    have e : ((σ.setv R 0).seth A (σ.sh A - 0)).seth B (σ.sh B - 0) = σ := by
      simp only [Nat.sub_zero]
      rw [← h0, wsetv_same]
      refine WState.eq ?_ rfl rfl rfl
      funext j
      by_cases hjB : j = B
      · subst hjB; simp
      · by_cases hjA : j = A
        · subst hjA; simp [hjB]
        · simp [hjB]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hc => by
    have s1 := WExec.dec (cap := cap) R σ (by omega)
    have s2 := WExec.bwd (cap := cap) A (σ.setv R (σ.val R - 1))
    have s3 := WExec.bwd (cap := cap) B ((σ.setv R (σ.val R - 1)).seth A ((σ.setv R (σ.val R - 1)).sh A - 1))
    have ih := rewind2_spec A B R hAB n (((σ.setv R (σ.val R - 1)).seth A ((σ.setv R (σ.val R - 1)).sh A - 1)).seth B
      (((σ.setv R (σ.val R - 1)).seth A ((σ.setv R (σ.val R - 1)).sh A - 1)).sh B - 1)) (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext j
      simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [Ne.symm hAB]; omega
      · by_cases hjA : j = A
        · subst hjA; simp [hjB]; omega
        · simp [hjA, hjB]
    · funext j
      by_cases hjR : j = R
      · subst hjR; simp
      · simp [hjR]

theorem mapPass_spec (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F R : Fin nr) (hAB : A ≠ B)
    (hFR : F ≠ R) (hcap : 1 ≤ cap) (as bs restA restB : List Bool) (c : Bool) (σ : WState ns nr)
    (hl : as.length = bs.length) (hA : σ.st A = frameP as ++ false :: restA) (hhA : σ.sh A = 0)
    (hB : σ.st B = frameP bs ++ restB) (hhB : σ.sh B = 0) (hF : σ.val F = c.toNat) (hR : σ.val R = 0)
    (hRc : 2 * as.length ≤ cap) :
    WExec cap (mapPass out nxt A B F R) σ
      ((σ.sets A (frameP (mapS out nxt as bs c).1 ++ false :: restA)).setv F (mapS out nxt as bs c).2.toNat)
      (as.length * 41 + 3) := by
  have h1 := mapLoop_spec cap out nxt A B F R hAB hFR hcap restA restB as bs [] [] c σ hl (by simpa using hA)
    (by simpa using hhA) (by simpa using hB) (by simpa using hhB) hF (by omega)
  simp only [List.nil_append] at h1
  have h2 := rewind2_spec cap A B R hAB (2 * as.length)
    (mapState A B F R (frameP (mapS out nxt as bs c).1 ++ false :: restA) as.length (mapS out nxt as bs c).2 σ)
    (by simp [mapState, hR]) hRc
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  unfold mapState
  refine WState.eq ?_ rfl ?_ rfl
  · funext j
    simp only [WState.seth_sh, WState.setv_sh, WState.sets_sh, Function.update_apply]
    by_cases hjB : j = B
    · subst hjB; simp [hhB]
    · by_cases hjA : j = A
      · subst hjA; simp [hjB, hhA]
      · simp [hjA, hjB]
  · funext j
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases hjR : j = R
    · subst hjR; simp [Ne.symm hFR, hR]
    · simp [hjR]

/-- **The pass at any positions**: the words start at the heads of `A` and `B`. -/
theorem mapPassAt_spec (out nxt : Bool → Bool → Bool → Bool) (A B : Fin (ns + 1)) (F R : Fin nr) (hAB : A ≠ B)
    (hFR : F ≠ R) (hcap : 1 ≤ cap) (as bs preA preB restA restB : List Bool) (c : Bool) (σ : WState ns nr)
    (hl : as.length = bs.length) (hA : σ.st A = preA ++ frameP as ++ false :: restA) (hhA : σ.sh A = preA.length)
    (hB : σ.st B = preB ++ frameP bs ++ restB) (hhB : σ.sh B = preB.length) (hF : σ.val F = c.toNat)
    (hR : σ.val R = 0) (hRc : 2 * as.length ≤ cap) :
    WExec cap (mapPass out nxt A B F R) σ
      ((σ.sets A (preA ++ frameP (mapS out nxt as bs c).1 ++ false :: restA)).setv F (mapS out nxt as bs c).2.toNat)
      (as.length * 41 + 3) := by
  have h1 := mapLoop_spec cap out nxt A B F R hAB hFR hcap restA restB as bs preA preB c σ hl hA hhA hB hhB hF
    (by omega)
  have h2 := rewind2_spec cap A B R hAB (2 * as.length)
    (mapState A B F R (preA ++ frameP (mapS out nxt as bs c).1 ++ false :: restA) as.length (mapS out nxt as bs c).2 σ)
    (by simp [mapState, hR]) hRc
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  unfold mapState
  refine WState.eq ?_ rfl ?_ rfl
  · funext j
    simp only [WState.seth_sh, WState.setv_sh, WState.sets_sh, Function.update_apply]
    by_cases hjB : j = B
    · subst hjB; simp
    · by_cases hjA : j = A
      · subst hjA; simp [hjB]
      · simp [hjA, hjB]
  · funext j
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases hjR : j = R
    · subst hjR; simp [Ne.symm hFR, hR]
    · simp [hjR]

end NearCubicWires.WireExponent3_5.FinalPass.Tm
