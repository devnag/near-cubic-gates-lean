import Proof.Wire_3_5.PrimAsmSymDecP2
import Proof.Wire_3_5.PrimAsmSymFlat

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## The markers -/

section Emit
variable (cap : ℕ) (x : ℕ)

/-- Print `[true]`: overwrite the output's closing `false`, step, close again. -/
def emitT : WM (LNS x) LNR := .seq (.wr (sk x 1) true) (.seq (.fwd (sk x 1)) (.wr (sk x 1) false))

/-- Print `[false]`: step past the output's closing `false`, close again. -/
def emitF : WM (LNS x) LNR := .seq (.fwd (sk x 1)) (.wr (sk x 1) false)

/-- The state after printing `bits` on the output `out ++ [false]`. -/
def markOut (σ : WState (LNS x) LNR) (out bits : List Bool) : WState (LNS x) LNR :=
  (σ.sets (sk x 1) (out ++ bits ++ [false])).seth (sk x 1) (out ++ bits).length

theorem wtb_last (out : List Bool) (b c : Bool) : writeTapeBit (out ++ [c]) out.length b = out ++ [b] := by
  induction out with
  | nil => rfl
  | cons h t ih => simp [writeTapeBit, ih]

theorem wtb_len (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [writeTapeBit, ih]

theorem emitT_spec (σ : WState (LNS x) LNR) (out : List Bool) (h1 : σ.st (sk x 1) = out ++ [false])
    (h2 : σ.sh (sk x 1) = out.length) : WExec cap (emitT x) σ (markOut x σ out [true]) 5 := by
  have e1 := WExec.wr (cap := cap) (sk x 1) true σ
  have e2 := WExec.fwd (cap := cap) (sk x 1) (σ.sets (sk x 1) (writeTapeBit (σ.st (sk x 1)) (σ.sh (sk x 1)) true))
  have e3 := WExec.wr (cap := cap) (sk x 1) false ((σ.sets (sk x 1) (writeTapeBit (σ.st (sk x 1)) (σ.sh (sk x 1))
    true)).seth (sk x 1) ((σ.sets (sk x 1) (writeTapeBit (σ.st (sk x 1)) (σ.sh (sk x 1)) true)).sh (sk x 1) + 1))
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = sk x 1
    · subst hi; simp [markOut, h2]
    · simp [markOut, Function.update_apply, hi]
  · funext i; by_cases hi : i = sk x 1
    · subst hi
      have e : out ++ [true] ++ [false] = writeTapeBit (out ++ [true]) (out ++ [true]).length false :=
        (wtb_len _ _).symm
      simp [markOut, h1, h2, wtb_last]
      rw [show out ++ [true, false] = out ++ [true] ++ [false] by simp, e]
      simp
    · simp [markOut, Function.update_apply, hi]
  · rfl
  · rfl

theorem emitF_spec (σ : WState (LNS x) LNR) (out : List Bool) (h1 : σ.st (sk x 1) = out ++ [false])
    (h2 : σ.sh (sk x 1) = out.length) : WExec cap (emitF x) σ (markOut x σ out [false]) 3 := by
  have e2 := WExec.fwd (cap := cap) (sk x 1) σ
  have e3 := WExec.wr (cap := cap) (sk x 1) false (σ.seth (sk x 1) (σ.sh (sk x 1) + 1))
  refine WExec.cast cap (WExec.seq e2 e3) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = sk x 1
    · subst hi; simp [markOut, h2]
    · simp [markOut, Function.update_apply, hi]
  · funext i; by_cases hi : i = sk x 1
    · subst hi
      have e : out ++ [false] ++ [false] = writeTapeBit (out ++ [false]) (out ++ [false]).length false :=
        (wtb_len _ _).symm
      simp [markOut, h1, h2]
      rw [show out ++ [false, false] = out ++ [false] ++ [false] by simp, e]
      simp
    · simp [markOut, Function.update_apply, hi]
  · rfl
  · rfl

theorem markOut_st (σ : WState (LNS x) LNR) (out bits : List Bool) (k : Fin 161) (hk : k ≠ 1) :
    (markOut x σ out bits).st (sk x k) = σ.st (sk x k) := by
  have : sk x k ≠ sk x 1 := fun e => hk (sk_inj x e)
  simp [markOut, Function.update_apply, this]

theorem markOut_sh (σ : WState (LNS x) LNR) (out bits : List Bool) (k : Fin 161) (hk : k ≠ 1) :
    (markOut x σ out bits).sh (sk x k) = σ.sh (sk x k) := by
  have : sk x k ≠ sk x 1 := fun e => hk (sk_inj x e)
  simp [markOut, Function.update_apply, this]

end Emit

/-! ## The emission by position -/

section Pos
variable (R M : ℕ) (rq : ℕ → ℕ → ℕ → List Bool) (j : ℕ)

theorem symEmit_w0 (hw : j % (R * (M + 3) + 2) = 0) : SymFlat.symEmit R M rq j = [true] := by
  unfold SymFlat.symEmit SymFlat.entryEmit; rw [hw]; rfl

theorem symEmit_wL (h0 : j % (R * (M + 3) + 2) ≠ 0) (hL : ¬ j % (R * (M + 3) + 2) < R * (M + 3) + 1) :
    SymFlat.symEmit R M rq j = [false] := by
  have hlt : j % (R * (M + 3) + 2) < R * (M + 3) + 2 := Nat.mod_lt _ (by omega)
  unfold SymFlat.symEmit SymFlat.entryEmit
  rw [if_neg h0, if_pos (by omega)]

theorem symEmit_v0 (h0 : j % (R * (M + 3) + 2) ≠ 0) (hL : j % (R * (M + 3) + 2) < R * (M + 3) + 1)
    (hv : (j % (R * (M + 3) + 2) - 1) % (M + 3) = 0) : SymFlat.symEmit R M rq j = [true] := by
  unfold SymFlat.symEmit SymFlat.entryEmit SymFlat.rowEmit
  rw [if_neg h0, if_neg (by omega), hv]; rfl

theorem symEmit_vL (h0 : j % (R * (M + 3) + 2) ≠ 0) (hL : j % (R * (M + 3) + 2) < R * (M + 3) + 1)
    (hv : (j % (R * (M + 3) + 2) - 1) % (M + 3) ≠ 0) (hvL : ¬ (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 2) :
    SymFlat.symEmit R M rq j = [false] := by
  have hlt : (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 3 := Nat.mod_lt _ (by omega)
  unfold SymFlat.symEmit SymFlat.entryEmit SymFlat.rowEmit
  rw [if_neg h0, if_neg (by omega), if_neg hv, if_pos (by omega)]

theorem symEmit_req (h0 : j % (R * (M + 3) + 2) ≠ 0) (hL : j % (R * (M + 3) + 2) < R * (M + 3) + 1)
    (hv : (j % (R * (M + 3) + 2) - 1) % (M + 3) ≠ 0) (hvL : (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 2) :
    SymFlat.symEmit R M rq j = rq (j / (R * (M + 3) + 2)) ((j % (R * (M + 3) + 2) - 1) / (M + 3))
      ((j % (R * (M + 3) + 2) - 1) % (M + 3) - 1) := by
  unfold SymFlat.symEmit SymFlat.entryEmit SymFlat.rowEmit
  rw [if_neg h0, if_neg (by omega), if_neg hv, if_neg (by omega)]

end Pos

/-- **The loop's emission at unit `j`**: the SYM tape's unit below `TOT`, empty past it. -/
def unitE (TOT R M : ℕ) (rq : ℕ → ℕ → ℕ → List Bool) (j : ℕ) : List Bool :=
  if j < TOT then SymFlat.symEmit R M rq j else []

/-- A FILTER unit: a request unit of a carrier row (`r < nc`) at target `s = 0`. -/
def IsFiltU (TOT R M nc j : ℕ) : Prop :=
  j < TOT ∧ j % (R * (M + 3) + 2) ≠ 0 ∧ j % (R * (M + 3) + 2) < R * (M + 3) + 1 ∧
    (j % (R * (M + 3) + 2) - 1) % (M + 3) ≠ 0 ∧ (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 2 ∧
    (j % (R * (M + 3) + 2) - 1) / (M + 3) < nc ∧ (j % (R * (M + 3) + 2) - 1) % (M + 3) - 1 = 0

/-- A POP unit: a request unit of a circuit row (`r ≥ nc`). -/
def IsPopU (TOT R M nc j : ℕ) : Prop :=
  j < TOT ∧ j % (R * (M + 3) + 2) ≠ 0 ∧ j % (R * (M + 3) + 2) < R * (M + 3) + 1 ∧
    (j % (R * (M + 3) + 2) - 1) % (M + 3) ≠ 0 ∧ (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 2 ∧
    nc ≤ (j % (R * (M + 3) + 2) - 1) / (M + 3)

/-! ## The branch -/

section Br
variable (cap : ℕ) (W : WalkBankProducer)

/-- `DecOK` is monotone in the pipeline bound. -/
theorem decOK_mono {σ : WState (LNS W.x) LNR} {out e : List Bool} {Bp Bq : ℕ} (h : DecOK cap W σ out e Bp)
    (hle : Bp ≤ Bq) : DecOK cap W σ out e Bq := by
  rcases h with h | ⟨f0, f0h, Pl, e', L, r4, G, off, Mlab, lw, CAP, LL, R, cp, RW, LW, sgn, s, hlabs, hR, he, hb⟩ |
      ⟨f0, f0h, f1, f1h, P, e', L, r4, G, off, Mlab, RW, LW, sample, hR, he, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨f0, f0h, Pl, e', L, r4, G, off, Mlab, lw, CAP, LL, R, cp, RW, LW, sgn, s, hlabs, hR, he,
      le_trans hb hle⟩)
  · exact Or.inr (Or.inr ⟨f0, f0h, f1, f1h, P, e', L, r4, G, off, Mlab, RW, LW, sample, hR, he, le_trans hb hle⟩)

def brW (fb pb : WM (LNS W.x) LNR) : WM (LNS W.x) LNR :=
  .ifr (H 2) (.ifr (H 3) (.ifr (H 6) (.ifr (H 7) (.ifr (H 11) (.ifr (H 19) (.ifr (H 12) .skip fb) pb)
    (emitF W.x)) (emitT W.x)) (emitF W.x)) (emitT W.x)) .skip

/-- **The unit's branch, run**: from the decoded index (`HVals`), the output `out ++ [false]` at `|out|` and both flags
down, `DecOK` with the loop's emission `unitE j`, given the banks' runs on their units. -/
theorem br_spec (fb pb : WM (LNS W.x) LNR) (σ : WState (LNS W.x) LNR) (out w : List Bool)
    (j TOT R M N2 nSt nFlat nc Bf Bp : ℕ) (rq : ℕ → ℕ → ℕ → List Bool)
    (hV : HVals W.x σ j TOT (R * (M + 3) + 2) M N2 nSt nFlat nc)
    (ho : σ.st (sk W.x 1) = out ++ [false]) (hoh : σ.sh (sk W.x 1) = out.length)
    (f0 : σ.st (sk W.x 150) = []) (f0h : σ.sh (sk W.x 150) = 0) (f1 : σ.st (sk W.x 151) = [])
    (f1h : σ.sh (sk W.x 151) = 0) (hw0 : σ.st (sk W.x 0) = frame w) (hj2 : σ.st (sk W.x 2) = List.replicate j true)
    (hj2h : σ.sh (sk W.x 2) = 0)
    (hfs : ∀ e r s, r < nc → s ≠ 0 → rq e r s = [])
    (hF : IsFiltU TOT R M nc j → ∃ τ c, WExec cap fb σ τ c ∧
      DecOK cap W τ out (rq (j / (R * (M + 3) + 2)) ((j % (R * (M + 3) + 2) - 1) / (M + 3)) 0) Bp ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bf)
    (hP : IsPopU TOT R M nc j → ∃ τ c, WExec cap pb σ τ c ∧
      DecOK cap W τ out (rq (j / (R * (M + 3) + 2)) ((j % (R * (M + 3) + 2) - 1) / (M + 3))
        ((j % (R * (M + 3) + 2) - 1) % (M + 3) - 1)) Bp ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bf) :
    ∃ τ c, WExec cap (brW W fb pb) σ τ c ∧ DecOK cap W τ out (unitE TOT R M rq j) Bp ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bf + 12 := by
  have n01 : (0 : Fin 161) ≠ 1 := by decide
  have n21 : (2 : Fin 161) ≠ 1 := by decide
  have n150 : (150 : Fin 161) ≠ 1 := by decide
  have n151 : (151 : Fin 161) ≠ 1 := by decide
  -- a printed marker is `DecOK`
  have mk : ∀ bits : List Bool, DecOK cap W (markOut W.x σ out bits) out bits Bp ∧
      (markOut W.x σ out bits).st (sk W.x 0) = frame w ∧
      (markOut W.x σ out bits).st (sk W.x 2) = List.replicate j true ∧ (markOut W.x σ out bits).sh (sk W.x 2) = 0 :=
    fun bits => ⟨decOK_mono cap W (Or.inl ⟨by rw [markOut_st _ _ _ _ _ n150, f0], by rw [markOut_sh _ _ _ _ _ n150, f0h],
      by rw [markOut_st _ _ _ _ _ n151, f1], by rw [markOut_sh _ _ _ _ _ n151, f1h], by simp [markOut],
      by simp [markOut]⟩) (Nat.zero_le _), by rw [markOut_st _ _ _ _ _ n01, hw0], by rw [markOut_st _ _ _ _ _ n21, hj2],
      by rw [markOut_sh _ _ _ _ _ n21, hj2h]⟩
  -- an empty unit is `DecOK`
  have em : DecOK cap W σ out [] Bp := Or.inl ⟨f0, f0h, f1, f1h, by simp [ho], by simp [hoh]⟩
  have hEU : R * (M + 3) + 2 - 1 = R * (M + 3) + 1 := by omega
  have hM : M + 3 - 1 = M + 2 := by omega
  have v2 := hV.h2; have v3 := hV.h3; have v6 := hV.h6; have v7 := hV.h7; have v11 := hV.h11
  have v12 := hV.h12; have v19 := hV.h19
  rw [hEU] at v6; rw [hM] at v11
  by_cases hT : j < TOT
  · have c2 : σ.val (H 2) ≠ 0 := by rw [v2, if_pos hT]; omega
    by_cases hw : j % (R * (M + 3) + 2) = 0
    · -- the entry's open marker
      have c3 : σ.val (H 3) = 0 := by rw [v3, hw]
      obtain ⟨d, k0, k2, k2h⟩ := mk [true]
      refine ⟨_, _, WExec.ifrT c2 (WExec.ifrF c3 (emitT_spec cap W.x σ out ho hoh)), ?_, k0, k2, k2h, by omega⟩
      unfold unitE; rw [if_pos hT, symEmit_w0 R M rq j hw]; exact d
    · have c3 : σ.val (H 3) ≠ 0 := by rw [v3]; exact hw
      by_cases hL : j % (R * (M + 3) + 2) < R * (M + 3) + 1
      · have c6 : σ.val (H 6) ≠ 0 := by rw [v6, if_pos hL]; omega
        by_cases hv : (j % (R * (M + 3) + 2) - 1) % (M + 3) = 0
        · -- a row's open marker
          have c7 : σ.val (H 7) = 0 := by rw [v7, hv]
          obtain ⟨d, k0, k2, k2h⟩ := mk [true]
          refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrF c7
            (emitT_spec cap W.x σ out ho hoh)))), ?_, k0, k2, k2h, by omega⟩
          unfold unitE; rw [if_pos hT, symEmit_v0 R M rq j hw hL hv]; exact d
        · have c7 : σ.val (H 7) ≠ 0 := by rw [v7]; exact hv
          by_cases hvL : (j % (R * (M + 3) + 2) - 1) % (M + 3) < M + 2
          · have c11 : σ.val (H 11) ≠ 0 := by rw [v11, if_pos hvL]; omega
            by_cases hr : (j % (R * (M + 3) + 2) - 1) / (M + 3) < nc
            · have c19 : σ.val (H 19) ≠ 0 := by rw [v19, if_pos hr]; omega
              by_cases hs : (j % (R * (M + 3) + 2) - 1) % (M + 3) - 1 = 0
              · -- a FILTER unit
                have c12 : σ.val (H 12) = 0 := by rw [v12, hs]
                obtain ⟨τ, c, e, d, k0, k2, k2h, hc⟩ := hF ⟨hT, hw, hL, hv, hvL, hr, hs⟩
                refine ⟨τ, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrT c11
                  (WExec.ifrT c19 (WExec.ifrF c12 e)))))), ?_, k0, k2, k2h, by omega⟩
                unfold unitE; rw [if_pos hT, symEmit_req R M rq j hw hL hv hvL, hs]; exact d
              · -- an empty carrier unit
                have c12 : σ.val (H 12) ≠ 0 := by rw [v12]; exact hs
                refine ⟨σ, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrT c11
                  (WExec.ifrT c19 (WExec.ifrT c12 (WExec.skip σ))))))), ?_, hw0, hj2, hj2h, by omega⟩
                unfold unitE; rw [if_pos hT, symEmit_req R M rq j hw hL hv hvL, hfs _ _ _ hr hs]; exact em
            · -- a POP unit
              have c19 : σ.val (H 19) = 0 := by rw [v19, if_neg hr]
              obtain ⟨τ, c, e, d, k0, k2, k2h, hc⟩ := hP ⟨hT, hw, hL, hv, hvL, by omega⟩
              refine ⟨τ, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrT c11
                (WExec.ifrF c19 e))))), ?_, k0, k2, k2h, by omega⟩
              unfold unitE; rw [if_pos hT, symEmit_req R M rq j hw hL hv hvL]; exact d
          · -- a row's close marker
            have c11 : σ.val (H 11) = 0 := by rw [v11, if_neg hvL]
            obtain ⟨d, k0, k2, k2h⟩ := mk [false]
            refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrT c6 (WExec.ifrT c7 (WExec.ifrF c11
              (emitF_spec cap W.x σ out ho hoh))))), ?_, k0, k2, k2h, by omega⟩
            unfold unitE; rw [if_pos hT, symEmit_vL R M rq j hw hL hv hvL]; exact d
      · -- the entry's close marker
        have c6 : σ.val (H 6) = 0 := by rw [v6, if_neg hL]
        obtain ⟨d, k0, k2, k2h⟩ := mk [false]
        refine ⟨_, _, WExec.ifrT c2 (WExec.ifrT c3 (WExec.ifrF c6 (emitF_spec cap W.x σ out ho hoh))), ?_, k0, k2,
          k2h, by omega⟩
        unfold unitE; rw [if_pos hT, symEmit_wL R M rq j hw hL]; exact d
  · -- padding
    have c2 : σ.val (H 2) = 0 := by rw [v2, if_neg hT]
    refine ⟨σ, _, WExec.ifrF c2 (WExec.skip σ), ?_, hw0, hj2, hj2h, by omega⟩
    unfold unitE; rw [if_neg hT]; exact em

end Br

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
