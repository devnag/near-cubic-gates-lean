import Proof.Gates.Recovery.HTParts
import Proof.Gates.Recovery.CaseOneSem

/-!
# The Case 1 machine, part 1: the cyclic table loop

Paper v2 §11.5 (Case 1 (i) `X_z`, Case 1 (iii) `O*`) and §11.6 ("run the general amplifier"): the amplifier reads the
complete truth table of the hard function, which for both Case 1 functions is a table `w` read cyclically
(`CaseOneSem.table_cycFn`). `cycW` writes it: `k` rounds, each reading the next marked cell of the framed `w` on the stream
`W` and appending `marks [w_p]` to the stream `X`; at the frame end the head of `W` returns to the start (by the
position counter `SC`). `cycW_spec`: after `k` rounds from cell `p`, `X` has gained `marks (cycFrom w p k)` and the head
of `W` sits at cell `(p + k) mod |w|` — it never reads past the first frame of `W`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.CaseOneMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off rtb_off0)

/-! ## Lists -/

/-- `k` entries of `wl` read cyclically from position `p`. -/
def cycFrom (wl : List Bool) (p k : ℕ) : List Bool := (List.range k).map fun i => wl.getD ((p + i) % wl.length) false

theorem cycFrom_length (wl : List Bool) (p k : ℕ) : (cycFrom wl p k).length = k := by simp [cycFrom]

theorem cycFrom_succ (wl : List Bool) (p k : ℕ) :
    cycFrom wl p (k + 1) = wl.getD (p % wl.length) false :: cycFrom wl ((p + 1) % wl.length) k := by
  apply List.ext_getElem
  · simp [cycFrom]
  · intro i h1 h2
    cases i with
    | zero => simp [cycFrom]
    | succ i =>
      have hm : ((p + 1) % wl.length + i) % wl.length = (p + (i + 1)) % wl.length := by
        rw [Nat.mod_add_mod]; congr 1; ring
      simp only [cycFrom, List.getElem_map, List.getElem_range, List.getElem_cons_succ]
      rw [hm]

theorem cycFrom_zero_eq (wl : List Bool) (K : ℕ) : cycFrom wl 0 K = CaseOneSem.cycList wl K := by
  simp [cycFrom, CaseOneSem.cycList]

theorem marks_cons (b : Bool) (l : List Bool) : marks (b :: l) = true :: b :: marks l := by simp [marks]

theorem marks_length (l : List Bool) : (marks l).length = 2 * l.length := by
  induction l with
  | nil => simp [marks]
  | cons b l ih => rw [marks_cons]; simp [ih]; ring

theorem frame_eq_marks (l : List Bool) : frame l = marks l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [marks_cons]; simp [frame, ih]

theorem rd_mark (wl rest : List Bool) : ∀ p, p < wl.length →
    readTapeBit (marks wl ++ false :: rest) (2 * p) = true := by
  induction wl with
  | nil => intro p hp; simp at hp
  | cons b wl ih =>
    intro p hp
    cases p with
    | zero => rw [marks_cons]; rfl
    | succ p =>
      rw [marks_cons, show 2 * (p + 1) = 2 * p + 1 + 1 by ring]
      simp only [List.cons_append, readTapeBit, List.getD_cons_succ]
      exact ih p (by simp at hp; omega)

theorem rd_bit (wl rest : List Bool) : ∀ p, p < wl.length →
    readTapeBit (marks wl ++ false :: rest) (2 * p + 1) = wl.getD p false := by
  induction wl with
  | nil => intro p hp; simp at hp
  | cons b wl ih =>
    intro p hp
    cases p with
    | zero => rw [marks_cons]; rfl
    | succ p =>
      rw [marks_cons, show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring]
      simp only [List.cons_append, readTapeBit, List.getD_cons_succ]
      exact ih p (by simp at hp; omega)

theorem rd_end (wl rest : List Bool) : readTapeBit (marks wl ++ false :: rest) (2 * wl.length) = false := by
  rw [show 2 * wl.length = (marks wl).length by rw [marks_length], rtb_off0]
  rfl

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Positioned appends -/

/-- Append `u` to `X` and put the head of `W` and the counter `SC` at `h`. -/
def pos (W X : Fin (ns + 1)) (opX SC : Fin nr) (σ : WState ns nr) (u : List Bool) (h : ℕ) : WState ns nr :=
  ((appendO σ X opX u).seth W h).setv SC h

variable {W X : Fin (ns + 1)} {opX SC rK : Fin nr}

theorem pos_pos (hWX : W ≠ X) (hOS : opX ≠ SC) (σ : WState ns nr) (u u' : List Bool) (h h' : ℕ) :
    pos W X opX SC (pos W X opX SC σ u h) u' h' = pos W X opX SC σ (u ++ u') h' := by
  apply WState.eq
  · funext j
    by_cases j1 : j = W
    · subst j1; simp [pos, appendO, Function.update_apply, hWX]
    · by_cases j2 : j = X
      · subst j2; simp [pos, appendO, Function.update_apply, j1]; ring
      · simp [pos, appendO, Function.update_apply, j1, j2]
  · funext j
    by_cases j2 : j = X
    · subst j2; simp [pos, appendO, Function.update_apply, Ne.symm hWX]
    · simp [pos, appendO, Function.update_apply, j2]
  · funext r
    by_cases r1 : r = SC
    · subst r1; simp [pos, appendO, Function.update_apply]
    · by_cases r2 : r = opX
      · subst r2; simp [pos, appendO, Function.update_apply, r1]; ring
      · simp [pos, appendO, Function.update_apply, r1, r2]
  · simp [pos, appendO]

theorem pos_setv (σ : WState ns nr) (u : List Bool) (h : ℕ) (r : Fin nr) (x : ℕ) (h1 : r ≠ opX) (h2 : r ≠ SC) :
    pos W X opX SC (σ.setv r x) u h = (pos W X opX SC σ u h).setv r x := by
  apply WState.eq <;> try rfl
  funext q
  simp only [pos, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
  by_cases q1 : q = SC
  · subst q1; simp [Ne.symm h2]
  · by_cases q2 : q = opX
    · subst q2; simp [q1, Ne.symm h1]
    · simp [q1, q2]

theorem pos_nil (σ : WState ns nr) (h : ℕ) (hW : σ.sh W = h) (hS : σ.val SC = h) :
    pos W X opX SC σ [] h = σ := by
  unfold pos
  rw [appendO_nil σ X opX]
  subst hW
  rw [wseth_same, ← hS, wsetv_same]

/-! ## One round -/

/-- One round: skip the marker, append `marks [b]` for the cell bit `b`, return `W` at the frame end. -/
def cycStep (W X : Fin (ns + 1)) (opX SC : Fin nr) : WM ns nr :=
  .seq (cellE W SC (fun _ => WM.skip)) (.seq (cellE W SC (fun b => emitPair X opX b)) (.ifs W WM.skip (WM.rewind W SC)))

/-- `k = val rK` rounds. -/
def cycW (W X : Fin (ns + 1)) (opX SC rK : Fin nr) : WM ns nr := .whr rK (.seq (.dec rK) (cycStep W X opX SC))

theorem cycStep_spec (hWX : W ≠ X) (hOS : opX ≠ SC) (wl rest : List Bool) (p : ℕ) (hp : p < wl.length)
    (σ : WState ns nr) (hst : σ.st W = marks wl ++ false :: rest) (hsh : σ.sh W = 2 * p) (hSC : σ.val SC = 2 * p)
    (hX : σ.sh X = (σ.st X).length) (hcapO : σ.val opX + 2 ≤ cap) (hcapS : 2 * wl.length + 1 ≤ cap) :
    WExec cap (cycStep W X opX SC) σ
      (pos W X opX SC σ [true, wl.getD p false] (2 * ((p + 1) % wl.length)))
      (33 + if p + 1 < wl.length then 0 else 10 * wl.length) := by
  have x1 := cellE_spec cap hWX hOS (emits_none cap (dst := X) (OP := opX)) σ hX
    (by simp; omega) (by omega)
  set σ1 := adv W X opX SC σ [] 1 with hσ1
  have hb : readTapeBit (σ1.st W) (σ1.sh W) = wl.getD p false := by
    rw [hσ1, adv_st_src hWX, adv_sh_src, hst, hsh]; exact rd_bit wl rest p hp
  have x2 := cellE_spec cap hWX hOS (emits_pair cap (dst := X) (OP := opX)) σ1
    (by rw [hσ1, adv_sh_dst hWX, adv_st_dst]; simp [hX])
    (by rw [hσ1, adv_val_OP hOS]; simp; omega) (by rw [hσ1, adv_val_SC]; omega)
  rw [hb] at x2
  set σ2 := adv W X opX SC σ1 [true, wl.getD p false] 1 with hσ2
  have h2 : σ2 = adv W X opX SC σ [true, wl.getD p false] 2 := by
    rw [hσ2, hσ1, adv_adv hWX hOS]; rfl
  have hst2 : σ2.st W = marks wl ++ false :: rest := by rw [h2, adv_st_src hWX, hst]
  have hsh2 : σ2.sh W = 2 * (p + 1) := by rw [h2, adv_sh_src, hsh]; ring
  have hSC2 : σ2.val SC = 2 * (p + 1) := by rw [h2, adv_val_SC, hSC]; ring
  by_cases hp1 : p + 1 < wl.length
  · have hw : wbit σ2 W = true := by unfold wbit; rw [hst2, hsh2]; exact rd_mark wl rest (p + 1) hp1
    have x3 : WExec cap (.ifs W WM.skip (WM.rewind W SC)) σ2 σ2 1 := WExec.ifsT hw (WExec.skip σ2)
    refine WExec.mono (WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ le_rfl) (by rw [if_pos hp1]; omega)
    rw [Nat.mod_eq_of_lt hp1, h2]
    unfold adv pos
    rw [hsh, hSC]; congr 2 <;> ring
  · have hpL : p + 1 = wl.length := by omega
    have hw : wbit σ2 W = false := by unfold wbit; rw [hst2, hsh2, hpL]; exact rd_end wl rest
    have x4 := wrewind_spec (cap := cap) W SC (2 * wl.length) σ2 (by rw [hSC2, hpL]) (by rw [hSC2]; omega)
    have x3 : WExec cap (.ifs W WM.skip (WM.rewind W SC)) σ2 ((σ2.setv SC 0).seth W (σ2.sh W - 2 * wl.length))
        (5 * (2 * wl.length) + 1 + 1) := WExec.ifsF hw x4
    refine WExec.mono (WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ le_rfl) (by rw [if_neg hp1]; omega)
    rw [hpL, Nat.mod_self, hsh2, hpL, Nat.sub_self, h2]
    unfold adv pos
    apply WState.eq
    · funext j
      by_cases j1 : j = W
      · subst j1; simp [Function.update_apply]
      · simp [Function.update_apply, j1]
    · rfl
    · funext r
      by_cases r1 : r = SC
      · subst r1; simp [Function.update_apply]
      · simp [Function.update_apply, r1]
    · rfl

/-- **The cyclic loop.** -/
theorem cycW_spec (hWX : W ≠ X) (hOS : opX ≠ SC) (hKO : rK ≠ opX) (hKS : rK ≠ SC) (wl rest : List Bool)
    (hcapS : 2 * wl.length + 1 ≤ cap) :
    ∀ (k p : ℕ) (σ : WState ns nr), p < wl.length → σ.st W = marks wl ++ false :: rest → σ.sh W = 2 * p →
      σ.val SC = 2 * p → σ.val rK = k → k ≤ cap → σ.sh X = (σ.st X).length → σ.val opX + 2 * k ≤ cap →
      WExec cap (cycW W X opX SC rK) σ
        ((pos W X opX SC σ (marks (cycFrom wl p k)) (2 * ((p + k) % wl.length))).setv rK 0)
        (k * 50 + 12 * p + 1)
  | 0, p, σ, hp, _, hsh, hSC, hK, _, hX, _ => by
    have e : (pos W X opX SC σ (marks (cycFrom wl p 0)) (2 * ((p + 0) % wl.length))).setv rK 0 = σ := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hp]
      simp only [cycFrom, List.range_zero, List.map_nil, marks, List.flatMap_nil]
      rw [pos_nil σ _ hsh hSC, ← hK, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whrF hK) (by omega)
  | k + 1, p, σ, hp, hst, hsh, hSC, hK, hKc, hX, hO => by
    have e1 := WExec.dec (cap := cap) rK σ (by omega)
    set σ0 := σ.setv rK (σ.val rK - 1) with hσ0
    have hσ0' : σ0 = σ.setv rK k := by rw [hσ0, hK]; rfl
    have e2 := cycStep_spec cap hWX hOS wl rest p hp σ0 (by rw [hσ0']; exact hst) (by rw [hσ0']; exact hsh)
      (by rw [hσ0']; simp [Function.update_apply, Ne.symm hKS, hSC]) (by rw [hσ0']; exact hX)
      (by rw [hσ0']; simp [Function.update_apply, Ne.symm hKO]; omega) hcapS
    set σ1 := pos W X opX SC σ0 [true, wl.getD p false] (2 * ((p + 1) % wl.length)) with hσ1
    have hL : 0 < wl.length := by omega
    have ih := cycW_spec hWX hOS hKO hKS wl rest hcapS k ((p + 1) % wl.length) σ1 (Nat.mod_lt _ hL)
      (by rw [hσ1, hσ0']; simp [pos, appendO, Function.update_apply, hWX, hst])
      (by rw [hσ1]; simp [pos])
      (by rw [hσ1]; simp [pos])
      (by rw [hσ1, hσ0']; simp [pos, appendO, Function.update_apply, hKS, hKO])
      (by omega)
      (by rw [hσ1]; simp [pos, appendO, Function.update_apply, Ne.symm hWX, hσ0', hX])
      (by rw [hσ1, hσ0']; simp [pos, appendO, Function.update_apply, hOS, Ne.symm hOS, hKO, Ne.symm hKO]; omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ le_rfl) (by
      by_cases hp1 : p + 1 < wl.length
      · rw [if_pos hp1, Nat.mod_eq_of_lt hp1]; omega
      · have hpL : p + 1 = wl.length := by omega
        rw [if_neg hp1, hpL, Nat.mod_self]; omega)
    rw [hσ1, pos_pos hWX hOS, hσ0', pos_setv _ _ _ rK k hKO hKS]
    rw [cycFrom_succ, marks_cons]
    have hmod : ((p + 1) % wl.length + k) % wl.length = (p + (k + 1)) % wl.length := by
      rw [Nat.mod_add_mod]; congr 1; ring
    rw [hmod, Nat.mod_eq_of_lt hp]
    apply WState.eq <;> try rfl
    funext r
    by_cases r1 : r = rK
    · subst r1; simp [Function.update_apply]
    · simp [Function.update_apply, r1]

end NearCubicGates.Close.Recovery.CaseOneMachine
