import Proof.Gates.Succinct.Time
import Proof.Gates.Expand.PolyTabPack

/-!
# 𝒱_G, part 12: computing `T_G(L_ν)` from `1^ν`

Paper: lem:succinct-verifier (i): "`T_G(n)` is computable from `n` in `poly(n)` steps"; the weak machine hands
`T_G(L_ν)` in binary to the imported constructor (input 6′ reads `T(n)` in binary). With `T_G(L_ν) = c_G·2^{(k+2)ν}`,
the binary word is `(k+2)ν` zeros followed by the bits of `c_G` (`bits_mul_two_pow`). `twW s a`: from `frame (1^ν)`,
write `ν·s` zeros, then `a.bits` (**`timeWordFn`**, an ordinary word function within `K·(ν+1)` steps).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

theorem bits_mul_two_pow (a : ℕ) (ha : a ≠ 0) : ∀ s, (a * 2 ^ s).bits = List.replicate s false ++ a.bits
  | 0 => by simp
  | s + 1 => by
    rw [pow_succ, show a * (2 ^ s * 2) = 2 * (a * 2 ^ s) by ring, Nat.bit0_bits _ (by positivity),
      bits_mul_two_pow a ha s, List.replicate_succ]
    rfl

/-- Append a constant list to `OUT` (position counter `OP`). -/
def emitList (OUT : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: l => .seq (emitC OUT OP b) (emitList OUT OP l)

theorem emitList_spec (cap : ℕ) (OUT : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (l : List Bool) (σ : WState ns nr), σ.sh OUT = (σ.st OUT).length → σ.val OP + l.length ≤ cap →
      WExec cap (emitList OUT OP l) σ
        (((σ.sets OUT (σ.st OUT ++ l)).seth OUT (σ.sh OUT + l.length)).setv OP (σ.val OP + l.length))
        (8 * l.length)
  | [], σ, _, _ => by
    refine WExec.mono (WExec.cast cap (WExec.skip σ) ?_ le_rfl) (by simp)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = OUT
      · subst hx; simp
      · simp [Function.update_of_ne hx]
    · funext x; by_cases hx : x = OUT
      · subst hx; simp
      · simp [Function.update_of_ne hx]
    · funext q; by_cases hq : q = OP
      · subst hq; simp
      · simp [Function.update_of_ne hq]
  | b :: l, σ, hO, hc => by
    have e1 := emitC_spec cap OUT OP b σ hO (by simp at hc; omega)
    set σ1 := ((σ.sets OUT (σ.st OUT ++ [b])).seth OUT (σ.sh OUT + 1)).setv OP (σ.val OP + 1) with hσ1
    have e2 := emitList_spec cap OUT OP l σ1 (by simp [σ1, hO]) (by simp [σ1] at hc ⊢; omega)
    refine WExec.mono (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) (by simp; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = OUT
      · subst hx; simp [σ1]; ring
      · simp [σ1, Function.update_of_ne hx]
    · funext x; by_cases hx : x = OUT
      · subst hx; simp [σ1]
      · simp [σ1, Function.update_of_ne hx]
    · funext q; by_cases hq : q = OP
      · subst hq; simp [σ1]; ring
      · simp [σ1, Function.update_of_ne hq]

/-- `s` zeros for each `1` of `frame (1^ν)` on `IN`. -/
def twLoop (IN OUT : Fin (ns + 1)) (OP : Fin nr) (s : ℕ) : WM ns nr :=
  .whs IN (.seq (.fwd IN) (.seq (.fwd IN) (emitList OUT OP (List.replicate s false))))

theorem twLoop_spec (cap : ℕ) (IN OUT : Fin (ns + 1)) (hIO : IN ≠ OUT) (OP : Fin nr) (s ν : ℕ) (σ : WState ns nr)
    (hIN : σ.st IN = RepairOrdinary.frame (List.replicate ν true)) (hcap : ν * s + 1 ≤ cap) :
    ∀ m j, j + m = ν →
      WExec cap (twLoop IN OUT OP s)
        (((σ.seth IN (2 * j)).sets OUT (List.replicate (j * s) false) |>.seth OUT (j * s)).setv OP (j * s))
        (((σ.seth IN (2 * ν)).sets OUT (List.replicate (ν * s) false) |>.seth OUT (ν * s)).setv OP (ν * s))
        (m * (8 * s + 6) + 1) := by
  intro m
  unfold twLoop
  induction m with
  | zero =>
    intro j hj; rw [Nat.add_zero] at hj; subst hj
    refine WExec.mono (WExec.whsF ?_) (by omega)
    simp [wbit, Function.update_apply, hIO, hIN, frame_even]
  | succ m ih =>
    intro j hj
    set τ := (((σ.seth IN (2 * j)).sets OUT (List.replicate (j * s) false) |>.seth OUT (j * s)).setv OP (j * s))
      with hτ
    have hb : wbit τ IN = true := by simp [wbit, τ, Function.update_apply, hIO, hIN, frame_even]; omega
    have e1 := WExec.fwd (cap := cap) IN τ
    have e2 := WExec.fwd (cap := cap) IN (τ.seth IN (τ.sh IN + 1))
    have e3 := emitList_spec cap OUT OP (List.replicate s false) ((τ.seth IN (τ.sh IN + 1)).seth IN
      ((τ.seth IN (τ.sh IN + 1)).sh IN + 1)) (by simp [τ, Function.update_apply, Ne.symm hIO])
      (by simp [τ]; nlinarith)
    have ih' := ih (j + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) ih') (by
      simp only [List.length_replicate]; ring_nf; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = IN
      · subst hx; simp [τ, hIO]; ring
      · by_cases hx2 : x = OUT
        · subst hx2; simp [τ, hx]; ring
        · simp [τ, Function.update_of_ne hx, Function.update_of_ne hx2]
    · funext x; by_cases hx2 : x = OUT
      · subst hx2; simp [τ, ← List.replicate_add]; ring_nf
      · simp [τ, Function.update_of_ne hx2]
    · funext q; by_cases hq : q = OP
      · subst hq; simp [τ]; ring
      · simp [τ, Function.update_of_ne hq]

/-- The time-word program: `ν·s` zeros, then the bits of `a` (streams: `0` input, `1` output; one register). -/
def twW (s a : ℕ) : WMX 1 1 := .wm (.seq (twLoop 0 1 0 s) (emitList 1 0 a.bits))

/-- **Computing `T_G(L_ν)`** (paper lem:succinct-verifier (i)): from `1^ν`, the bits of `a·2^{sν}`, within
`(16s + 16|bits a| + 20)·(ν+1)` steps. -/
noncomputable def timeWordFn (s a : ℕ) (ha : a ≠ 0) :
    RepairSource.OrdinaryWordFunction ℕ (fun ν => List.replicate ν true) (fun ν => (a * 2 ^ (s * ν)).bits)
      (fun ν => (16 * s + 16 * a.bits.length + 20) * (ν + 1) ^ 1) :=
  Expand.PolyTab.wordFunction_of_ideal (twW s a) 1 (by decide) (fun ν => ν * s + a.bits.length + 10) (fun _ _ => 0)
    (fun ν => ν * (8 * s + 6) + 8 * a.bits.length + 2)
    (fun ν => by rw [pow_one]; nlinarith)
    (fun ν => by
      refine ⟨rfl, ?_⟩
      set σ := Expand.PolyTab.idealStart 1 1 (List.replicate ν true) (fun _ => 0) with hσ
      have hIN : σ.st 0 = RepairOrdinary.frame (List.replicate ν true) := by simp [σ, Expand.PolyTab.idealStart]
      have h0 : (((σ.seth 0 (2 * 0)).sets 1 (List.replicate (0 * s) false)).seth 1 (0 * s)).setv 0 (0 * s) = σ := by
        refine WState.eq ?_ ?_ ?_ rfl
        · funext x; fin_cases x <;> simp [σ, Expand.PolyTab.idealStart, Function.update_apply]
        · funext x; fin_cases x <;> simp [σ, Expand.PolyTab.idealStart, Function.update_apply]
        · funext q; fin_cases q; simp [σ, Expand.PolyTab.idealStart]
      have e1 := twLoop_spec (ν * s + a.bits.length + 10) 0 1 (by decide) 0 s ν σ hIN (by omega) ν 0 (by omega)
      rw [h0] at e1
      set τ := ((σ.seth 0 (2 * ν)).sets 1 (List.replicate (ν * s) false) |>.seth 1 (ν * s)).setv 0 (ν * s) with hτ
      have e2 := emitList_spec (ν * s + a.bits.length + 10) 1 (0 : Fin 1) a.bits τ (by simp [τ])
        (by simp [τ]; try omega)
      refine ⟨_, WXExec.wm (WExec.mono (WExec.seq e1 e2) (by omega)), ?_⟩
      simp [τ, bits_mul_two_pow a ha, Nat.mul_comm])

end NearCubicGates.Close.Succinct
