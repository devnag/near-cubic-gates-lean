import Proof.Gates.Expand.PolyTabPack
import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.FinalPassWordMap
import Proof.Wire_3_5.FinalPassWordAux

/-!
# Ordinary word functions: pulling back, constant output, and branching on an input cell

Generic combinators for actual ordinary programs (`RepairOrdinary.WordFunction`, L `Statement.lean:546`), used by
the top-level construction of input 6 (proof of `thm:short-pcp-ours`: "For `n = 1`, output a zero-input, one-node constant-false
circuit … For `n = 0`, use the same fixed output … Thus one constructor covers every input length"):

* `pull g W`: a word function on `R` is one on `S` along any request map `g : S → R` (same program);
* `constWriter input w`: a program writing the fixed word `w` (a WMX emitter, `wordFunction_of_ideal`);
* `branch j P Q`: given word functions on the requests whose framed input has a `true`, resp. `false`, cell `j`,
  one program first moves the input head to cell `j`, tests it, rewinds, and runs `P`'s or `Q`'s machine on the
  untouched tapes (both output tapes are placed on one output stream). The test reads the actual framed input
  `frame w` (`cellAt j w = (frame w).getD j false`), so the predicate is decided by the machine itself.

Everything is a construction on L's WMX word programs (`Proof/Gates/WordPrograms/WMX.lean`): `.mach` embeds the two
machines, `WXExec.mach_run` docks their runs, and `Expand.PolyTab.wordFunction_of_ideal` packages the program with
its final head resets.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Branch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab

/-! ## Pulling back along a request map -/

/-- The same program serves every request map. -/
def pull {R S : Type} {input output : R → List Bool} {budget : R → ℕ} (g : S → R)
    (W : WordFunction R input output budget) :
    WordFunction S (fun s => input (g s)) (fun s => output (g s)) (fun s => budget (g s)) :=
  ⟨W.program, fun s => W.realizes (g s)⟩

/-! ## Head moves and the emitter -/

variable {ns nr : ℕ}

theorem seth_seth (σ : WState ns nr) (i : Fin (ns + 1)) (x y : ℕ) : (σ.seth i x).seth i y = σ.seth i y := by
  apply WState.eq <;> simp

/-- Move the head of stream `i` right `k` times. -/
def fwdN (i : Fin (ns + 1)) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.fwd i) (fwdN i k)

/-- Move the head of stream `i` left `k` times. -/
def bwdN (i : Fin (ns + 1)) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | k + 1 => .seq (WMX.bwd i) (bwdN i k)

theorem fwdN_exec (cap : ℕ) (i : Fin (ns + 1)) :
    ∀ (k : ℕ) (σ : WState ns nr), WXExec cap (fwdN i k) σ (σ.seth i (σ.sh i + k)) (2 * k)
  | 0, σ => by simpa [fwdN, wseth_same] using WXExec.skip cap σ
  | k + 1, σ => by
    have e := WXExec.seq (WXExec.fwd cap i σ) (fwdN_exec cap i k (σ.seth i (σ.sh i + 1)))
    rw [seth_seth] at e
    simp only [WState.seth_sh, Function.update_self] at e
    exact WXExec.cast cap e (by rw [Nat.add_assoc, Nat.add_comm 1 k]) (by omega)

theorem bwdN_exec (cap : ℕ) (i : Fin (ns + 1)) :
    ∀ (k : ℕ) (σ : WState ns nr), WXExec cap (bwdN i k) σ (σ.seth i (σ.sh i - k)) (2 * k)
  | 0, σ => by simpa [bwdN, wseth_same] using WXExec.skip cap σ
  | k + 1, σ => by
    have e := WXExec.seq (WXExec.bwd cap i σ) (bwdN_exec cap i k (σ.seth i (σ.sh i - 1)))
    rw [seth_seth] at e
    simp only [WState.seth_sh, Function.update_self] at e
    exact WXExec.cast cap e (by rw [Nat.sub_sub, Nat.add_comm 1 k]) (by omega)

/-- Write the word `w` on stream `o` at its end. -/
def emitW (o : Fin (ns + 1)) : List Bool → WMX ns nr
  | [] => WMX.skip
  | b :: bs => .seq (WMX.wr o b) (.seq (WMX.fwd o) (emitW o bs))

theorem emitW_exec (cap : ℕ) (o : Fin (ns + 1)) :
    ∀ (w : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length →
      WXExec cap (emitW o w) σ ((σ.sets o (σ.st o ++ w)).seth o (σ.sh o + w.length)) (4 * w.length)
  | [], σ, _ => by simpa [emitW, wsets_same, wseth_same] using WXExec.skip cap σ
  | b :: bs, σ, hO => by
    have e1 := WXExec.wr cap o b σ
    rw [hO, writeTapeBit_end'] at e1
    let σ1 := σ.sets o (σ.st o ++ [b])
    have e2 := WXExec.fwd cap o σ1
    let σ2 := σ1.seth o (σ1.sh o + 1)
    have e3 := emitW_exec cap o bs σ2 (by simp [σ2, σ1, hO])
    have he := WXExec.seq e1 (WXExec.seq e2 e3)
    have hf : (σ2.sets o (σ2.st o ++ bs)).seth o (σ2.sh o + bs.length) =
        (σ.sets o (σ.st o ++ b :: bs)).seth o (σ.sh o + (b :: bs).length) := by
      apply WState.eq
      · funext i; by_cases h : i = o
        · subst h; simp [σ2, σ1]; omega
        · simp [σ2, σ1, Function.update_of_ne h]
      · funext i; by_cases h : i = o
        · subst h; simp [σ2, σ1]
        · simp [σ2, σ1, Function.update_of_ne h]
      · rfl
      · rfl
    rw [hf] at he
    exact WXExec.cast cap he rfl (by simp; omega)

/-! ## The constant writer -/

/-- **A program writing the fixed word `w`**, whatever its input. -/
noncomputable def constWriter {R : Type} (input : R → List Bool) (w : List Bool) :
    WordFunction R input (fun _ => w) (fun _ => 8 * w.length + 2) :=
  wordFunction_of_ideal (ns := 1) (nr := 0) (emitW 1 w) 1 (by decide) (fun _ => 0) (fun _ _ => 0)
    (fun _ => 4 * w.length) (fun _ => by omega) (fun r => by
      refine ⟨rfl, _, emitW_exec 0 1 w _ (by simp [idealStart]), ?_⟩
      simp [idealStart])

/-! ## Branching on a cell of the framed input -/

/-- The cell `j` of the input tape `frame w`. -/
def cellAt (j : ℕ) (w : List Bool) : Bool := (frame w).getD j false

/-- `p`'s tapes on streams `0, …, |p| − 1`. -/
def tmapP (p q : Program) (j : Fin p.tapeCount) : Fin (p.tapeCount + q.tapeCount + 1) := ⟨j.val, by omega⟩

/-- The common output stream: `p`'s output tape. -/
def outS (p q : Program) : Fin (p.tapeCount + q.tapeCount + 1) := tmapP p q p.outputTape

/-- `q`'s input tape on stream `0`, its output tape on `outS`, its other tapes on streams `|p| + j`. -/
def tmapQ (p q : Program) (j : Fin q.tapeCount) : Fin (p.tapeCount + q.tapeCount + 1) :=
  if j.val = 0 then ⟨0, by omega⟩ else if j = q.outputTape then outS p q else ⟨p.tapeCount + j.val, by omega⟩

theorem tmapP_inj (p q : Program) : Function.Injective (tmapP p q) := by
  intro a b h
  exact Fin.ext (by simpa [tmapP] using congrArg Fin.val h)

theorem outS_val (p q : Program) : (outS p q).val = p.outputTape.val := rfl

theorem tmapQ_val_ne (p q : Program) (j : Fin q.tapeCount) (hj : j.val ≠ 0) : (tmapQ p q j).val ≠ 0 := by
  have h1 := p.outputFresh
  unfold tmapQ
  rw [if_neg hj]
  split_ifs
  · rw [outS_val]; exact h1
  · simp only; omega

theorem tmapQ_inj (p q : Program) : Function.Injective (tmapQ p q) := by
  have hpo := p.outputTape.isLt
  intro a b h
  have hv := congrArg Fin.val h
  by_cases ha : a.val = 0
  · by_cases hb : b.val = 0
    · exact Fin.ext (by omega)
    · exfalso
      have h1 := tmapQ_val_ne p q b hb
      have h0 : (tmapQ p q a).val = 0 := by simp [tmapQ, ha]
      omega
  · by_cases hb : b.val = 0
    · exfalso
      have h1 := tmapQ_val_ne p q a ha
      have h0 : (tmapQ p q b).val = 0 := by simp [tmapQ, hb]
      omega
    · have ea : (tmapQ p q a).val = if a = q.outputTape then p.outputTape.val else p.tapeCount + a.val := by
        unfold tmapQ; rw [if_neg ha]; split_ifs <;> rfl
      have eb : (tmapQ p q b).val = if b = q.outputTape then p.outputTape.val else p.tapeCount + b.val := by
        unfold tmapQ; rw [if_neg hb]; split_ifs <;> rfl
      rw [ea, eb] at hv
      by_cases hao : a = q.outputTape
      · by_cases hbo : b = q.outputTape
        · rw [hao, hbo]
        · rw [if_pos hao, if_neg hbo] at hv
          omega
      · by_cases hbo : b = q.outputTape
        · rw [if_neg hao, if_pos hbo] at hv
          omega
        · rw [if_neg hao, if_neg hbo] at hv
          exact Fin.ext (by omega)

/-- The branching program: move to cell `j`, test, rewind, run `p` or `q`. -/
noncomputable def branchProg (p q : Program) (j : ℕ) : WMX (p.tapeCount + q.tapeCount) 0 :=
  .seq (fwdN 0 j) (.ifs 0 (.seq (bwdN 0 j) (.mach p.machine (tmapP p q)))
    (.seq (bwdN 0 j) (.mach q.machine (tmapQ p q))))

theorem branch_runs {R : Type} {input output : R → List Bool} (bT bF : R → ℕ) (j : ℕ)
    (P : WordFunction {r // cellAt j (input r) = true} (fun r => input r.1) (fun r => output r.1)
      (fun r => bT r.1))
    (Q : WordFunction {r // cellAt j (input r) = false} (fun r => input r.1) (fun r => output r.1)
      (fun r => bF r.1)) (r : R) :
    ∃ τ, WXExec 0 (branchProg P.program Q.program j)
      (idealStart (P.program.tapeCount + Q.program.tapeCount) 0 (input r) (fun _ => 0)) τ
      (4 * j + 4 + bT r + bF r) ∧ τ.st (outS P.program Q.program) = output r := by
  set σ0 := idealStart (P.program.tapeCount + Q.program.tapeCount) 0 (input r) (fun _ => 0) with hσ0
  have hsh : ∀ i, σ0.sh i = 0 := fun _ => rfl
  have e1 := fwdN_exec 0 (0 : Fin (P.program.tapeCount + Q.program.tapeCount + 1)) j σ0
  set σ1 := σ0.seth 0 (σ0.sh 0 + j) with hσ1
  have e2 := bwdN_exec 0 (0 : Fin (P.program.tapeCount + Q.program.tapeCount + 1)) j σ1
  have hσ2 : σ1.seth 0 (σ1.sh 0 - j) = σ0 := by
    rw [hσ1, seth_seth]
    simp only [WState.seth_sh, Function.update_self, hsh, zero_add, Nat.sub_self]
    have := wseth_same σ0 0
    rwa [hsh 0] at this
  rw [hσ2] at e2
  have hbit : wbit σ1 0 = cellAt j (input r) := by
    simp [wbit, hσ1, hσ0, idealStart, cellAt, readTapeBit]
  cases hc : cellAt j (input r)
  · obtain ⟨rc, hrun, hout⟩ := Q.realizes ⟨r, hc⟩
    have hin : (fun k => σ0.st (tmapQ P.program Q.program k)) = Q.program.inputTapes (input r) := by
      funext k
      by_cases hk : k.val = 0
      · simp [hσ0, idealStart, Program.inputTapes, tmapQ, hk]
      · have h1 := tmapQ_val_ne P.program Q.program k hk
        have h2 : tmapQ P.program Q.program k ≠ 0 := fun h => h1 (by rw [h]; rfl)
        simp [hσ0, idealStart, Program.inputTapes, hk, h2]
    rw [← hin] at hrun
    obtain ⟨τ, e3, hd⟩ := WXExec.mach_run 0 (tmapQ_inj P.program Q.program) σ0 (fun _ => rfl) hrun
    have e3' : WXExec 0 (.mach Q.program.machine (tmapQ P.program Q.program)) σ0 τ (bF r) := e3
    refine ⟨τ, WXExec.mono (WXExec.seq e1 (WXExec.ifsF (by rw [hbit]; exact hc) (WXExec.seq e2 e3')))
      (by omega), ?_⟩
    have ho : tmapQ P.program Q.program Q.program.outputTape = outS P.program Q.program := by
      simp [tmapQ, Q.program.outputFresh]
    rw [← ho, hd.st]
    exact hout
  · obtain ⟨rc, hrun, hout⟩ := P.realizes ⟨r, hc⟩
    have hin : (fun k => σ0.st (tmapP P.program Q.program k)) = P.program.inputTapes (input r) := by
      funext k
      simp [hσ0, idealStart, Program.inputTapes, tmapP]
    rw [← hin] at hrun
    obtain ⟨τ, e3, hd⟩ := WXExec.mach_run 0 (tmapP_inj P.program Q.program) σ0 (fun _ => rfl) hrun
    have e3' : WXExec 0 (.mach P.program.machine (tmapP P.program Q.program)) σ0 τ (bT r) := e3
    refine ⟨τ, WXExec.mono (WXExec.seq e1 (WXExec.ifsT (by rw [hbit]; exact hc) (WXExec.seq e2 e3')))
      (by omega), ?_⟩
    rw [outS, hd.st]
    exact hout

/-- **Branching on an input cell.** Word functions on the requests whose framed input has cell `j` equal to `true`,
resp. `false`, give one word function on all requests. -/
noncomputable def branch {R : Type} {input output : R → List Bool} (bT bF : R → ℕ) (j : ℕ)
    (P : WordFunction {r // cellAt j (input r) = true} (fun r => input r.1) (fun r => output r.1)
      (fun r => bT r.1))
    (Q : WordFunction {r // cellAt j (input r) = false} (fun r => input r.1) (fun r => output r.1)
      (fun r => bF r.1)) :
    WordFunction R input output (fun r => 2 * (4 * j + 4 + bT r + bF r) + 2) :=
  wordFunction_of_ideal (branchProg P.program Q.program j) (outS P.program Q.program)
    (by rw [outS_val]; exact P.program.outputFresh) (fun _ => 0) (fun _ _ => 0)
    (fun r => 4 * j + 4 + bT r + bF r) (fun _ => le_rfl) (fun r => ⟨rfl, branch_runs bT bF j P Q r⟩)

end NearCubicGates.Adapters.ShortPCP.Branch
