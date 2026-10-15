import Proof.Gates.Setup.PhaseD4

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_nil)
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

theorem length_le_flatMap {α : Type} (f : α → List Bool) (h : ∀ a, 1 ≤ (f a).length) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length
  | [] => by simp
  | a :: l => by
    have := length_le_flatMap f h l
    have := h a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- The code length is at most the supports record's length (every row is a nonempty word). -/
theorem codeLength_le_supports (P : ThreeQueryPCPP) (q : ℕ) : P.code.length q ≤ (supportsWord P.code q).length := by
  unfold supportsWord
  have := length_le_flatMap (fun j : Fin (P.code.length q) =>
    Interfaces.listWord natWord ((canonList (P.code.support q j)).map Fin.val)) (fun j => by
      simp only [Interfaces.listWord, List.length_append]
      have : (natWord ((canonList (P.code.support q j)).map Fin.val).length).length =
          2 * natBitLength ((canonList (P.code.support q j)).map Fin.val).length + 1 := by simp
      omega) (List.finRange (P.code.length q))
  simpa using this

/-- The spare stream used as the row scan's (empty) output. -/
def sSP (D : SetupData s P g) : Fin (nsW D + 1) := fixS D 10 (by decide)

/-- **Phase D.** -/
def phD (D : SetupData s P g) : WMX (nsW D) nrW :=
  .seq (regsP (kB D D.cf.pOut) (kB D D.cf.rOut) (kB D D.cf.cOut) g.clauseDegree)
  (.seq (trW (sWT D) (sCW D)) (.seq (rowsW (sSUP D)) (.seq (hdW (sVI D)) (.wm (WM.clear rBs)))))

section Final
variable (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
  (B : Outer.OuterGuess (width s g N))

/-- The state after phase D, from the ideal state `ι` after phase C. -/
def finalSt (ι : WState (nsW D) nrW) : WState (nsW D) nrW :=
  appendO (((((regsSt ι (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits
      (width s g N + P.code.length (width s g N)) (clauseWidth g.clauseDegree (width s g N))).sets (sCW D)
      (Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)))
        (auxN s P g x B))).seth (sWT D)
      (Codec.circPos (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) (auxN s P g x B))).setv 7
      (Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)))
        (auxN s P g x B)).length).setv cA 0 |>.setv 8 (2 * (supportsWord P.code (width s g N)).length))
    (sVI D) 9 (headerOf s P g x B) |>.setv rBs 0

end Final

section Exec
variable (D : SetupData s P g) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
  (B : Outer.OuterGuess (width s g N))

/-- The cost of phase D. -/
def phDCost : ℕ :=
  regsCost (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits (width s g N + P.code.length (width s g N))
    (clauseWidth g.clauseDegree (width s g N)) (width s g N) + 1 +
  (30000 * (setupSize D x bits pad B + 1) ^ 5 + 1 + (100 * ((supportsWord P.code (width s g N)).length + 1) + 1 +
    (WorkerArith.headerCost (10 * setupSize D x bits pad B + 10) + 1 + (3 * setupSize D x bits pad B + 1))))

/-- `setupSize`, unfolded. -/
theorem setupSize_eq : setupSize D x bits pad B = N + pad + D.N0 + width s g N + gadgets s g N +
    ((pcpp s P g x B).proofBits + gadgets s g N) + (pcpp s P g x B).randomBits + (pcpp s P g x B).word.length +
    (supportsWord P.code (width s g N)).length +
    (Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)))
      ((pcpp s P g x B).proofBits + gadgets s g N)).length +
    (mwWord s g N B.src).length + (PCPPNative.descriptor B.src).length + (PCPPNative.descriptor B.pf).length +
    Worker.nu N ^ (g.lenRoot + 1) := rfl

/-- The sizes bounded by `setupSize`. -/
theorem size_facts :
    (pcpp s P g x B).proofBits ≤ setupSize D x bits pad B ∧ (pcpp s P g x B).randomBits ≤ setupSize D x bits pad B ∧
    width s g N ≤ setupSize D x bits pad B ∧ gadgets s g N ≤ setupSize D x bits pad B ∧
    auxN s P g x B ≤ setupSize D x bits pad B ∧
    (supportsWord P.code (width s g N)).length ≤ setupSize D x bits pad B ∧
    (Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)))
      (auxN s P g x B)).length ≤ setupSize D x bits pad B ∧
    N ≤ setupSize D x bits pad B ∧ (guessWord N bits pad).length ≤ setupSize D x bits pad B ∧
    P.code.length (width s g N) ≤ setupSize D x bits pad B := by
  have hL := codeLength_le_supports P (width s g N)
  have hw : (guessWord N bits pad).length = N / 16 + pad := by
    simp [guessWord, prefixBits_length]
  rw [setupSize_eq]
  unfold auxN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem base_le_size : baseOf g (nu N) ≤ setupSize D x bits pad B := by
  rw [setupSize_eq]; unfold baseOf; omega

theorem regE_val (i : Fin 40) : (regE i).val = i.val := rfl

/-- The zero registers after `regsP` (all but `R 6`, `N`, `M`, `rb`, `cl`, `sysCount`, the loop counter, `proofBits`,
`cA`). -/
theorem regs_zero (ι : WState (nsW D) nrW) (hι : AfterC D x bits pad B ι) (pb rb sc cl : ℕ) (r : Fin nrW)
    (h6 : r.val ≠ 6) (h4 : r.val < 40 ∨ (47 < r.val ∧ r.val ≠ 111)) (h79 : r.val ≠ 79) :
    (regsSt ι pb rb sc cl).val r = 0 := by
  have n1 : r ≠ cA := fin_ne_of_val (by show r.val ≠ 79; omega)
  have n2 : r ≠ rLC := fin_ne_of_val (by show r.val ≠ 46; omega)
  have n3 : r ≠ rM := fin_ne_of_val (by show r.val ≠ 41; omega)
  have n4 : r ≠ rCL := fin_ne_of_val (by show r.val ≠ 43; omega)
  have n5 : r ≠ rSC := fin_ne_of_val (by show r.val ≠ 44; omega)
  have n6 : r ≠ rRB := fin_ne_of_val (by show r.val ≠ 42; omega)
  have n7 : r ≠ rPB := fin_ne_of_val (by show r.val ≠ 47; omega)
  have n8 : r ≠ regE 6 := fin_ne_of_val (by show r.val ≠ 6; omega)
  have n9 : r ≠ rN := fin_ne_of_val (by show r.val ≠ 40; omega)
  have n10 : r ≠ rBs := fin_ne_of_val (by show r.val ≠ 111; omega)
  simp only [regsSt, WState.setv_val, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, if_false]
  rw [hι.val]; simp [n8, n9, n10]

theorem aT_range : ∀ i : Fin 18, i ≠ 6 → (80 ≤ (aT i).val ∧ (aT i).val < 96) ∨ (aT i).val = 7 := by decide

theorem phD1 (cap : ℕ) (hcap : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterC D x bits pad B ι) :
    WXExec cap (regsP (kB D D.cf.pOut) (kB D D.cf.rOut) (kB D D.cf.cOut) g.clauseDegree) ι
      (regsSt ι (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits (width s g N + P.code.length (width s g N))
        (clauseWidth g.clauseDegree (width s g N)))
      (regsCost (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits (width s g N + P.code.length (width s g N))
        (clauseWidth g.clauseDegree (width s g N)) (width s g N)) := by
  obtain ⟨hpb, hrb, hq, hM, -, -, -, -, -, hL⟩ := size_facts D x bits pad B
  have hcap' : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap := hcap
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have hcw0 : ι.st (kB D D.cf.cOut) = marks (natWord (width s g N + P.code.length (width s g N))) ++
      RepairOrdinary.frame (encodeBooleanCircuit (checkedCircuit P.code (Worker.substituted s g x B)).D).bits := by
    rw [hι.cw, checkedWord_eq, frame_append_marks]; rfl
  refine regs_exec (cap := cap) (kB D D.cf.pOut) (kB D D.cf.rOut) (kB D D.cf.cOut) g.clauseDegree (width s g N)
    (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits _ _ ι hι.pb (hsh _ (fin_ne_of_val (by simp; omega)))
    hι.rb (hsh _ (fin_ne_of_val (by simp; omega))) hcw0 (hsh _ (fin_ne_of_val (by simp; omega)))
    (by rw [hι.val]; simp)
    (fun r h1 h2 h3 => by
      rw [hι.val]
      have h6 : r ≠ regE 6 := fin_ne_of_val (by rw [regE_val]; simp; omega)
      have hB : r ≠ rBs := fin_ne_of_val (by show r.val ≠ 111; omega)
      simp [h6, h3, hB]) ?_
  have h1 : 2 ^ clauseWidth g.clauseDegree (width s g N) + width s g N + (pcpp s P g x B).proofBits +
      (pcpp s P g x B).randomBits + (width s g N + P.code.length (width s g N)) + 4 ≤
      6 * (setupSize D x bits pad B + 1) := by
    have : 2 ^ clauseWidth g.clauseDegree (width s g N) = gadgets s g N := rfl
    omega
  have h2 := Nat.pow_le_pow_left h1 2
  have h3 : (6 * (setupSize D x bits pad B + 1)) ^ 2 = 36 * (setupSize D x bits pad B + 1) ^ 2 := by ring
  omega

/-- The state after the register program. -/
abbrev st6 (ι : WState (nsW D) nrW) : WState (nsW D) nrW :=
  regsSt ι (pcpp s P g x B).proofBits (pcpp s P g x B).randomBits (width s g N + P.code.length (width s g N))
    (clauseWidth g.clauseDegree (width s g N))

/-- The circuit stream of the guess. -/
abbrev cwOf : List Bool :=
  Codec.cwPrefix (Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad))) (auxN s P g x B)

/-- The first witness field's position. -/
abbrev cpOf : ℕ := Codec.circPos (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) (auxN s P g x B)

/-- The state after the transcoder. -/
abbrev st7 (ι : WState (nsW D) nrW) : WState (nsW D) nrW :=
  ((((st6 D x B ι).sets (sCW D) (cwOf (P := P) x bits pad B)).seth (sWT D) (cpOf (P := P) x bits pad B)).setv 7
    (cwOf (P := P) x bits pad B).length).setv cA 0

theorem phD2 (cap : ℕ) (hcap : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterC D x bits pad B ι) :
    WXExec cap (trW (sWT D) (sCW D)) (st6 D x B ι) (st7 D x bits pad B ι)
      (30000 * (setupSize D x bits pad B + 1) ^ 5) := by
  obtain ⟨-, -, hq, -, haux, -, hcw, -, hw, -⟩ := size_facts D x bits pad B
  have hcap' : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap := hcap
  have hS2 : setupSize D x bits pad B + 1 ≤ (setupSize D x bits pad B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  refine trW_exec (cap := cap) (sWT D) (sCW D) (fin_ne_of_val (by simp)) (width s g N) (auxN s P g x B)
    (pairEnd (guessWord N bits pad)) (guessWord N bits pad) (st6 D x B ι)
    (by simp [regsSt, hι.wt]) (by simp [regsSt, hι.sh])
    (by simp only [regsSt, WState.setv_st]; exact hι.blank _ (by unfold UntC; simp))
    (by simp only [regsSt, WState.setv_sh]; exact hsh _ (fin_ne_of_val (by simp)))
    (by simp only [regsSt, WState.setv_val, Function.update_apply]; rw [hι.val]; simp (config := { decide := true }))
    (fun i hi => by
      rcases aT_range i hi with h | h
      · exact regs_zero D x bits pad B ι hι _ _ _ _ _ (by omega) (by omega) (by omega)
      · exact regs_zero D x bits pad B ι hι _ _ _ _ _ (by omega) (by omega) (by omega))
    (by simp [regsSt, auxN])
    (regs_zero D x bits pad B ι hι _ _ _ _ _ (by decide) (by decide) (by decide))
    (regs_zero D x bits pad B ι hι _ _ _ _ _ (by decide) (by decide) (by decide))
    (setupSize D x bits pad B) haux hq hw hcw (by omega)

/-- The state after the rows scan. -/
abbrev st8 (ι : WState (nsW D) nrW) : WState (nsW D) nrW :=
  (st7 D x bits pad B ι).setv 8 (2 * (supportsWord P.code (width s g N)).length)

theorem st7_val (ι : WState (nsW D) nrW) (r : Fin nrW) (h7 : r ≠ 7) (hA : r ≠ cA) :
    (st7 D x bits pad B ι).val r = (st6 D x B ι).val r := by
  simp [Function.update_apply, h7, hA]

theorem phD3 (cap : ℕ) (hcap : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterC D x bits pad B ι) :
    WXExec cap (rowsW (sSUP D)) (st7 D x bits pad B ι) (st8 D x bits pad B ι)
      (100 * ((supportsWord P.code (width s g N)).length + 1)) := by
  obtain ⟨-, -, -, -, -, hsw, -, -, -, -⟩ := size_facts D x bits pad B
  have hcap' : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap := hcap
  have hS2 : setupSize D x bits pad B + 1 ≤ (setupSize D x bits pad B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have nSC : sSUP D ≠ sCW D := fin_ne_of_val (by unfold sSUP; simp; omega)
  have nSW : sSUP D ≠ sWT D := fin_ne_of_val (by unfold sSUP; simp; omega)
  have nSP : sSUP D ≠ sSP D := fin_ne_of_val (by unfold sSUP sSP fixS; simp; omega)
  have nPC : sSP D ≠ sCW D := fin_ne_of_val (by unfold sSP fixS; simp)
  have nPW : sSP D ≠ sWT D := fin_ne_of_val (by unfold sSP fixS; simp)
  have z : ∀ r : Fin nrW, r.val ≠ 6 → (r.val < 40 ∨ (47 < r.val ∧ r.val ≠ 111)) → r.val ≠ 79 → r ≠ 7 →
      (st7 D x bits pad B ι).val r = 0 := fun r h6 h4 h79 h7 => by
    rw [st7_val D x bits pad B ι r h7 (fin_ne_of_val (by show r.val ≠ 79; omega))]
    exact regs_zero D x bits pad B ι hι _ _ _ _ _ h6 h4 h79
  have hst : (st7 D x bits pad B ι).st (sSUP D) = RepairOrdinary.frame (supportsWord P.code (width s g N)) := by
    simp only [st7, st6, regsSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne nSC]
    exact hι.sup
  have hsh' : (st7 D x bits pad B ι).sh (sSUP D) = 0 := by
    simp only [st7, st6, regsSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne nSW]
    exact hsh _ nSW
  have hd : (st7 D x bits pad B ι).sh (sSP D) = ((st7 D x bits pad B ι).st (sSP D)).length := by
    simp only [st7, st6, regsSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setv_st, WState.seth_st,
      WState.sets_st, Function.update_of_ne nPC, Function.update_of_ne nPW]
    rw [hsh _ nPW, hι.blank _ (by unfold UntC sSP fixS; simp)]; rfl
  exact rowsW_exec (cap := cap) (sSUP D) (sSP D) nSP _ _ hst hsh' hd (z _ (by decide) (by decide) (by decide) (by decide))
    (z _ (by decide) (by decide) (by decide) (by decide)) (z _ (by decide) (by decide) (by decide) (by decide))
    (z _ (by decide) (by decide) (by decide) (by decide)) (by omega)

theorem st8_val (ι : WState (nsW D) nrW) (r : Fin nrW) (h8 : r ≠ 8) (h7 : r ≠ 7) (hA : r ≠ cA) :
    (st8 D x bits pad B ι).val r = (st6 D x B ι).val r := by
  simp [Function.update_apply, h7, hA, h8]

theorem phD4 (cap : ℕ) (hcap : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterC D x bits pad B ι) :
    WXExec cap (hdW (sVI D)) (st8 D x bits pad B ι) (appendO (st8 D x bits pad B ι) (sVI D) 9 (headerOf s P g x B))
      (WorkerArith.headerCost (10 * setupSize D x bits pad B + 10)) := by
  obtain ⟨-, hrb, hq, hM, -, -, -, hN, -, -⟩ := size_facts D x bits pad B
  have hcap' : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap := hcap
  have hS2 : setupSize D x bits pad B + 1 ≤ (setupSize D x bits pad B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcl : clauseWidth g.clauseDegree (width s g N) < gadgets s g N := Nat.lt_two_pow_self
  have hg : gadgets s g N = 2 ^ clauseWidth g.clauseDegree (width s g N) := rfl
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have nVC : sVI D ≠ sCW D := fin_ne_of_val (by simp)
  have nVW : sVI D ≠ sWT D := fin_ne_of_val (by simp)
  have v6 : ∀ r : Fin nrW, r ≠ 8 → r ≠ 7 → r ≠ cA → (st8 D x bits pad B ι).val r = (st6 D x B ι).val r :=
    fun r h8 h7 hA => st8_val D x bits pad B ι r h8 h7 hA
  have hval : ∀ r, ι.val r = if r = regE 6 then width s g N else if r = rN then N
    else if r = rBs then baseOf g (nu N) else 0 := fun r => by rw [hι.val]
  have hbS := base_le_size D x bits pad B
  have e := hdW_exec (cap := cap) (sVI D) (st8 D x bits pad B ι) (10 * setupSize D x bits pad B + 10)
    (by
      simp only [st8, st7, st6, regsSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setv_st,
        WState.seth_st, WState.sets_st, Function.update_of_ne nVC, Function.update_of_ne nVW]
      rw [hsh _ nVW, hι.blank _ (by unfold UntC; simp)]; rfl)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [v6 _ (by decide) (by decide) (by decide)]
         exact regs_zero D x bits pad B ι hι _ _ _ _ _ (by decide) (by decide) (by decide)))
    (by rw [v6 _ (by decide) (by decide) (by decide)]; simp (config := { decide := true }) [regsSt, Function.update_apply, hval, regE]; omega)
    (by rw [v6 _ (by decide) (by decide) (by decide)]; simp (config := { decide := true }) [regsSt, Function.update_apply, hval, regE]; omega)
    (by rw [v6 _ (by decide) (by decide) (by decide)]; simp (config := { decide := true }) [regsSt, Function.update_apply, regE]; omega)
    (by rw [v6 _ (by decide) (by decide) (by decide)]; simp (config := { decide := true }) [regsSt, Function.update_apply, regE]; omega)
    (by rw [v6 _ (by decide) (by decide) (by decide)]; simp (config := { decide := true }) [regsSt, Function.update_apply, regE]; omega)
    (by
      rw [v6 _ (by decide) (by decide) (by decide), regs_zero D x bits pad B ι hι _ _ _ _ _ (by decide) (by decide)
        (by decide)]
      nlinarith)
  refine WXExec.cast cap e ?_ le_rfl
  congr 2
  rw [v6 _ (by decide) (by decide) (by decide), v6 _ (by decide) (by decide) (by decide),
    v6 _ (by decide) (by decide) (by decide), v6 _ (by decide) (by decide) (by decide),
    v6 _ (by decide) (by decide) (by decide)]
  simp (config := { decide := true }) [regsSt, Function.update_apply, hval, regE, headerOf, baseOf]

theorem phD_exec (cap : ℕ) (hcap : 1000000 * (setupSize D x bits pad B + 1) ^ 2 ≤ cap) (ι : WState (nsW D) nrW)
    (hι : AfterC D x bits pad B ι) :
    WXExec cap (phD D) ι (finalSt D x bits pad B ι) (phDCost D x bits pad B) := by
  have hbS := base_le_size D x bits pad B
  have hS2 : setupSize D x bits pad B + 1 ≤ (setupSize D x bits pad B + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hv : (appendO (st8 D x bits pad B ι) (sVI D) 9 (headerOf s P g x B)).val rBs = baseOf g (nu N) := by
    rw [appendO_val, Function.update_of_ne (by decide), st8_val D x bits pad B ι rBs (by decide) (by decide)
      (by decide)]
    simp (config := { decide := true }) only [st6, regsSt, WState.setv_val, Function.update_apply, if_false]
    rw [hι.val]; simp (config := { decide := true })
  have e5 := wclear_spec (cap := cap) rBs (baseOf g (nu N)) _ hv (by rw [hv]; nlinarith)
  refine WXExec.mono (WXExec.seq (phD1 D x bits pad B cap hcap ι hι) (WXExec.seq (phD2 D x bits pad B cap hcap ι hι)
    (WXExec.seq (phD3 D x bits pad B cap hcap ι hι) (WXExec.seq (phD4 D x bits pad B cap hcap ι hι)
      (WXExec.wm e5))))) ?_
  unfold phDCost
  omega

theorem finalSt_st (ι : WState (nsW D) nrW) (i : Fin (nsW D + 1)) (hC : i ≠ sCW D) (hV : i ≠ sVI D) :
    (finalSt D x bits pad B ι).st i = ι.st i := by
  simp [finalSt, regsSt, Function.update_apply, hC, hV]

theorem finalSt_CW (ι : WState (nsW D) nrW) : (finalSt D x bits pad B ι).st (sCW D) = cwOf (P := P) x bits pad B := by
  have : sCW D ≠ sVI D := fin_ne_of_val (by simp)
  simp [finalSt, regsSt, Function.update_apply, this]

theorem finalSt_VI (ι : WState (nsW D) nrW) :
    (finalSt D x bits pad B ι).st (sVI D) = ι.st (sVI D) ++ headerOf s P g x B := by
  have : sVI D ≠ sCW D := fin_ne_of_val (by simp)
  simp [finalSt, regsSt, Function.update_apply, this]

/-- **The end state of phase D reads like the loop-entry state.** -/
theorem final_simW (ι : WState (nsW D) nrW) (hι : AfterC D x bits pad B ι) :
    SimW (LoopEntry D N x bits pad B (finalSt D x bits pad B ι).st) (finalSt D x bits pad B ι) := by
  classical
  have hsh : ∀ i, i ≠ sWT D → ι.sh i = 0 := fun i hi => by rw [hι.sh]; simp [hi]
  have hval : ∀ r, ι.val r = if r = regE 6 then width s g N else if r = rN then N
    else if r = rBs then baseOf g (nu N) else 0 := fun r => by rw [hι.val]
  have nVC : sVI D ≠ sCW D := fin_ne_of_val (by simp)
  have nVW : sVI D ≠ sWT D := fin_ne_of_val (by simp)
  have hVb : ι.st (sVI D) = [] := hι.blank _ (by unfold UntC; simp)
  have hCb : ι.st (sCW D) = [] := hι.blank _ (by unfold UntC; simp)
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · funext i
    simp only [LoopEntry, finalSt, regsSt, appendO_sh, WState.setv_sh, WState.seth_sh, WState.sets_sh,
      Function.update_apply]
    by_cases h1 : i = sVI D
    · subst h1; simp [nVW, hsh _ nVW, hVb]
    · by_cases h2 : i = sWT D
      · subst h2; simp [h1]
      · simp [h1, h2, hsh _ h2]
  · funext r
    by_cases hr : r ∈ ([regE 6, 7, 8, 9, rN, rM, rRB, rCL, rSC, rA, rLC, rPB, cA, rBs] : List (Fin nrW))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [LoopEntry, finalSt, regsSt, Function.update_apply, hval, regE, hVb,
          rowPrefix_supports_length]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h6, h7, h8, h9, hN, hM, hRB, hCL, hSC, hA, hLC, hPB, hcA, hBs⟩ := hr
      have e7 : regE 7 = (7 : Fin nrW) := Fin.ext rfl
      have e8 : regE 8 = (8 : Fin nrW) := Fin.ext rfl
      have e9 : regE 9 = (9 : Fin nrW) := Fin.ext rfl
      simp [LoopEntry, finalSt, regsSt, Function.update_apply, hval, h6, h7, h8, h9, hN, hM, hRB, hCL, hSC, hA, hLC,
        hPB, hcA, hBs, e7, e8, e9]
  · simp [LoopEntry, finalSt, regsSt, hι.cell]
  · show RdEq ((LoopEntry D N x bits pad B (finalSt D x bits pad B ι).st).st i) _
    simp only [LoopEntry]
    by_cases hX : i = sX D
    · subst hX; rw [if_pos rfl, finalSt_st _ _ _ _ _ _ _ (fin_ne_of_val (by simp)) (fin_ne_of_val (by simp)), hι.sx]
      exact RdEq.refl _
    rw [if_neg hX]
    by_cases hB : i = sBW D
    · subst hB; rw [if_pos rfl, finalSt_st _ _ _ _ _ _ _ (fin_ne_of_val (by simp)) (fin_ne_of_val (by simp)), hι.bw]
      exact RdEq.refl _
    rw [if_neg hB]
    by_cases hW : i = sWT D
    · subst hW; rw [if_pos rfl, finalSt_st _ _ _ _ _ _ _ (fin_ne_of_val (by simp)) (fin_ne_of_val (by simp)), hι.wt]
      exact RdEq.refl _
    rw [if_neg hW]
    by_cases hC : i = sCW D
    · subst hC; rw [if_pos rfl, finalSt_CW]; exact RdEq.refl _
    rw [if_neg hC]
    by_cases hV : i = sVI D
    · subst hV; rw [if_pos rfl, finalSt_VI, hVb, List.nil_append]; exact RdEq.refl _
    rw [if_neg hV, finalSt_st _ _ _ _ _ _ _ hC hV]
    by_cases hJ : i = sJ D
    · subst hJ; rw [if_pos rfl, hι.j8]; exact RdEq.refl _
    rw [if_neg hJ]
    by_cases hS : i = sSUP D
    · subst hS; rw [if_pos rfl, hι.sup]; exact RdEq.refl _
    rw [if_neg hS]
    by_cases hF : i = sFL D
    · subst hF; rw [if_pos rfl, hι.fl]; exact RdEq.refl _
    rw [if_neg hF]
    split_ifs with hb
    · rw [hι.blank i (by
        unfold UntC
        have h0 : i.val ≠ 0 := fun e => hX (Fin.ext e)
        have h1 : i.val ≠ 1 := fun e => hB (Fin.ext e)
        have h2 : i.val ≠ 2 := fun e => hW (Fin.ext e)
        omega)]
      exact RdEq.refl _
    · exact RdEq.refl _

end Exec

end

end NearCubicGates.Close.Setup
