import Proof.Gates.CheckedPCPP.WMXReady
import Proof.Gates.ENP.TableSpecParts
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

/-- The prep's word states. -/
abbrev PS := WState 6 7

/-- One marked bit: step past the marker, copy the bit to the raw stream, step past the bit. -/
def unmarkBody : WM 6 7 :=
  .seq (WM.fwdC 0 0) (.seq (.ifs 0 (.wr 2 true) (.wr 2 false)) (.seq (WM.fwdC 2 1) (WM.fwdC 0 0)))

/-- One unary step: `N -= 1`, a `true` on streams `a` and `b`, `K += 1`. -/
def onesBody (N K : Fin 7) (a b : Fin 7) : WM 6 7 :=
  .seq (.dec N) (.seq (.wr a true) (.seq (.fwd a) (.seq (.wr b true) (.seq (.fwd b) (.inc K)))))

/-- **The preparation program** (registers: `0`, `1` graph counters, `2` info counter, `3` = `n`, `4` = `o`,
`5`, `6` unary counters). -/
def prepWM : WM 6 7 :=
  .seq (.whs 0 unmarkBody) <| .seq (WM.rewind 0 0) <| .seq (WM.rewind 2 1) <|
  .seq (WM.readU 1 2 3) <| .seq (WM.readU 1 2 4) <| .seq (WM.rewind 1 2) <|
  .seq (.whr 3 (onesBody 3 5 3 4)) <| .seq (rewind2 3 4 5) <|
  .seq (.whr 4 (onesBody 4 6 5 6)) <| .seq (.wr 6 true) (rewind2 5 6 6)

/-! ## Reading and writing cells -/

theorem rd_past (l : List Bool) (i : ℕ) (h : l.length ≤ i) : readTapeBit l i = false := by
  unfold readTapeBit
  rw [List.getD_eq_default _ _ h]

theorem rd_at (l r : List Bool) (b : Bool) : readTapeBit (l ++ b :: r) l.length = b := by
  unfold readTapeBit
  simp

theorem wr_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] :=
  Streaming.write_append l b

theorem marks_snoc (pre : List Bool) (b : Bool) (rest : List Bool) :
    Streaming.marks (pre ++ b :: rest) = Streaming.marks pre ++ true :: b :: Streaming.marks rest := by
  simp [Streaming.marks]

/-! ## Phase 1: unmarking -/

/-- The state after unmarking the prefix `pre` of `g`. -/
def stA (g info pre : List Bool) : PS :=
  ⟨![2 * pre.length, 0, pre.length, 0, 0, 0, 0], ![Streaming.marks g, info, pre, [], [], [], []],
    ![2 * pre.length, pre.length, 0, 0, 0, 0, 0], false⟩

theorem unmark_loop (cap : ℕ) (g info : List Bool) (hcap : 2 * g.length < cap) :
    ∀ rest pre, pre ++ rest = g →
      WExec cap (.whs 0 unmarkBody) (stA g info pre) (stA g info g) (24 * rest.length + 1)
  | [], pre, h => by
    simp only [List.append_nil] at h
    subst h
    refine WExec.mono (WExec.whsF ?_) (by omega)
    change readTapeBit (Streaming.marks pre) (2 * pre.length) = false
    exact rd_past _ _ (by simp)
  | b :: rest, pre, h => by
    have hlen : pre.length + 1 + rest.length = g.length := by rw [← h]; simp; omega
    have hm : Streaming.marks g = Streaming.marks pre ++ true :: b :: Streaming.marks rest := by
      rw [← h, marks_snoc]
    let σ := stA g info pre
    have h1 := wfwdC_spec cap (0 : Fin 7) (0 : Fin 7) σ (by simp [σ, stA]; omega)
    set σ1 := (σ.seth 0 (σ.sh 0 + 1)).setv 0 (σ.val 0 + 1) with hσ1
    have hb1 : wbit σ1 0 = b := by
      simp only [wbit, σ1, σ, stA, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
        Function.update_self]
      simp only [Matrix.cons_val_zero, hm]
      have := rd_at (Streaming.marks pre ++ [true]) (Streaming.marks rest) b
      simpa [Streaming.marks_length, List.append_assoc] using this
    have h2 : WExec cap (.ifs 0 (.wr 2 true) (.wr 2 false)) σ1
        (σ1.sets 2 (writeTapeBit (σ1.st 2) (σ1.sh 2) b)) 2 := by
      cases b
      · exact WExec.ifsF hb1 (WExec.wr 2 false σ1)
      · exact WExec.ifsT hb1 (WExec.wr 2 true σ1)
    set σ2 := σ1.sets 2 (writeTapeBit (σ1.st 2) (σ1.sh 2) b) with hσ2
    have h3 := wfwdC_spec cap (2 : Fin 7) (1 : Fin 7) σ2 (by simp [σ2, σ1, σ, stA]; omega)
    set σ3 := (σ2.seth 2 (σ2.sh 2 + 1)).setv 1 (σ2.val 1 + 1) with hσ3
    have h4 := wfwdC_spec cap (0 : Fin 7) (0 : Fin 7) σ3 (by simp [σ3, σ2, σ1, σ, stA]; omega)
    have ih := unmark_loop cap g info hcap rest (pre ++ [b]) (by rw [← h]; simp)
    have e : (σ3.seth 0 (σ3.sh 0 + 1)).setv 0 (σ3.val 0 + 1) = stA g info (pre ++ [b]) := by
      apply WState.eq
      · funext j; fin_cases j <;> simp [σ3, σ2, σ1, σ, stA] <;> omega
      · funext j; fin_cases j <;> simp [σ3, σ2, σ1, σ, stA, wr_end]
      · funext j; fin_cases j <;> simp [σ3, σ2, σ1, σ, stA] <;> omega
      · rfl
    have hbody : WExec cap unmarkBody σ (stA g info (pre ++ [b])) 20 := by
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) e (by omega)
    have hb0 : wbit σ 0 = true := by
      change readTapeBit (Streaming.marks g) (2 * pre.length) = true
      rw [hm]
      have := rd_at (Streaming.marks pre) (b :: Streaming.marks rest) true
      simpa [Streaming.marks_length] using this
    refine WExec.mono (WExec.whsT hb0 hbody ih) ?_
    simp
    omega

/-! ## Phase 3: the unary words -/

/-- The state while writing `1^n` on streams `3`, `4` (`j` written). -/
def stN (g info : List Bool) (n o j : ℕ) : PS :=
  ⟨![0, 0, 0, j, j, 0, 0], ![Streaming.marks g, info, g, List.replicate j true, List.replicate j true, [], []],
    ![0, 0, 0, n - j, o, j, 0], false⟩

/-- The state while writing `1^o` on streams `5`, `6` (`j` written). -/
def stO (g info : List Bool) (n o j : ℕ) : PS :=
  ⟨![0, 0, 0, 0, 0, j, j], ![Streaming.marks g, info, g, List.replicate n true, List.replicate n true,
      List.replicate j true, List.replicate j true], ![0, 0, 0, 0, o - j, 0, j], false⟩

theorem rep_snoc (j : ℕ) : writeTapeBit (List.replicate j true) j true = List.replicate (j + 1) true := by
  have := wr_end (List.replicate j true) true
  rw [List.length_replicate] at this
  rw [this, List.replicate_succ']

theorem onesN_loop (cap : ℕ) (g info : List Bool) (n o : ℕ) (hcap : n < cap) :
    ∀ k j, j + k = n → WExec cap (.whr 3 (onesBody 3 5 3 4)) (stN g info n o j) (stN g info n o n) (16 * k + 1)
  | 0, j, h => by
    simp only [Nat.add_zero] at h
    subst h
    refine WExec.mono (WExec.whrF ?_) (by omega)
    simp [stN]
  | k + 1, j, h => by
    let σ := stN g info n o j
    have h1 := WExec.dec (cap := cap) (3 : Fin 7) σ (by simp [σ, stN]; omega)
    set σ1 := σ.setv 3 (σ.val 3 - 1) with hσ1
    have h2 := WExec.wr (cap := cap) (3 : Fin 7) true σ1
    set σ2 := σ1.sets 3 (writeTapeBit (σ1.st 3) (σ1.sh 3) true) with hσ2
    have h3 := WExec.fwd (cap := cap) (3 : Fin 7) σ2
    set σ3 := σ2.seth 3 (σ2.sh 3 + 1) with hσ3
    have h4 := WExec.wr (cap := cap) (4 : Fin 7) true σ3
    set σ4 := σ3.sets 4 (writeTapeBit (σ3.st 4) (σ3.sh 4) true) with hσ4
    have h5 := WExec.fwd (cap := cap) (4 : Fin 7) σ4
    set σ5 := σ4.seth 4 (σ4.sh 4 + 1) with hσ5
    have h6 := WExec.inc (cap := cap) (5 : Fin 7) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, σ, stN]; omega)
    have e : σ5.setv 5 (σ5.val 5 + 1) = stN g info n o (j + 1) := by
      apply WState.eq
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stN]
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stN, rep_snoc]
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stN] <;> omega
      · rfl
    have hbody : WExec cap (onesBody 3 5 3 4) σ (stN g info n o (j + 1)) 13 :=
      WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6))))) e (by omega)
    have ih := onesN_loop cap g info n o hcap k (j + 1) (by omega)
    refine WExec.mono (WExec.whrT ?_ hbody ih) (by omega)
    simp [σ, stN]
    omega

theorem onesO_loop (cap : ℕ) (g info : List Bool) (n o : ℕ) (hcap : o < cap) :
    ∀ k j, j + k = o → WExec cap (.whr 4 (onesBody 4 6 5 6)) (stO g info n o j) (stO g info n o o) (16 * k + 1)
  | 0, j, h => by
    simp only [Nat.add_zero] at h
    subst h
    refine WExec.mono (WExec.whrF ?_) (by omega)
    simp [stO]
  | k + 1, j, h => by
    let σ := stO g info n o j
    have h1 := WExec.dec (cap := cap) (4 : Fin 7) σ (by simp [σ, stO]; omega)
    set σ1 := σ.setv 4 (σ.val 4 - 1) with hσ1
    have h2 := WExec.wr (cap := cap) (5 : Fin 7) true σ1
    set σ2 := σ1.sets 5 (writeTapeBit (σ1.st 5) (σ1.sh 5) true) with hσ2
    have h3 := WExec.fwd (cap := cap) (5 : Fin 7) σ2
    set σ3 := σ2.seth 5 (σ2.sh 5 + 1) with hσ3
    have h4 := WExec.wr (cap := cap) (6 : Fin 7) true σ3
    set σ4 := σ3.sets 6 (writeTapeBit (σ3.st 6) (σ3.sh 6) true) with hσ4
    have h5 := WExec.fwd (cap := cap) (6 : Fin 7) σ4
    set σ5 := σ4.seth 6 (σ4.sh 6 + 1) with hσ5
    have h6 := WExec.inc (cap := cap) (6 : Fin 7) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, σ, stO]; omega)
    have e : σ5.setv 6 (σ5.val 6 + 1) = stO g info n o (j + 1) := by
      apply WState.eq
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stO]
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stO, rep_snoc]
      · funext x; fin_cases x <;> simp [σ5, σ4, σ3, σ2, σ1, σ, stO] <;> omega
      · rfl
    have hbody : WExec cap (onesBody 4 6 5 6) σ (stO g info n o (j + 1)) 13 :=
      WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 h6))))) e (by omega)
    have ih := onesO_loop cap g info n o hcap k (j + 1) (by omega)
    refine WExec.mono (WExec.whrT ?_ hbody ih) (by omega)
    simp [σ, stO]
    omega

/-! ## The info word -/

theorem rd_info_lo (n o k : ℕ) (hk : k < n) : readTapeBit (tInfo n o) k = true := by
  unfold readTapeBit tInfo
  rw [List.getD_append _ _ _ _ (by simpa using hk)]
  simp [hk]

theorem rd_info_mid (n o : ℕ) : readTapeBit (tInfo n o) (0 + n) = false := by
  have := rd_at (List.replicate n true) (List.replicate o true) false
  simpa [tInfo] using this

theorem rd_info_hi (n o k : ℕ) (hk : k < o) : readTapeBit (tInfo n o) (n + 1 + k) = true := by
  unfold readTapeBit tInfo
  have e : List.replicate n true ++ false :: List.replicate o true =
      (List.replicate n true ++ [false]) ++ List.replicate o true := by simp
  rw [e, List.getD_append_right _ _ _ _ (by simp)]
  simp [hk]

theorem rd_info_end (n o : ℕ) : readTapeBit (tInfo n o) (n + 1 + o) = false :=
  rd_past _ _ (by simp [tInfo]; omega)

/-! ## The whole program -/

/-- The prep's start state: the marked graph and the info word, everything else empty and at `0`. -/
def stIn (g info : List Bool) : PS :=
  ⟨fun _ => 0, ![Streaming.marks g, info, [], [], [], [], []], fun _ => 0, false⟩

/-- The prep's end state: the raw graph, `1^n` twice, `1^o`, `1^{o+1}`; every head and register at `0`. -/
def stFin (g : List Bool) (n o : ℕ) : PS :=
  ⟨fun _ => 0, ![Streaming.marks g, tInfo n o, g, List.replicate n true, List.replicate n true,
      List.replicate o true, List.replicate (o + 1) true], fun _ => 0, false⟩

/-- The prep's register cap. -/
def prepCap (len n o : ℕ) : ℕ := 2 * len + n + o + 3

/-- The prep's cost. -/
def prepCost (len n o : ℕ) : ℕ := 40 * (len + n + o) + 60

/-- The state after both graph streams are rewound. -/
def stB (g info : List Bool) : PS :=
  ⟨fun _ => 0, ![Streaming.marks g, info, g, [], [], [], []], fun _ => 0, false⟩

theorem phase1 (cap : ℕ) (g info : List Bool) (hcap : 2 * g.length < cap) :
    WExec cap (.seq (.whs 0 unmarkBody) (.seq (WM.rewind 0 0) (WM.rewind 2 1)))
      (stIn g info) (stB g info) (39 * g.length + 5) := by
  have e0 : stIn g info = stA g info [] := by
    apply WState.eq
    · funext x; fin_cases x <;> simp [stIn, stA]
    · funext x; fin_cases x <;> simp [stIn, stA]
    · funext x; fin_cases x <;> simp [stIn, stA]
    · rfl
  have p1 := unmark_loop cap g info hcap g [] rfl
  have p2 := wrewind_spec cap (0 : Fin 7) (0 : Fin 7) (2 * g.length) (stA g info g) (by simp [stA])
    (by simp [stA] <;> omega)
  set τ := ((stA g info g).setv 0 0).seth 0 ((stA g info g).sh 0 - 2 * g.length) with hτ
  have p3 := wrewind_spec cap (2 : Fin 7) (1 : Fin 7) g.length τ (by simp [τ, stA])
    (by simp [τ, stA] <;> omega)
  have e : (τ.setv 1 0).seth 2 (τ.sh 2 - g.length) = stB g info := by
    apply WState.eq
    · funext x; fin_cases x <;> simp [τ, stA, stB]
    · funext x; fin_cases x <;> simp [τ, stA, stB]
    · funext x; fin_cases x <;> simp [τ, stA, stB]
    · rfl
  rw [e0]
  refine WExec.cast cap (WExec.seq p1 (WExec.seq p2 p3)) e ?_
  omega

/-- Checkpoints of the run. -/
def cpB1 (g info : List Bool) : PS :=
  ⟨![0, 0, g.length, 0, 0, 0, 0], ![Streaming.marks g, info, g, [], [], [], []], ![0, g.length, 0, 0, 0, 0, 0], false⟩
def cpD (g info : List Bool) (n : ℕ) : PS :=
  ⟨![0, n + 1, 0, 0, 0, 0, 0], ![Streaming.marks g, info, g, [], [], [], []], ![0, 0, n + 1, n, 0, 0, 0], false⟩
def cpE (g info : List Bool) (n o : ℕ) : PS :=
  ⟨![0, n + 1 + o + 1, 0, 0, 0, 0, 0], ![Streaming.marks g, info, g, [], [], [], []],
    ![0, 0, n + 1 + o + 1, n, o, 0, 0], false⟩
def cpJ (g info : List Bool) (n o : ℕ) : PS :=
  ⟨![0, 0, 0, 0, 0, o, o], ![Streaming.marks g, info, g, List.replicate n true, List.replicate n true,
      List.replicate o true, List.replicate (o + 1) true], ![0, 0, 0, 0, 0, 0, o], false⟩

/-- **The preparation run** (paper §11.6 stage 2: the formula of `c_T` handed to the SAT search): from the marked graph
and the info word `1^n 0 1^o` to the raw graph, `1^n` twice, `1^o`, `1^{o+1}`, every head and register at `0`. -/
theorem prep_exec (g : List Bool) (n o : ℕ) :
    WExec (prepCap g.length n o) prepWM (stIn g (tInfo n o)) (stFin g n o) (prepCost g.length n o) := by
  set cap := prepCap g.length n o with hcap
  set info := tInfo n o with hinfo
  have e0 : stIn g info = stA g info [] := by
    apply WState.eq
    · funext x; fin_cases x <;> simp [stIn, stA]
    · funext x; fin_cases x <;> simp [stIn, stA]
    · funext x; fin_cases x <;> simp [stIn, stA]
    · rfl
  have hA := unmark_loop cap g info (by simp [cap, prepCap]; omega) g [] rfl
  have hB := WExec.cast cap (wrewind_spec cap (0 : Fin 7) (0 : Fin 7) (2 * g.length) (stA g info g) (by simp [stA])
    (by simp [stA, cap, prepCap] <;> omega)) (show _ = cpB1 g info by
      apply WState.eq
      · funext x; fin_cases x <;> simp [stA, cpB1]
      · funext x; fin_cases x <;> simp [stA, cpB1]
      · funext x; fin_cases x <;> simp [stA, cpB1]
      · rfl) le_rfl
  have hC := WExec.cast cap (wrewind_spec cap (2 : Fin 7) (1 : Fin 7) g.length (cpB1 g info) (by simp [cpB1])
    (by simp [cpB1, cap, prepCap] <;> omega)) (show _ = stB g info by
      apply WState.eq
      · funext x; fin_cases x <;> simp [cpB1, stB]
      · funext x; fin_cases x <;> simp [cpB1, stB]
      · funext x; fin_cases x <;> simp [cpB1, stB]
      · rfl) le_rfl
  have hD := WExec.cast cap (wreadU_spec cap (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (by decide) n (stB g info)
    (fun k hk => by simpa [stB, info] using rd_info_lo n o k hk) (by simpa [stB, info] using rd_info_mid n o)
    (by simp [stB, cap, prepCap] <;> omega) (by simp [stB, cap, prepCap] <;> omega)) (show _ = cpD g info n by
      apply WState.eq
      · funext x; fin_cases x <;> simp [stB, cpD]
      · funext x; fin_cases x <;> simp [stB, cpD]
      · funext x; fin_cases x <;> simp [stB, cpD]
      · rfl) le_rfl
  have hE := WExec.cast cap (wreadU_spec cap (1 : Fin 7) (2 : Fin 7) (4 : Fin 7) (by decide) o (cpD g info n)
    (fun k hk => by simpa [cpD, info] using rd_info_hi n o k hk) (by simpa [cpD, info] using rd_info_end n o)
    (by simp [cpD, cap, prepCap] <;> omega) (by simp [cpD, cap, prepCap] <;> omega)) (show _ = cpE g info n o by
      apply WState.eq
      · funext x; fin_cases x <;> simp [cpD, cpE]
      · funext x; fin_cases x <;> simp [cpD, cpE]
      · funext x; fin_cases x <;> simp [cpD, cpE]
      · rfl) le_rfl
  have hF := WExec.cast cap (wrewind_spec cap (1 : Fin 7) (2 : Fin 7) (n + 1 + o + 1) (cpE g info n o)
    (by simp [cpE]) (by simp [cpE, cap, prepCap] <;> omega)) (show _ = stN g info n o 0 by
      apply WState.eq
      · funext x; fin_cases x <;> simp [cpE, stN]
      · funext x; fin_cases x <;> simp [cpE, stN]
      · funext x; fin_cases x <;> simp [cpE, stN]
      · rfl) le_rfl
  have hG := onesN_loop cap g info n o (by simp [cap, prepCap]; omega) n 0 (by omega)
  have hH := WExec.cast cap (rewind2_spec cap (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (by decide) n (stN g info n o n)
    (by simp [stN]) (by simp [cap, prepCap]; omega)) (show _ = stO g info n o 0 by
      apply WState.eq
      · funext x; fin_cases x <;> simp [stN, stO]
      · funext x; fin_cases x <;> simp [stN, stO]
      · funext x; fin_cases x <;> simp [stN, stO]
      · rfl) le_rfl
  have hI := onesO_loop cap g info n o (by simp [cap, prepCap]; omega) o 0 (by omega)
  have hJ := WExec.cast cap (WExec.wr (cap := cap) (6 : Fin 7) true (stO g info n o o)) (show _ = cpJ g info n o by
      apply WState.eq
      · funext x; fin_cases x <;> simp [stO, cpJ]
      · funext x; fin_cases x <;> simp [stO, cpJ, rep_snoc]
      · funext x; fin_cases x <;> simp [stO, cpJ]
      · rfl) le_rfl
  have hK := WExec.cast cap (rewind2_spec cap (5 : Fin 7) (6 : Fin 7) (6 : Fin 7) (by decide) o (cpJ g info n o)
    (by simp [cpJ]) (by simp [cap, prepCap]; omega)) (show _ = stFin g n o by
      apply WState.eq
      · funext x; fin_cases x <;> simp [cpJ, stFin]
      · funext x; fin_cases x <;> simp [cpJ, stFin, info]
      · funext x; fin_cases x <;> simp [cpJ, stFin]
      · rfl) le_rfl
  rw [e0]
  refine WExec.mono (WExec.seq hA (WExec.seq hB (WExec.seq hC (WExec.seq hD (WExec.seq hE (WExec.seq hF
    (WExec.seq hG (WExec.seq hH (WExec.seq hI (WExec.seq hJ hK)))))))))) ?_
  simp only [prepCost, List.length_nil, Nat.sub_zero]
  omega

end NearCubicGates.Close.ENP.TableSearch
