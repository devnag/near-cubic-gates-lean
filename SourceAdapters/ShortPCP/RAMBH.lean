import SourceAdapters.ShortPCP.RAMSim
import Proof.Foundations.OrdinaryMachine
import Proof.Foundations.OrdinaryRewindCarrier

/-!
# The run of `V` inside `M_n`, both directions (P02c/d)

Paper context: proof of `lem:tm-ram`, “Simulating `V`”, “Idling” and “The verdict”. These lemmas
establish the forward and backward simulation used in Step 1 of the proof of `thm:short-pcp-ours`:
acceptance of the original verifier corresponds to an accepting bounded run of `M_n`.

- `sim_run_accept` (`⇒`): an accepting run of `V` from `C` within `fuel` steps takes `M_n` from `SimAt C c` to the idle
  block in exactly `steps·simLen + accLen` steps, counter advanced by that much, verdict `1`.
- `sim_run_back` (`⇐`): if `M_n`, started at `SimAt C c`, is at an `(out, accept)` instruction `D` steps later, then
  `V` accepts from `C` (some fuel).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

theorem move_apply_le (mv : HeadMove) (h : ℕ) : mv.apply h ≤ h + 1 := by
  cases mv <;> simp [HeadMove.apply]; omega

theorem simLen_pos (V : Verifier) : 1 ≤ simLen V := by unfold simLen; omega

section Pure

variable {M : Ram} (ga gb : ℕ → Option (BitVec M.w))

theorem xstep_pure (X : XState M) (h : IsPureAt X.S) : xstep ga gb X = { X with S := pureSucc X.S } := by
  unfold IsPureAt at h
  unfold xstep pureSucc
  rcases hI : M.instrAt X.S.pc with _ | I
  · simp [hI] at h
  · rw [hI] at h
    cases I <;> simp_all [xexec]

theorem steppable_of_pure (X : XState M) (h : IsPureAt X.S) : Steppable X := by
  unfold IsPureAt at h
  rcases hI : M.instrAt X.S.pc with _ | I
  · simp [hI] at h
  · rw [hI] at h
    refine ⟨I, hI, fun b hb => ?_⟩
    subst hb; exact h

theorem xrun_pure (X : XState M) : ∀ K, (∀ i < K, IsPureAt (pureSucc^[i] X.S)) →
    xrun ga gb X K = { X with S := pureSucc^[K] X.S } ∧ ∀ i < K, Steppable (xrun ga gb X i) := by
  intro K
  induction K with
  | zero => intro _; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ K ih =>
    intro hp
    obtain ⟨h1, h2⟩ := ih (fun i hi => hp i (by omega))
    have hK : IsPureAt (xrun ga gb X K).S := by rw [h1]; exact hp K (by omega)
    refine ⟨?_, fun i hi => ?_⟩
    · rw [xrun_succ', xstep_pure ga gb _ hK, h1, Function.iterate_succ_apply']
    · rcases Nat.lt_or_ge i K with h | h
      · exact h2 i h
      · rw [show i = K by omega]; exact steppable_of_pure _ hK

/-- **A run that steps for `T − 1` steps from the initial state and then sits at `(out, accept)`** is an accepting
valid sequence of `T` configurations (Defs. 6.8, 6.9, 6.13). -/
theorem accepting_valid_of_run (X0 : XState M) (hX0 : X0 = ⟨⟨0, fun _ => some 0⟩, 0, 0, 0⟩) (T : ℕ) (hT : 1 ≤ T)
    (h : Runs ga gb X0 (T - 1) (xrun ga gb X0 (T - 1)))
    (hout : M.instrAt (xrun ga gb X0 (T - 1)).S.pc = some (.out true)) :
    M.AcceptingSeq T (fun i => (xrun ga gb X0 i).S) ∧ M.ValidSeq T (fun i => (xrun ga gb X0 i).S) := by
  have hinit : M.Initial (xrun ga gb X0 0).S := by rw [xrun_zero, hX0]; exact ⟨rfl, fun _ => rfl⟩
  have hstep : ∀ i, i + 1 < T → M.Step (xrun ga gb X0 i).S (xrun ga gb X0 i).mem
      (xrun ga gb X0 (i + 1)).S (xrun ga gb X0 (i + 1)).mem := by
    intro i hi
    rw [xrun_succ']
    exact step_xstep ga gb _ (h.1 i (by omega))
  refine ⟨⟨hinit, hout⟩, fun i hi => ?_, fun i => (xrun ga gb X0 i).mem,
    by show (xrun ga gb X0 0).mem = 0; rw [xrun_zero, hX0], hstep⟩
  unfold Ram.transition
  by_cases hi' : i + 1 < T
  · rw [Nat.mod_eq_of_lt hi', if_pos (Or.inl ⟨_, _, hstep i hi'⟩)]
  · have hi2 : i = T - 1 := by omega
    rw [show (i + 1) % T = 0 by rw [show i + 1 = T by omega, Nat.mod_self]]
    refine if_pos (Or.inr ⟨⟨true, ?_⟩, hinit⟩)
    rw [hi2]; exact hout

end Pure

section BH

variable (V : Verifier) {w n t T : ℕ} (hfit : codeLen V ≤ 2 ^ w)
variable (ga gb : ℕ → Option (BitVec w))

local notation "MM" => mnRam V w n t T hfit

theorem headsFit_of_bound (B : ℕ) (hB : stride V * (B + 1) + V.tapeCount ≤ 2 ^ w)
    (C : Configuration V.tapeCount V.stateCount) (hC : ∀ i, C.heads i ≤ B) : HeadsFit V (w := w) C := by
  intro i
  have h1 : stride V * (C.heads i + 1) ≤ stride V * (B + 1) := Nat.mul_le_mul_left _ (by have := hC i; omega)
  have := i.isLt
  omega

/-- **`⇒`: an accepting run of `V` reaches the idle block.** -/
theorem sim_run_accept (B : ℕ) (hB : stride V * (B + 1) + V.tapeCount ≤ 2 ^ w) (hcl : codeLen V < 2 ^ w)
    (hw : 2 ≤ w) :
    ∀ (fuel : ℕ) (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM)
      (r : ExecutionReceipt V.tapeCount V.stateCount), SimAt V hfit C c Y → (∀ i, C.heads i + fuel ≤ B) →
      runFrom V.machine fuel C = some r → V.accepting r.final.control = true →
      ∃ Y', Runs ga gb Y (r.steps * simLen V + accLen V) Y' ∧ Y'.S.pc = BitVec.ofNat w (idleAddr V) ∧
        Y'.S.regs rCnt = some (BitVec.ofNat w (c + r.steps * simLen V + accLen V)) ∧
        Y'.S.regs rVd = some (BitVec.ofNat w 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro C c Y r hY hb hr hacc
    simp only [runFrom] at hr
    split_ifs at hr with hh
    cases hr
    obtain ⟨Y', h1, h2, h3, h4⟩ := sim_step_acc V hfit ga gb C c Y hY
      (headsFit_of_bound V B hB C (fun i => by have := hb i; omega)) hcl hh hacc
    exact ⟨Y', by simpa using h1, h2, by simpa using h3, h4⟩
  | succ f ih =>
    intro C c Y r hY hb hr hacc
    have hfitC := headsFit_of_bound V B hB C (fun i => by have := hb i; omega)
    by_cases hh : V.machine.halted C.control = true
    · simp only [runFrom, hh, if_true] at hr
      cases hr
      obtain ⟨Y', h1, h2, h3, h4⟩ := sim_step_acc V hfit ga gb C c Y hY hfitC hcl hh hacc
      exact ⟨Y', by simpa using h1, h2, by simpa using h3, h4⟩
    · have hh' : V.machine.halted C.control = false := by simpa using hh
      simp only [runFrom, hh', Bool.false_eq_true, if_false, step] at hr
      rcases hrule : V.machine.rule C.control C.scanned with _ | a
      · simp [hrule] at hr
      · rw [hrule] at hr
        simp only [Option.map_some] at hr
        rcases hsuf : runFrom V.machine f (applyAction C a) with _ | suf
        · simp [hsuf] at hr
        · simp only [hsuf] at hr
          cases hr
          obtain ⟨Y1, r1, hY1⟩ := sim_step_act V hfit ga gb C c Y hY hfitC hcl hw hh' a hrule
          obtain ⟨Y', r2, h2, h3, h4⟩ := ih (applyAction C a) (c + simLen V) Y1 suf hY1
            (fun i => by
              have := move_apply_le (a.move i) (C.heads i); have := hb i
              simp only [applyAction]; omega) hsuf hacc
          refine ⟨Y', ?_, h2, ?_, h4⟩
          · have := r1.trans _ _ r2
            rwa [show simLen V + (suf.steps * simLen V + accLen V) = (suf.steps + 1) * simLen V + accLen V by ring]
              at this
          · rw [h3]; congr 2; ring

theorem not_out_of_runs {X Y : XState MM} {k D : ℕ} (h : Runs ga gb X k Y) (hD : D < k) :
    Ram.instrAt MM (xrun ga gb X D).S.pc ≠ some (.out true) := by
  obtain ⟨I, hI, hno⟩ := h.1 D hD
  rw [hI]; intro h'; exact hno true (Option.some.inj h')

/-- **`⇐`: reaching `(out, accept)` means `V` accepts.** -/
theorem sim_run_back (B : ℕ) (hB : stride V * (B + 1) + V.tapeCount ≤ 2 ^ w) (hcl : codeLen V < 2 ^ w)
    (hw : 2 ≤ w) :
    ∀ (D : ℕ) (C : Configuration V.tapeCount V.stateCount) (c : ℕ) (Y : XState MM), SimAt V hfit C c Y →
      (∀ i, C.heads i + D ≤ B) → Ram.instrAt MM (xrun ga gb Y D).S.pc = some (.out true) →
      ∃ fuel r, runFrom V.machine fuel C = some r ∧ V.accepting r.final.control = true := by
  have hd : deadAddr V < 2 ^ w := by unfold codeLen idleAddr at hcl; omega
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro C c Y hY hb hout
    have hfitC := headsFit_of_bound V B hB C (fun i => by have := hb i; omega)
    -- a dead end contradicts `hout`
    have dead_contra : ∀ k Y', Runs ga gb Y k Y' → Y'.S.pc = BitVec.ofNat w (deadAddr V) → False := by
      intro k Y' hr hpc
      rcases Nat.lt_or_ge D k with hk | hk
      · exact not_out_of_runs V hfit ga gb hr hk hout
      · obtain ⟨j, rfl⟩ : ∃ j, D = k + j := ⟨D - k, by omega⟩
        rw [xrun_add, hr.2] at hout
        obtain ⟨hp, I, hI, hno⟩ := dead_forever V hfit ga gb hd Y' hpc j
        rw [hI] at hout; exact hno true (Option.some.inj hout)
    by_cases hh : V.machine.halted C.control = true
    · by_cases hacc : V.accepting C.control = true
      · exact ⟨0, ⟨C, 0, C.tapeCells⟩, by simp [runFrom, hh], hacc⟩
      · obtain ⟨k, Y', hr, hpc⟩ := sim_step_dead V hfit ga gb C c Y hY hfitC hcl
          (Or.inl ⟨hh, by simpa using hacc⟩)
        exact (dead_contra k Y' hr hpc).elim
    · have hh' : V.machine.halted C.control = false := by simpa using hh
      rcases hrule : V.machine.rule C.control C.scanned with _ | a
      · obtain ⟨k, Y', hr, hpc⟩ := sim_step_dead V hfit ga gb C c Y hY hfitC hcl (Or.inr ⟨hh', hrule⟩)
        exact (dead_contra k Y' hr hpc).elim
      · obtain ⟨Y1, r1, hY1⟩ := sim_step_act V hfit ga gb C c Y hY hfitC hcl hw hh' a hrule
        rcases Nat.lt_or_ge D (simLen V) with hk | hk
        · exact (not_out_of_runs V hfit ga gb r1 hk hout).elim
        · obtain ⟨j, rfl⟩ : ∃ j, D = simLen V + j := ⟨D - simLen V, by omega⟩
          rw [xrun_add, r1.2] at hout
          have hpos := simLen_pos V
          obtain ⟨fuel, r, hr, hacc⟩ := ih j (by omega) (applyAction C a) (c + simLen V) Y1 hY1
            (fun i => by
              have := move_apply_le (a.move i) (C.heads i); have := hb i
              simp only [applyAction]; omega) hout
          refine ⟨fuel + 1, ⟨r.final, r.steps + 1, max C.tapeCells r.peakTapeCells⟩, ?_, hacc⟩
          simp [runFrom, hh', step, hrule, hr]

/-- The idle block of `M_n` as an `IdleSetup` (`lem:tm-ram` and its proof). -/
def mnIdle (hTlt : T < 2 ^ w) (hT16 : 16 ≤ T) (hT8 : 8 ∣ T) (hcl : codeLen V < 2 ^ w) : IdleSetup MM where
  addOp := 0
  cmpOp := 3
  cnt := rCnt
  tmp := rTmp
  vd := rVd
  b := idleAddr V
  T := T
  add_eq := rfl
  cmp_eq := rfl
  cnt_tmp := by simp [reg_eq_iff]
  vd_cnt := by simp [reg_eq_iff]
  vd_tmp := by simp [reg_eq_iff]
  code_eq := fun i hi => code_idle V hfit i (by simpa [idleCode] using hi)
  fits := by unfold codeLen at hcl; show idleAddr V + 17 ≤ 2 ^ w; omega
  T_lt := hTlt
  T_ge := hT16
  T_dvd := hT8

/-- **The idle phase**: entering the idle block at counter `c` (`8 ∣ c`, `c + 16 ≤ T`) with verdict `1`, the run
reaches `(out, accept)` after exactly `T − 1 − c` steps. -/
theorem idle_run (hTlt : T < 2 ^ w) (hT16 : 16 ≤ T) (hT8 : 8 ∣ T) (hcl : codeLen V < 2 ^ w) (hw : 1 ≤ w)
    (Y : XState MM) (c : ℕ) (hpc : Y.S.pc = BitVec.ofNat w (idleAddr V))
    (hcnt : Y.S.regs rCnt = some (BitVec.ofNat w c)) (hvd : Y.S.regs rVd = some (BitVec.ofNat w 1))
    (hc8 : 8 ∣ c) (hc : c + 16 ≤ T) :
    ∃ Y', Runs ga gb Y (T - 1 - c) Y' ∧ Ram.instrAt MM Y'.S.pc = some (.out true) := by
  let I := mnIdle V hfit (n := n) (t := t) hTlt hT16 hT8 hcl
  have hAt : At I I.b c (some (BitVec.ofNat w 1)) Y.S := ⟨hpc, hcnt, hvd⟩
  obtain ⟨hp, hout⟩ := idle_exact_pure I Y.S c _ hAt hc8 hc
  obtain ⟨h1, h2⟩ := xrun_pure ga gb Y (I.T - 1 - c) hp
  have hne : (BitVec.ofNat w 1 : BitVec w) ≠ 0 := one_ne_zero_of (Nat.one_lt_two_pow (by omega))
  refine ⟨_, ⟨h2, h1⟩, ?_⟩
  simp only at hout ⊢
  rw [hout]
  have hw0 : w ≠ 0 := by omega
  simp [hw0]

/-! ## Arithmetic of the counter -/

theorem dvd_initLen (V : Verifier) (n t : ℕ) : 8 ∣ initLen V n t := ⟨3 * n + 3 * t + V.tapeCount + 5, by
  unfold initLen; ring⟩

theorem dvd_simLen (V : Verifier) : 8 ∣ simLen V := by
  unfold simLen simPad; apply Nat.dvd_of_mod_eq_zero; omega

theorem dvd_accLen (V : Verifier) : 8 ∣ accLen V := by
  unfold accLen accPad; apply Nat.dvd_of_mod_eq_zero; omega

/-! ## Words and frames -/

theorem frameFn_congr (n : ℕ) (b b' : ℕ → Bool) (h : ∀ q < n, b q = b' q) : frameFn n b = frameFn n b' := by
  funext j
  unfold frameFn
  by_cases hj : j < 2 * n
  · rw [h (j / 2) (by omega)]
  · simp [hj]

theorem streamBit_wordStream (w : ℕ) (hw : 0 < w) (x : List Bool) (p : ℕ) (hp : (p / w + 1) * w ≤ x.length) :
    streamBit (wordStream w x) 0 p = x.getD p false := by
  unfold streamBit wordStream
  rw [Nat.zero_add, if_pos hp, Option.getD_some, getLsbD_wordOf w x _ _ (Nat.mod_lt _ hw),
    Nat.mul_comm, Nat.div_add_mod]

theorem ceil_mul_ge (t w : ℕ) (hw : 0 < w) : t ≤ (t + w - 1) / w * w := by
  have h := Nat.div_add_mod (t + w - 1) w
  have := Nat.mod_lt (t + w - 1) hw
  rw [Nat.mul_comm] at h
  omega

/-- The bits of the first `k` proper words of a read list, in order. -/
theorem flatten_words_getD {w : ℕ} (hw : 0 < w) : ∀ (k : ℕ) (L : List (Option (BitVec w))),
    (∀ q < k, L.getD q none ≠ none) →
      k * w ≤ ((L.filterMap fun v => v.map Ram.wordBits).flatten).length ∧
      ∀ p < k * w, ((L.filterMap fun v => v.map Ram.wordBits).flatten).getD p false =
        ((L.getD (p / w) none).getD 0).getLsbD (p % w)
  | 0, L, _ => ⟨by simp, fun p hp => absurd hp (by simp)⟩
  | k + 1, [], h => absurd rfl (h 0 (by omega))
  | k + 1, v :: L, h => by
    obtain ⟨W, rfl⟩ : ∃ W, v = some W := Option.ne_none_iff_exists'.mp (by simpa using h 0 (by omega))
    obtain ⟨ih1, ih2⟩ := flatten_words_getD hw k L (fun q hq => by simpa using h (q + 1) (by omega))
    have hlen : (Ram.wordBits W).length = w := by simp [Ram.wordBits]
    simp only [List.filterMap_cons, Option.map_some, List.flatten_cons, List.length_append, hlen]
    refine ⟨by rw [Nat.add_mul, Nat.one_mul]; omega, fun p hp => ?_⟩
    rcases Nat.lt_or_ge p w with hpw | hpw
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hpw)]
      simp [Ram.wordBits, Nat.div_eq_of_lt hpw, Nat.mod_eq_of_lt hpw, List.getD_eq_getElem?_getD, hpw]
    · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact hpw), hlen,
        ih2 (p - w) (by rw [Nat.add_mul, Nat.one_mul] at hp; omega)]
      have e1 : (p - w) / w = p / w - 1 := by
        have := Nat.add_div_right (p - w) hw; rw [Nat.sub_add_cancel hpw] at this; rw [this]; rfl
      have e2 : (p - w) % w = p % w := by
        have := Nat.add_mod_right (p - w) w; rw [Nat.sub_add_cancel hpw] at this; exact this.symm
      rw [e1, e2]
      have h1 : 1 ≤ p / w := (Nat.le_div_iff_mul_le hw).mpr (by omega)
      obtain ⟨d, hd⟩ : ∃ d, p / w = d + 1 := ⟨p / w - 1, by generalize p / w = a at h1 ⊢; omega⟩
      rw [hd]; simp

/-! ## `BH_RAM(M_n)` ⇔ acceptance by `V` -/

/-- The size side conditions of `lem:tm-ram` ("Constants", `lem:tm-ram` and its proof), with `T_n = 2^τ`. -/
structure MnFits (V : Verifier) (w n t τ : ℕ) : Prop where
  w_ge : 2 ≤ w
  code : codeLen V < 2 ^ w
  init : InitFits V w n t
  tau : 1 ≤ τ
  T16 : 16 ≤ 2 ^ τ
  T8 : 8 ∣ 2 ^ τ
  Tlt : 2 ^ τ < 2 ^ w
  heads : stride V * (2 ^ τ + 1) + V.tapeCount ≤ 2 ^ w
  time : initLen V n t + t * simLen V + accLen V + 16 ≤ 2 ^ τ
  wit : (t + w - 1) / w * w ≤ 2 ^ τ

theorem initState_eq (M : Ram) (S : M.Config) (mem : M.Memory) (hS : M.Initial S) (hm : mem = 0) :
    (⟨S, mem, 0, 0⟩ : XState M) = initState M := by
  obtain ⟨hpc, hregs⟩ := hS
  cases S
  simp only at hpc hregs
  subst hpc hm
  simp only [initState, XState.mk.injEq, and_true]
  congr 1
  funext i; exact hregs i

theorem tapes_init (V : Verifier) {w : ℕ} (ga gb : ℕ → Option (BitVec w)) (n t : ℕ) (x : BitInput n)
    (y : BitInput t) (hx : ∀ q (hq : q < n), streamBit ga 0 q = x ⟨q, hq⟩)
    (hy : ∀ q (hq : q < t), streamBit gb 0 q = y ⟨q, hq⟩) :
    initTapes V ga gb n t =
      tapeFn V (initialConfiguration V.machine (V.inputTapes (List.ofFn x) (List.ofFn y))) := by
  funext i j
  simp only [initTapes, tapeFn, initialConfiguration, Verifier.inputTapes]
  split_ifs with h0 h1
  · rw [frame_getD, List.length_ofFn]
    exact congrFun (frameFn_congr n _ _ (fun q hq => by
      rw [hx q hq, List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hq])) j
  · rw [frame_getD, List.length_ofFn]
    exact congrFun (frameFn_congr t _ _ (fun q hq => by
      rw [hy q hq, List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [hq])) j
  · simp

theorem getD_of_prefix {l l' : List Bool} (h : l <+: l') {p : ℕ} (hp : p < l.length) :
    l.getD p false = l'.getD p false := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hp]

/-- **`⇐` of `mn_bhram_iff`** (no promise needed): membership in `BH_RAM(M_n)` gives a `t`-bit witness that `V`
accepts. -/
theorem mn_bhram_back (V : Verifier) (w n t τ : ℕ) (hfit : codeLen V ≤ 2 ^ w) (hF : MnFits V w n t τ)
    (x : BitInput n) (xbar : List Bool) (hxpre : ∀ p (hp : p < n), xbar.getD p false = x ⟨p, hp⟩) :
    (mnRam V w n t (2 ^ τ) hfit).BHRAM xbar τ τ → ∃ y : BitInput t, V.accepts (List.ofFn x) (List.ofFn y) := by
  rintro ⟨-, -, -, wit, -, S, ⟨hinit, hacc⟩, ⟨-, mem, hmem0, hstep⟩, ⟨hconsA, -⟩, -⟩
  have hw : 0 < w := by have := hF.w_ge; omega
  have hT16 := hF.T16
  have hcl := hF.code
  have hd : deadAddr V < 2 ^ w := by unfold codeLen idleAddr at hcl; omega
  set ga := readOracle true S (2 ^ τ) with hga
  set gb := readOracle false S (2 ^ τ) with hgb
  have hxr := valid_eq_xrun (2 ^ τ) S mem hstep
  have hX0 : (⟨S 0, mem 0, 0, 0⟩ : XState (mnRam V w n t (2 ^ τ) hfit)) = initState _ :=
    initState_eq _ _ _ hinit hmem0
  have hout : Ram.instrAt (mnRam V w n t (2 ^ τ) hfit) (xrun ga gb (initState _) ((2 ^ τ) - 1)).S.pc =
      some (.out true) := by
    rw [← hX0, hxr ((2 ^ τ) - 1) le_rfl]; exact hacc
  -- a dead end contradicts `hout`
  have dead_contra : ∀ k Y, Runs ga gb (initState (mnRam V w n t (2 ^ τ) hfit)) k Y →
      Y.S.pc = BitVec.ofNat w (deadAddr V) → False := by
    intro k Y hr hpc
    rcases Nat.lt_or_ge ((2 ^ τ) - 1) k with hk | hk
    · exact not_out_of_runs V hfit ga gb hr hk hout
    · obtain ⟨j, hj⟩ : ∃ j, (2 ^ τ) - 1 = k + j := ⟨(2 ^ τ) - 1 - k, by omega⟩
      rw [hj, xrun_add, hr.2] at hout
      obtain ⟨-, I, hI, hno⟩ := dead_forever V hfit ga gb hd Y hpc j
      rw [hI] at hout; exact hno true (Option.some.inj hout)
  by_cases hok : (∀ q < (n + w - 1) / w, ga q ≠ none) ∧ (∀ q < (t + w - 1) / w, gb q ≠ none)
  · obtain ⟨Y0, r0, hY0⟩ := init_ok V hfit ga gb hF.init hok.1 hok.2
    rcases Nat.lt_or_ge ((2 ^ τ) - 1) (initLen V n t) with hk | hk
    · exact (not_out_of_runs V hfit ga gb r0 hk hout).elim
    · obtain ⟨D, hD⟩ : ∃ D, (2 ^ τ) - 1 = initLen V n t + D := ⟨(2 ^ τ) - 1 - initLen V n t, by omega⟩
      rw [hD, xrun_add, r0.2] at hout
      let x' : BitInput n := fun p => streamBit ga 0 p.val
      let y' : BitInput t := fun p => streamBit gb 0 p.val
      have hsim : SimAt V hfit (initialConfiguration V.machine (V.inputTapes (List.ofFn x') (List.ofFn y')))
          (initLen V n t) Y0 :=
        ⟨hY0.pc, hY0.regCnt, hY0.regSr, fun i => hY0.regH i,
          by rw [hY0.mem, tapes_init V ga gb n t x' y' (fun q _ => rfl) (fun q _ => rfl)]⟩
      obtain ⟨fuel, r, hr, hacc'⟩ := sim_run_back V hfit ga gb (2 ^ τ) hF.heads hcl hF.w_ge D _ _ Y0 hsim
        (fun i => by simp only [initialConfiguration]; omega) hout
      have hxx : x' = x := by
        funext p
        have hL := flatten_words_getD hw ((n + w - 1) / w) (readsUpTo true S ((2 ^ τ) - 1)) hok.1
        rw [readString_eq] at hconsA
        have hp' : p.val < (n + w - 1) / w * w := lt_of_lt_of_le p.isLt (ceil_mul_ge n w hw)
        have e1 := hL.2 p.val hp'
        rw [getD_of_prefix hconsA (lt_of_lt_of_le hp' hL.1), hxpre p.val p.isLt] at e1
        show streamBit ga 0 p.val = x p
        rw [e1]
        simp only [streamBit, Nat.zero_add]
        rfl
      exact ⟨y', fuel, r, by rw [← hxx]; exact hr, hacc'⟩
  · obtain ⟨m, Y, rY, hYpc⟩ := init_bad V hfit ga gb hF.init hok
    exact (dead_contra m Y rY hYpc).elim

/-- **`⇒` of `mn_bhram_iff`**: under the promise, an accepting `t`-bit witness gives `(x̄, 1^τ, 1^τ) ∈ BH_RAM(M_n)`,
with the witness tape `y` padded by zeros to whole words (`lem:tm-ram` and its proof). -/
theorem mn_bhram_fwd (V : Verifier) (w n t τ : ℕ) (hfit : codeLen V ≤ 2 ^ w) (hF : MnFits V w n t τ)
    (x : BitInput n) (xbar : List Bool) (hxpre : ∀ p (hp : p < n), xbar.getD p false = x ⟨p, hp⟩)
    (hxlen : (n + w - 1) / w * w ≤ xbar.length) (hxT : xbar.length ≤ 2 ^ τ)
    (hrun : ∀ y : List Bool, ∃ receipt, run V.machine t (V.inputTapes (List.ofFn x) y) = some receipt) :
    (∃ y : BitInput t, V.accepts (List.ofFn x) (List.ofFn y)) → (mnRam V w n t (2 ^ τ) hfit).BHRAM xbar τ τ := by
  rintro ⟨y, fuel, rr, hrr, hacc⟩
  have hw : 0 < w := by have := hF.w_ge; omega
  obtain ⟨r, hr⟩ := hrun (List.ofFn y)
  have hrr' : r = rr := by
    have e1 := runFrom_moreFuel V.machine fuel t _ rr hrr
    have e2 := runFrom_moreFuel V.machine t fuel _ r hr
    rw [Nat.add_comm] at e2
    exact Option.some.inj (e2.symm.trans e1)
  subst hrr'
  have hsteps : r.steps ≤ t := runFrom_steps_le V.machine t _ r hr
  obtain ⟨wit, hwit⟩ : ∃ wit : List Bool, wit = List.ofFn y ++ List.replicate ((t + w - 1) / w * w - t) false :=
    ⟨_, rfl⟩
  have hwitlen : wit.length = (t + w - 1) / w * w := by
    have := ceil_mul_ge t w hw; simp [hwit]; omega
  obtain ⟨ga, hga⟩ : ∃ ga, ga = wordStream w xbar := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ gb, gb = wordStream w wit := ⟨_, rfl⟩
  have hA : ∀ q < (n + w - 1) / w, ga q ≠ none := by
    intro q hq
    have : (q + 1) * w ≤ (n + w - 1) / w * w := Nat.mul_le_mul_right _ hq
    simp [hga, wordStream, show (q + 1) * w ≤ xbar.length by omega]
  have hB : ∀ q < (t + w - 1) / w, gb q ≠ none := by
    intro q hq
    have : (q + 1) * w ≤ (t + w - 1) / w * w := Nat.mul_le_mul_right _ hq
    simp [hgb, wordStream, show (q + 1) * w ≤ wit.length by omega]
  obtain ⟨Y0, r0, hY0⟩ := init_ok V hfit (T := 2 ^ τ) ga gb hF.init hA hB
  have hx : ∀ q (hq : q < n), streamBit ga 0 q = x ⟨q, hq⟩ := by
    intro q hq
    have h1 : (q / w + 1) * w ≤ xbar.length :=
      le_trans (Nat.mul_le_mul_right _ (div_lt_ceil hw hq)) hxlen
    rw [hga, streamBit_wordStream w hw xbar q h1, hxpre q hq]
  have hy : ∀ q (hq : q < t), streamBit gb 0 q = y ⟨q, hq⟩ := by
    intro q hq
    have h1 : (q / w + 1) * w ≤ wit.length := by
      rw [hwitlen]; exact Nat.mul_le_mul_right _ (div_lt_ceil hw hq)
    rw [hgb, streamBit_wordStream w hw wit q h1, hwit, List.getD_append _ _ _ _ (by simpa using hq),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hq]
  have hsim : SimAt V hfit (initialConfiguration V.machine (V.inputTapes (List.ofFn x) (List.ofFn y)))
      (initLen V n t) Y0 :=
    ⟨hY0.pc, hY0.regCnt, hY0.regSr, fun i => hY0.regH i, hY0.mem.trans (by rw [tapes_init V ga gb n t x y hx hy])⟩
  have htime := hF.time
  obtain ⟨Y1, r1, h1pc, h1cnt, h1vd⟩ := sim_run_accept V hfit ga gb (2 ^ τ) hF.heads hF.code hF.w_ge t _ _ Y0 r
    hsim (fun i => by simp only [initialConfiguration]; unfold initLen at htime; omega) hr hacc
  have hc8 : 8 ∣ initLen V n t + r.steps * simLen V + accLen V :=
    Nat.dvd_add (Nat.dvd_add (dvd_initLen V n t) (Dvd.dvd.mul_left (dvd_simLen V) _)) (dvd_accLen V)
  have hmul : r.steps * simLen V ≤ t * simLen V := Nat.mul_le_mul_right _ hsteps
  obtain ⟨Y2, r2, hout⟩ := idle_run V hfit ga gb hF.Tlt hF.T16 hF.T8 hF.code (by have := hF.w_ge; omega) Y1 _
    h1pc h1cnt h1vd hc8 (by omega)
  have rAll := Runs.trans (M := mnRam V w n t (2 ^ τ) hfit) ga gb
    (Runs.trans (M := mnRam V w n t (2 ^ τ) hfit) ga gb r0 r1) r2
  rw [show initLen V n t + (r.steps * simLen V + accLen V) +
      (2 ^ τ - 1 - (initLen V n t + r.steps * simLen V + accLen V)) = 2 ^ τ - 1 by omega] at rAll
  have hT16 := hF.T16
  obtain ⟨hacc2, hvalid⟩ := accepting_valid_of_run ga gb (initState (mnRam V w n t (2 ^ τ) hfit)) rfl (2 ^ τ)
    (by omega) (by rw [← rAll.2] at rAll; exact rAll) (by rw [rAll.2]; exact hout)
  have hcons : (mnRam V w n t (2 ^ τ) hfit).ConsistentSeq (2 ^ τ)
      (fun i => (xrun ga gb (initState (mnRam V w n t (2 ^ τ) hfit)) i).S) xbar wit := by
    constructor
    · rw [readString_eq, (readsA_xrun (M := mnRam V w n t (2 ^ τ) hfit) ga gb (initState _) (2 ^ τ - 1)).1]
      simp only [initState, Nat.sub_zero, Nat.zero_add]
      rw [hga]; exact wordStream_prefix w xbar _
    · rw [readString_eq, (readsB_xrun (M := mnRam V w n t (2 ^ τ) hfit) ga gb (initState _) (2 ^ τ - 1)).1]
      simp only [initState, Nat.sub_zero, Nat.zero_add]
      rw [hgb]; exact wordStream_prefix w wit _
  have haddr : (mnRam V w n t (2 ^ τ) hfit).addressCount (2 ^ τ)
      (fun i => (xrun ga gb (initState (mnRam V w n t (2 ^ τ) hfit)) i).S) ≤ 2 ^ τ := by
    unfold Ram.addressCount
    exact (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans (by simp))
  exact ⟨hF.tau, hF.tau, hxT, wit, by rw [hwitlen]; exact hF.wit, _, hacc2, hvalid, hcons, haddr⟩

/-- **`lem:tm-ram` + Step 1 of `thm:short-pcp-ours`** (`lem:tm-ram` and its proof): for `x̄` extending `x` with
room for the `⌈n/w⌉` words that `M_n` reads, under the promise that `V` halts within `t` steps on every witness,
`V` accepts `x` with some `t`-bit witness iff `(x̄, 1^τ, 1^τ) ∈ BH_RAM(M_n)` (the bounded RAM predicate of `ACSP/Model.lean`), `T_n = 2^τ`. -/
theorem mn_bhram_iff (V : Verifier) (w n t τ : ℕ) (hfit : codeLen V ≤ 2 ^ w) (hF : MnFits V w n t τ)
    (x : BitInput n) (xbar : List Bool) (hxpre : ∀ p (hp : p < n), xbar.getD p false = x ⟨p, hp⟩)
    (hxlen : (n + w - 1) / w * w ≤ xbar.length) (hxT : xbar.length ≤ 2 ^ τ)
    (hrun : ∀ y : List Bool, ∃ receipt, run V.machine t (V.inputTapes (List.ofFn x) y) = some receipt) :
    (∃ y : BitInput t, V.accepts (List.ofFn x) (List.ofFn y)) ↔
      (mnRam V w n t (2 ^ τ) hfit).BHRAM xbar τ τ := by
  exact ⟨mn_bhram_fwd V w n t τ hfit hF x xbar hxpre hxlen hxT hrun, mn_bhram_back V w n t τ hfit hF x xbar hxpre⟩

end BH

end NearCubicGates.Adapters.ShortPCP

/-! ## Auxiliary syntactic memory discipline -/

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Adapters.ACSP
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

theorem LoadsOK.flatten_append {w k ops : ℕ} : ∀ (L : List (List (Instr w k ops))) (R : List (Instr w k ops)),
    (∀ l ∈ L, LoadsOK l ∧ ∀ i j, l.getLast? ≠ some (.load i j)) → NoLoad R → LoadsOK (L.flatten ++ R)
  | [], R, _, hR => by simpa using LoadsOK.of_noLoad hR
  | l :: L, R, hL, hR => by
    rw [List.flatten_cons, List.append_assoc]
    exact LoadsOK.append (hL l (by simp)).1 (LoadsOK.flatten_append L R (fun l' h => hL l' (by simp [h])) hR)
      (hL l (by simp)).2

theorem NoLoad.append {w k ops : ℕ} {l₁ l₂ : List (Instr w k ops)} (h₁ : NoLoad l₁) (h₂ : NoLoad l₂) :
    NoLoad (l₁ ++ l₂) := fun i j h => by
  rcases List.mem_append.mp h with h | h
  · exact h₁ i j h
  · exact h₂ i j h

theorem LoadsOK.noLoad_append {w k ops : ℕ} {l₁ l₂ : List (Instr w k ops)} (h₁ : NoLoad l₁) (h₂ : LoadsOK l₂) :
    LoadsOK (l₁ ++ l₂) := by
  refine LoadsOK.append (LoadsOK.of_noLoad h₁) h₂ (fun i j h => h₁ i j ?_)
  exact List.mem_of_getLast? h

theorem noLoad_of {w k ops : ℕ} {l : List (Instr w k ops)} (h : ∀ I ∈ l, ∀ i j, I ≠ .load i j) : NoLoad l :=
  fun i j hm => h _ hm i j rfl

section MWB

variable (V : Verifier) (w : ℕ)

theorem tapeSeg_noLoad (a : Action V.tapeCount V.stateCount) (i : Fin V.tapeCount) :
    NoLoad (tapeSeg V w a i) := by
  apply noLoad_of
  intro I hI
  simp only [tapeSeg, List.mem_cons] at hI
  rcases hI with rfl | hI
  · generalize a.write i = o; cases o <;> intro _ _ h <;> cases h
  · generalize a.move i = mv at hI
    cases mv <;> simp only [moveInstrs, List.mem_cons, List.not_mem_nil, or_false] at hI <;>
      rcases hI with h|h|h|h|h|h <;> rw [h] <;> intro _ _ h' <;> cases h'

theorem leafCode_noLoad (m : Fin (leafCount V)) : NoLoad (leafCode V w m) := by
  have hpad : ∀ l : List (MI V w), NoLoad l → NoLoad (padLeaf V w l) := fun l h =>
    NoLoad.append h (noLoad_of (by intro I hI; rw [List.eq_of_mem_replicate hI]; intro _ _ h; cases h))
  have hrep : ∀ k, NoLoad (List.replicate k (Instr.nop : MI V w)) :=
    fun k => noLoad_of (by intro I hI; rw [List.eq_of_mem_replicate hI]; intro _ _ h; cases h)
  have hsingle : ∀ I : MI V w, (∀ i j, I ≠ .load i j) → NoLoad [I] := fun I h => noLoad_of (by simpa using h)
  unfold leafCode
  apply hpad
  split_ifs
  · exact ((hrep _).append (hsingle _ (by intro _ _ h; cases h))).append (hrep _) |>.append
      (noLoad_of (by simp))
  · exact noLoad_of (by simp [deadLeaf])
  · split
    · exact noLoad_of (by simp [deadLeaf])
    · refine ((((hrep _).append ?_).append (hsingle _ (by intro _ _ h; cases h))).append (hrep _)).append
        (noLoad_of (by simp))
      intro i j hm
      obtain ⟨l, hl, hm'⟩ := List.mem_flatten.mp hm
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact tapeSeg_noLoad V w _ k i j hm'

/-- **`M_n` satisfies the auxiliary memory discipline**: its first instruction is a
`store`, and its only `load`s occur in the interpreter header, each followed by
its `pload`, with distinct operands. -/
theorem mnRam_wellBehaved (n t T : ℕ) (hfit : codeLen V ≤ 2 ^ w) : (mnRam V w n t T hfit).MemoryWellBehaved := by
  refine ⟨⟨rCnt, cst 0, rfl⟩, ?_⟩
  have hnl : ∀ (l : List (MI V w)), (∀ I ∈ l, ∀ i j, I ≠ .load i j) → NoLoad l := fun l h => noLoad_of h
  have hP : NoLoad (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++ setupBlock V w ++
      unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w) := by
    apply hnl
    intro I hI i j h
    subst h
    simp [startBlock, unpackBlock, setupBlock, simSetupBlock, List.mem_replicate, List.mem_ofFn] at hI
  have hR : NoLoad ([.arith 0 rIdx (.reg rSr) (cst 0)] ++
      (List.ofFn fun i : Fin V.tapeCount =>
        ([.arith 0 rIdx (.reg rIdx) (.reg rIdx), .arith 0 rIdx (.reg rIdx) (.reg (rS i))] : List (MI V w))).flatten ++
      chainBlock V w ++ (List.ofFn (leafCode V w)).flatten ++ [.jmp (deadAddr V)] ++
      idleCode 0 3 rCnt rTmp rVd (idleAddr V) T) := by
    refine NoLoad.append (NoLoad.append (NoLoad.append ?_ ?_) (noLoad_of (by simp))) (noLoad_of ?_)
    · apply hnl; intro I hI i j h; subst h
      simp [chainBlock, List.mem_ofFn] at hI
    · intro i j hm
      obtain ⟨l, hl, hm'⟩ := List.mem_flatten.mp hm
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hl
      exact leafCode_noLoad V w k i j hm'
    · intro I hI i j h; subst h; simp [idleCode] at hI
  have hcode : mnCode V w n t T = (startBlock V w ++ unpackBlock V w (fun r => .readA r) 8 n (deadAddr V) ++
      setupBlock V w ++ unpackBlock V w (fun r => .readB r) 50 t (deadAddr V) ++ simSetupBlock V w) ++
      ((List.ofFn fun i : Fin V.tapeCount =>
        ([.load (rH i) (rS i), .pload (rH i) (rS i)] : List (MI V w))).flatten ++
      ([.arith 0 rIdx (.reg rSr) (cst 0)] ++
      (List.ofFn fun i : Fin V.tapeCount =>
        ([.arith 0 rIdx (.reg rIdx) (.reg rIdx), .arith 0 rIdx (.reg rIdx) (.reg (rS i))] : List (MI V w))).flatten ++
      chainBlock V w ++ (List.ofFn (leafCode V w)).flatten ++ [.jmp (deadAddr V)] ++
      idleCode 0 3 rCnt rTmp rVd (idleAddr V) T)) := by
    simp only [mnCode, headerBlock, List.append_assoc]
  have hok : LoadsOK (mnCode V w n t T) := by
    rw [hcode]
    refine LoadsOK.noLoad_append hP (LoadsOK.flatten_append _ _ ?_ hR)
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    refine ⟨?_, by simp⟩
    intro p a b hp
    rcases p with _ | _ | p
    · simp at hp; obtain ⟨rfl, rfl⟩ := hp
      refine ⟨fun h => ?_, rfl⟩
      have h1 := congrArg Fin.val h; have := V.twoTapes; simp at h1; omega
    · simp at hp
    · simp at hp
  exact hok

end MWB

end NearCubicGates.Adapters.ShortPCP
