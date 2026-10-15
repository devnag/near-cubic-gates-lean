import Proof.Gates.Recovery.AfterSpec
import Proof.MachineModel.OrdinaryOracleCompose
import Proof.Amplification.RecoveryFocusRetained

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound

/-! ## Clocked stages -/

/-- The clocked program's entry bank: the source bank, then the blank clock and reset tapes. -/
def clockIn (p : OrdinaryOracleProgram) (input : Fin p.base.tapeCount → List Bool) :
    Fin (clocked p).base.tapeCount → List Bool :=
  Fin.addCases (Fin.addCases input (fun _ => [])) (fun _ => [])

/-- The clocked program's exit bank: the source tapes, the clock `1^n` and the reset log `0^n`. -/
def clockOut (p : OrdinaryOracleProgram) (tapes : Fin p.base.tapeCount → List Bool) (n : ℕ) :
    Fin (clocked p).base.tapeCount → List Bool :=
  Fin.addCases (Fin.addCases tapes (fun _ => List.replicate n true)) (fun _ => List.replicate n false)

/-- The source tape `i` inside the clocked program. -/
def cslot (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) : Fin (clocked p).base.tapeCount :=
  (i.castAdd 1).castAdd 1

theorem clockIn_src (p : OrdinaryOracleProgram) (input : Fin p.base.tapeCount → List Bool)
    (i : Fin p.base.tapeCount) : clockIn p input (cslot p i) = input i := by
  simp [clockIn, cslot]

theorem clockOut_src (p : OrdinaryOracleProgram) (tapes : Fin p.base.tapeCount → List Bool) (n : ℕ)
    (i : Fin p.base.tapeCount) : clockOut p tapes n (cslot p i) = tapes i := by
  simp [clockOut, cslot]

theorem clockOut_clock (p : OrdinaryOracleProgram) (tapes : Fin p.base.tapeCount → List Bool) (n : ℕ) :
    clockOut p tapes n (clockTape p) = List.replicate n true := by
  simp [clockOut, clockTape]

theorem clockIn_clock (p : OrdinaryOracleProgram) (input : Fin p.base.tapeCount → List Bool) :
    clockIn p input (clockTape p) = [] := by
  simp [clockIn, clockTape]

theorem clockIn_reset (p : OrdinaryOracleProgram) (input : Fin p.base.tapeCount → List Bool) :
    clockIn p input (resetTape p) = [] := by
  simp [clockIn, resetTape]

theorem cslot_query (p : OrdinaryOracleProgram) : cslot p p.queryTape = (clocked p).queryTape := rfl

theorem cslot_injective (p : OrdinaryOracleProgram) : Function.Injective (cslot p) := by
  intro a b h
  have := congrArg Fin.val h
  simp [cslot] at this
  exact Fin.ext this

theorem cslot_ne_clock (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) : cslot p i ≠ clockTape p := by
  intro h
  have := congrArg Fin.val h
  simp [cslot, clockTape] at this
  omega

/-- Every tape of the clocked program is a source tape, the clock tape or the reset tape. -/
theorem clocked_cases (p : OrdinaryOracleProgram) (j : Fin (clocked p).base.tapeCount) :
    (∃ i, j = cslot p i) ∨ j = clockTape p ∨ j = resetTape p := by
  have hj := j.isLt
  change j.val < p.base.tapeCount + 1 + 1 at hj
  by_cases h1 : j.val < p.base.tapeCount
  · exact Or.inl ⟨⟨j.val, h1⟩, Fin.ext (by simp [cslot])⟩
  · by_cases h2 : j.val = p.base.tapeCount
    · exact Or.inr (Or.inl (Fin.ext (by simp [clockTape, h2])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [resetTape]; omega)))

theorem clocked_ready {o : ℕ → Bool} {p : OrdinaryOracleProgram} {cost : ℕ}
    {input : Fin p.base.tapeCount → List Bool} {final : p.Config}
    (h : OrdinaryOracleTrace o p cost (initialConfiguration p.base.machine input) final)
    (hh : p.base.machine.halted final.control = true) :
    ∃ n, n ≤ cost ∧ Ready o (clocked p) (cost + (n + 2)) (clockIn p input) (clockOut p final.tapes n) ∧
      ∀ i, (final.tapes i).length ≤ max (input i).length n := by
  obtain ⟨k, hk, htr, hheads, htapes⟩ := clock_trace h 0 (by intro i; simp [initialConfiguration])
    (fun i => (input i).length) (by intro i; simp [initialConfiguration])
  simp only [Nat.zero_add] at htr hheads htapes
  have hr := reset_trace o p final k hheads hh
  have hinit : clockRecord (initialConfiguration p.base.machine input) 0 =
      initialConfiguration (clocked p).base.machine (clockIn p input) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
          simp [clockRecord, Rewind.recording, Rewind.config, clockConfig, initialConfiguration]
      · simp [clockRecord, Rewind.recording, Rewind.config, initialConfiguration]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
          simp [clockRecord, Rewind.recording, Rewind.config, clockConfig, initialConfiguration, clockIn]
      · simp [clockRecord, Rewind.recording, Rewind.config, initialConfiguration, clockIn]
  have whole := trans htr hr
  rw [hinit] at whole
  refine ⟨k, hk, ⟨_, whole, ?_, ?_, ?_⟩, htapes⟩
  · simp [clocked, Rewind.finished, Rewind.config, Rewind.machine]
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Rewind.finished, Rewind.config]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
        simp [Rewind.finished, Rewind.config, clockConfig, clockOut]
    · simp [Rewind.finished, Rewind.config, clockOut]

/-! ## Bank slots -/

/-- The port map of a list of `(local tape, ambient tape)` pairs (the first pair of a local tape wins). -/
def portL {t T : ℕ} (l : List (Fin t × Fin T)) (j : Fin t) : Option (Fin T) :=
  (l.find? (fun p => decide (p.1 = j))).map Prod.snd

theorem portL_cons_self {t T : ℕ} (a : Fin t) (x : Fin T) (l : List (Fin t × Fin T)) :
    portL ((a, x) :: l) a = some x := by
  simp [portL]

theorem portL_cons_ne {t T : ℕ} (a b : Fin t) (x : Fin T) (l : List (Fin t × Fin T)) (h : b ≠ a) :
    portL ((a, x) :: l) b = portL l b := by
  simp [portL, Ne.symm h]

theorem portL_nil {t T : ℕ} (j : Fin t) : portL ([] : List (Fin t × Fin T)) j = none := rfl

theorem portL_some {t T : ℕ} {l : List (Fin t × Fin T)} {j : Fin t} {x : Fin T} (h : portL l j = some x) :
    (j, x) ∈ l := by
  unfold portL at h
  cases hf : l.find? (fun p => decide (p.1 = j)) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [← h, ← hp]
    exact hm

/-- A bank slot: a listed local tape goes to its ambient tape, every other local tape `j` to `off + j`. -/
def bslot {t T : ℕ} (off : ℕ) (hT : off + t ≤ T) (l : List (Fin t × Fin T)) (j : Fin t) : Fin T :=
  match portL l j with
  | some a => a
  | none => ⟨off + j.val, by have := j.isLt; omega⟩

theorem bslot_port {t T : ℕ} {off : ℕ} {hT : off + t ≤ T} {l : List (Fin t × Fin T)} {j : Fin t} {x : Fin T}
    (h : portL l j = some x) : bslot off hT l j = x := by
  simp only [bslot, h]

theorem bslot_priv {t T : ℕ} {off : ℕ} {hT : off + t ≤ T} {l : List (Fin t × Fin T)} {j : Fin t}
    (h : portL l j = none) : (bslot off hT l j).val = off + j.val := by
  simp only [bslot, h]

theorem bslot_injective {t T : ℕ} (off : ℕ) (hT : off + t ≤ T) (l : List (Fin t × Fin T))
    (hnd : (l.map Prod.snd).Nodup) (hlow : ∀ p ∈ l, p.2.val < off) : Function.Injective (bslot off hT l) := by
  intro i j he
  cases hi : portL l i with
  | none =>
    cases hj : portL l j with
    | none =>
      have h1 := bslot_priv (hT := hT) hi
      have h2 := bslot_priv (hT := hT) hj
      have := congrArg Fin.val he
      exact Fin.ext (by omega)
    | some b =>
      have h1 := bslot_priv (hT := hT) hi
      rw [bslot_port hj] at he
      have hb := hlow _ (portL_some hj)
      have := congrArg Fin.val he
      simp only at hb
      omega
  | some a =>
    cases hj : portL l j with
    | none =>
      have h2 := bslot_priv (hT := hT) hj
      rw [bslot_port hi] at he
      have ha := hlow _ (portL_some hi)
      have := congrArg Fin.val he
      simp only at ha
      omega
    | some b =>
      rw [bslot_port hi, bslot_port hj] at he
      subst he
      have hmi := portL_some hi
      have hmj := portL_some hj
      have := List.inj_on_of_nodup_map hnd hmi hmj rfl
      simp only [Prod.mk.injEq, and_true] at this
      exact this

/-- Tapes outside the listed ports and outside the private block are not slots of the bank. -/
theorem bslot_ne {t T : ℕ} {off : ℕ} {hT : off + t ≤ T} {l : List (Fin t × Fin T)} (x : Fin T)
    (hx : ∀ p ∈ l, p.2 ≠ x) (hout : x.val < off ∨ off + t ≤ x.val) (j : Fin t) : bslot off hT l j ≠ x := by
  cases h : portL l j with
  | none =>
    have h1 := bslot_priv (hT := hT) h
    intro he
    have := congrArg Fin.val he
    have := j.isLt
    omega
  | some a =>
    rw [bslot_port h]
    exact hx _ (portL_some h)

/-! ## Pieces of the after-prefix graph -/

/-- A `ClockJoin` run within a budget is an exact ready run within at most that budget. -/
theorem exact_time {t s cost : ℕ} {p : Machine t s} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p cost input output) :
    ∃ time, time ≤ cost ∧ RecoveryRootRound.ReadyRun p time input output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  have he := RecoveryRootRound.ready_of_run p cost input r hr hh
  rw [ht] at he
  exact ⟨r.steps, hs, he⟩

/-- **An ordinary piece**: a ready run of one machine, focused on its bank of the ambient tapes. -/
theorem piece_ordinary {o : ℕ → Bool} {T t s n : ℕ} (ports : Ports T) {M : Machine t s}
    {input output : Fin t → List Bool} (h : RecoveryRootRound.ReadyRun M n input output)
    (slot : Fin t → Fin T) (hi : Function.Injective slot) (A : Fin T → List Bool)
    (hin : ∀ j, A (slot j) = input j) :
    Ready o (ports.program (ordinary (RecoveryFocus.machine slot M))) n A (install slot A output) :=
  Ready.ordinary ports (h.focus slot hi A hin)

/-- **An oracle piece**: a ready stage, its tapes zero padded (the shared query tape after a clear), focused on its bank
of the ambient tapes, its query tape on the shared one. -/
theorem piece_oracle {o : ℕ → Bool} {T : ℕ} (ports : Ports T) {p : OrdinaryOracleProgram} {n : ℕ}
    {input output : Fin p.base.tapeCount → List Bool} (h : Ready o p n input output)
    (caps : Fin p.base.tapeCount → ℕ) (slot : Fin p.base.tapeCount → Fin T) (hi : Function.Injective slot)
    (hq : slot p.queryTape = ports.queryTape) (A : Fin T → List Bool)
    (hin : ∀ j, A (slot j) = ZeroPadding.pad (caps j) (input j)) :
    Ready o (ports.program (focused p slot)) n A
      (install slot A (fun j => ZeroPadding.pad (caps j) (output j))) :=
  (h.padding caps).focus ports slot hi hq A hin

/-- The graph program starts with its entry piece. -/
theorem graph_initial {t k : ℕ} (ports : Ports t) (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k)) (A : Fin t → List Bool) :
    initialConfiguration (ports.program (graph pieces entry next)).base.machine A =
      controlConfig (RecoveryCalls.code (fun j => (pieces j).states) entry)
        (initialConfiguration (pieces entry).machine A) := rfl

/-- A trace of the graph program from its entry to the stopped configuration is a ready run. -/
theorem graph_ready {o : ℕ → Bool} {t k : ℕ} (ports : Ports t) (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k)) {A B : Fin t → List Bool}
    {cost : ℕ}
    (h : OrdinaryOracleTrace o (ports.program (graph pieces entry next)) cost
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) entry)
        (initialConfiguration (pieces entry).machine A))
      (RecoveryCalls.stopped (fun j => (pieces j).states) (fun _ => 0) B)) :
    Ready o (ports.program (graph pieces entry next)) cost A B := by
  refine ⟨_, by rw [graph_initial]; exact h, ?_, fun _ => rfl, rfl⟩
  simp [Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped]

/-! ## Banks -/

/-- The shared-tape values written by a bank: listed pair `(j, x)` puts the local output `out j` on `x`. -/
def updates {t T : ℕ} (l : List (Fin t × Fin T)) (out : Fin t → List Bool) (A : Fin T → List Bool) :
    Fin T → List Bool :=
  l.foldr (fun p f => Function.update f p.2 (out p.1)) A

@[simp] theorem updates_nil {t T : ℕ} (out : Fin t → List Bool) (A : Fin T → List Bool) :
    updates ([] : List (Fin t × Fin T)) out A = A := rfl

@[simp] theorem updates_cons {t T : ℕ} (p : Fin t × Fin T) (l : List (Fin t × Fin T)) (out : Fin t → List Bool)
    (A : Fin T → List Bool) : updates (p :: l) out A = Function.update (updates l out A) p.2 (out p.1) := rfl

theorem updates_mem {t T : ℕ} {l : List (Fin t × Fin T)} (hnd : (l.map Prod.snd).Nodup)
    (out : Fin t → List Bool) (A : Fin T → List Bool) {j : Fin t} {x : Fin T} (h : (j, x) ∈ l) :
    updates l out A x = out j := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [updates_cons, Function.update_apply]
    rcases List.mem_cons.mp h with he | hm
    · subst he; simp
    · have hx : x ≠ p.2 := by
        intro e
        exact hnd.1 ⟨(j, x), hm, e⟩
      rw [if_neg hx]
      exact ih hnd.2 hm

theorem updates_not {t T : ℕ} {l : List (Fin t × Fin T)} (out : Fin t → List Bool) (A : Fin T → List Bool)
    {x : Fin T} (h : ∀ p ∈ l, p.2 ≠ x) : updates l out A x = A x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [updates_cons, Function.update_apply, if_neg (Ne.symm (h p (List.mem_cons_self ..)))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- A bank of `t` local tapes in `T` ambient tapes: the listed ports (shared tapes below `off`), every other local tape
`j` at `off + j`. -/
structure Bank (T t : ℕ) where
  off : ℕ
  fits : off + t ≤ T
  l : List (Fin t × Fin T)
  fstNodup : (l.map Prod.fst).Nodup
  sndNodup : (l.map Prod.snd).Nodup
  low : ∀ p ∈ l, p.2.val < off

namespace Bank

variable {T t : ℕ}

/-- The slot map of a bank. -/
def slot (b : Bank T t) : Fin t → Fin T := bslot b.off b.fits b.l

theorem injective (b : Bank T t) : Function.Injective b.slot :=
  bslot_injective b.off b.fits b.l b.sndNodup b.low

theorem portL_of_mem (b : Bank T t) {j : Fin t} {x : Fin T} (h : (j, x) ∈ b.l) : portL b.l j = some x := by
  cases hp : portL b.l j with
  | none =>
    exfalso
    have hs : (b.l.find? (fun p => decide (p.1 = j))).isSome := by
      rw [List.find?_isSome]
      exact ⟨(j, x), h, by simp⟩
    unfold portL at hp
    cases hf : b.l.find? (fun p => decide (p.1 = j)) with
    | none => rw [hf] at hs; simp at hs
    | some q => rw [hf] at hp; simp at hp
  | some y =>
    have hm := portL_some hp
    have := List.inj_on_of_nodup_map b.fstNodup hm h rfl
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]

theorem slot_port (b : Bank T t) {j : Fin t} {x : Fin T} (h : (j, x) ∈ b.l) : b.slot j = x :=
  bslot_port (b.portL_of_mem h)

theorem slot_free (b : Bank T t) {j : Fin t} (h : ∀ p ∈ b.l, p.1 ≠ j) : (b.slot j).val = b.off + j.val := by
  apply bslot_priv
  cases hp : portL b.l j with
  | none => rfl
  | some y => exact absurd rfl (h _ (portL_some hp))

/-- Below the bank's block, installing its outputs only writes the listed ports. -/
theorem install_low (b : Bank T t) (A : Fin T → List Bool) (out : Fin t → List Bool) (x : Fin T)
    (hx : x.val < b.off) : install b.slot A out x = updates b.l out A x := by
  by_cases hm : ∃ j, (j, x) ∈ b.l
  · obtain ⟨j, hj⟩ := hm
    rw [← b.slot_port hj, install_slot _ b.injective, b.slot_port hj, updates_mem b.sndNodup out A hj]
  · have hn : ∀ p ∈ b.l, p.2 ≠ x := by
      intro p hp he
      exact hm ⟨p.1, by rw [← he]; exact hp⟩
    rw [updates_not out A hn]
    apply install_other
    intro j hj
    cases hp : portL b.l j with
    | none =>
      have := bslot_priv (hT := b.fits) hp
      have := congrArg Fin.val hj
      unfold slot at this
      omega
    | some y =>
      have hy : b.slot j = y := bslot_port hp
      exact hn _ (portL_some hp) (hy.symm.trans hj)

/-- Above the bank's block nothing changes. -/
theorem install_high (b : Bank T t) (A : Fin T → List Bool) (out : Fin t → List Bool) (x : Fin T)
    (hx : b.off + t ≤ x.val) : install b.slot A out x = A x := by
  apply install_other
  intro j hj
  cases hp : portL b.l j with
  | none =>
    have := bslot_priv (hT := b.fits) hp
    have := congrArg Fin.val hj
    have := j.isLt
    unfold slot at *
    omega
  | some y =>
    have hy : b.slot j = y := bslot_port hp
    have hl : y.val < b.off := b.low _ (portL_some hp)
    have := congrArg Fin.val (hy.symm.trans hj)
    omega

/-- The bank reads an input bank: listed ports carry their words, every other local tape is blank, the private block is
blank in the ambient state. -/
theorem input (b : Bank T t) (A : Fin T → List Bool) (inp : Fin t → List Bool)
    (hport : ∀ p ∈ b.l, A p.2 = inp p.1) (hfree : ∀ j, (∀ p ∈ b.l, p.1 ≠ j) → inp j = [])
    (hblank : ∀ x : Fin T, b.off ≤ x.val → x.val < b.off + t → A x = []) : ∀ j, A (b.slot j) = inp j := by
  intro j
  by_cases hm : ∃ x, (j, x) ∈ b.l
  · obtain ⟨x, hx⟩ := hm
    rw [b.slot_port hx]
    exact hport _ hx
  · have hf : ∀ p ∈ b.l, p.1 ≠ j := by
      intro p hp he
      exact hm ⟨p.2, by rw [← he]; exact hp⟩
    rw [hfree j hf]
    have hv := b.slot_free hf
    exact hblank _ (by omega) (by have := j.isLt; omega)

/-- The bank's output on a listed port. -/
theorem install_port (b : Bank T t) (A : Fin T → List Bool) (out : Fin t → List Bool) {j : Fin t} {x : Fin T}
    (h : (j, x) ∈ b.l) : install b.slot A out x = out j := by
  rw [← b.slot_port h, install_slot _ b.injective]

end Bank

end NearCubicGates.Close.Recovery.After
