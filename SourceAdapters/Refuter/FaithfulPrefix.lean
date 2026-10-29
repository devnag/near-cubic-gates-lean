import NineInputs

/-!
# Faithful prefixes, for every guess (input 7, step F02)

Paper anchor: `lem:multitape-refuter`, paragraph "Shared prefix simulation", and
`cor:framed-refuter`.

* proof of `lem:multitape-refuter`: "the hierarchy verifier guesses a positive length `r` in unary and copies cells
  `0,…,r−1` of both prepared tapes, including genuine blank cells when necessary." — `prefixTapes`.
* proof of `lem:multitape-refuter`: "Reaching a cutoff aborts without either verdict, before executing an original
  transition there." — `cutRunFrom`.
* proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`: two separate verdict predicates, "we never complement the universal
  acceptor"; the copied tapes "include the prescribed frame terminators and blank zeros beyond
  them". — `CertifiesAccept`, `CertifiesReject` (the framed tapes are `Verifier.inputTapes`).
* proof of `lem:multitape-refuter`: "For every guessed `r`, the initial simulated cells agree with the original tapes.
  Induction on the simulated steps, including their writes, preserves the state, heads, and all
  visited cells until a cutoff or a genuine halt. Hence every verified verdict is genuine." —
  `cutRun_sound`, `certifiesAccept_genuine`, `certifiesReject_genuine` (for **every** `r`).
* proof of `lem:multitape-refuter`: "Conversely, if the original computation halts in `t` steps, the choice `r=t+2` keeps
  both heads strictly before the cutoffs: a head starts at zero and moves by at most one cell per
  step." — `cutRun_complete`, `certifies_of_halts`.
* proof of `lem:multitape-refuter`: "The original work tapes remain unbounded. A computation on some other prefix can run
  arbitrarily long without reaching a cutoff": nothing here bounds other prefixes.

This module is the machine-independent semantic core. The machine that realizes `cutRunFrom` on a
packed prefix word is a separate construction (F01/F03).
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape

set_option autoImplicit false

/-! ## Cells, prefixes and the cut run -/

/-- Two tapes agree on the cells `0, …, r-1`. -/
def AgreeBelow (r : ℕ) (a b : List Bool) : Prop :=
  ∀ p, p < r → readTapeBit a p = readTapeBit b p

/-- The copied prefix of one tape: cells `0, …, r-1`, blank beyond (proof of `lem:multitape-refuter`). -/
def prefixTape (r : ℕ) (tape : List Bool) : List Bool := tape.take r

/-- The copied prefixes of all tapes. -/
def prefixTapes {t : ℕ} (r : ℕ) (tapes : Fin t → List Bool) : Fin t → List Bool :=
  fun i => prefixTape r (tapes i)

/-- A configuration `d` on the copied prefixes is faithful to the original `c` below the cutoff
`r`: same control state, same heads, same cells `0, …, r-1` on every tape (proof of `lem:multitape-refuter`). -/
structure PrefixFaithful {t s : ℕ} (r : ℕ) (c d : Configuration t s) : Prop where
  control : d.control = c.control
  heads : d.heads = c.heads
  tapes : ∀ i, AgreeBelow r (d.tapes i) (c.tapes i)

/-- The cut run (proof of `lem:multitape-refuter`): like `runFrom`, except that when some head has reached the
protected cutoff cell `r`, it aborts with no verdict before executing a transition there. A halted
configuration is returned as it is. -/
def cutRunFrom {t s : ℕ} (m : Machine t s) (r : ℕ) :
    ℕ → Configuration t s → Option (Configuration t s)
  | 0, c => if m.halted c.control then some c else none
  | fuel + 1, c =>
      if m.halted c.control then some c
      else if ∃ i, r ≤ c.heads i then none
      else
        match step m c with
        | none => none
        | some next => cutRunFrom m r fuel next

/-! ## Cell lemmas -/

theorem readTapeBit_writeTapeBit (l : List Bool) (p : ℕ) (v : Bool) (q : ℕ) :
    readTapeBit (writeTapeBit l p v) q = if q = p then v else readTapeBit l q := by
  unfold readTapeBit
  induction l generalizing p q with
  | nil =>
    induction p generalizing q with
    | zero => cases q <;> simp [writeTapeBit]
    | succ p ih =>
      cases q with
      | zero => simp [writeTapeBit]
      | succ q => simpa [writeTapeBit] using ih q
  | cons a l ih =>
    cases p <;> cases q <;>
      simp only [writeTapeBit, List.getD_cons_succ, List.getD_cons_zero, ih] <;> simp

theorem AgreeBelow.write {r : ℕ} {a b : List Bool} (h : AgreeBelow r a b) (p : ℕ) (v : Bool) :
    AgreeBelow r (writeTapeBit a p v) (writeTapeBit b p v) := by
  intro q hq
  rw [readTapeBit_writeTapeBit, readTapeBit_writeTapeBit, h q hq]

theorem agreeBelow_prefixTape (r : ℕ) (tape : List Bool) :
    AgreeBelow r (prefixTape r tape) tape := by
  intro p hp
  unfold readTapeBit prefixTape
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp]

theorem HeadMove.apply_le (move : HeadMove) (h : ℕ) : move.apply h ≤ h + 1 := by
  cases move <;> (simp only [HeadMove.apply]; omega)

theorem step_heads_le {t s : ℕ} (m : Machine t s) {c c' : Configuration t s}
    (h : step m c = some c') (i : Fin t) : c'.heads i ≤ c.heads i + 1 := by
  unfold step at h
  cases hrule : m.rule c.control c.scanned with
  | none => simp [hrule] at h
  | some a =>
    simp only [hrule, Option.map_some, Option.some.injEq] at h
    subst h
    exact HeadMove.apply_le _ _

/-! ## One step preserves faithfulness below the cutoff -/

theorem PrefixFaithful.scanned {t s r : ℕ} {c d : Configuration t s}
    (h : PrefixFaithful r c d) (hr : ∀ i, c.heads i < r) : d.scanned = c.scanned := by
  funext i
  simp only [Configuration.scanned]
  rw [h.heads]
  exact h.tapes i _ (hr i)

theorem PrefixFaithful.applyAction {t s r : ℕ} {c d : Configuration t s}
    (h : PrefixFaithful r c d) (a : Action t s) :
    PrefixFaithful r (applyAction c a) (applyAction d a) where
  control := rfl
  heads := by
    funext i
    simp only [LocalBitMultitape.applyAction, h.heads]
  tapes := by
    intro i
    simp only [LocalBitMultitape.applyAction]
    cases a.write i with
    | none => exact h.tapes i
    | some v => rw [h.heads]; exact (h.tapes i).write _ v

/-- Below the cutoff the copied configuration takes exactly the original transition. -/
theorem step_faithful {t s r : ℕ} (m : Machine t s) {c d : Configuration t s}
    (h : PrefixFaithful r c d) (hr : ∀ i, c.heads i < r) :
    (step m c = none ∧ step m d = none) ∨
      ∃ c' d', step m c = some c' ∧ step m d = some d' ∧ PrefixFaithful r c' d' := by
  unfold step
  rw [h.scanned hr, h.control]
  cases m.rule c.control c.scanned with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some a => exact Or.inr ⟨_, _, rfl, rfl, h.applyAction a⟩

/-! ## Every certified verdict is genuine, for every cutoff `r` -/

/-- **Soundness for every guessed `r`** (proof of `lem:multitape-refuter`): a halted cut run is matched by an original
run with the same fuel whose final configuration agrees in control, heads and all cells below `r`. -/
theorem cutRun_sound {t s : ℕ} (m : Machine t s) (r : ℕ) :
    ∀ (fuel : ℕ) (c d d' : Configuration t s), PrefixFaithful r c d →
      cutRunFrom m r fuel d = some d' →
      ∃ receipt, runFrom m fuel c = some receipt ∧ PrefixFaithful r receipt.final d' := by
  intro fuel
  induction fuel with
  | zero =>
    intro c d d' h hrun
    simp only [cutRunFrom] at hrun
    split_ifs at hrun with hh
    cases hrun
    rw [h.control] at hh
    exact ⟨{ final := c, steps := 0, peakTapeCells := c.tapeCells }, by simp [runFrom, hh], h⟩
  | succ fuel ih =>
    intro c d d' h hrun
    simp only [cutRunFrom] at hrun
    split_ifs at hrun with hh hcut
    · cases hrun
      rw [h.control] at hh
      exact ⟨{ final := c, steps := 0, peakTapeCells := c.tapeCells }, by simp [runFrom, hh], h⟩
    · have hr : ∀ i, c.heads i < r := by
        intro i
        rw [← h.heads]
        exact Nat.lt_of_not_le fun hle => hcut ⟨i, hle⟩
      rw [h.control] at hh
      rcases step_faithful m h hr with ⟨_, hd⟩ | ⟨c', d'', hc, hd, h'⟩
      · rw [hd] at hrun
        cases hrun
      · rw [hd] at hrun
        obtain ⟨suffix, hs, hf⟩ := ih c' d'' d' h' hrun
        refine ⟨⟨suffix.final, suffix.steps + 1, max c.tapeCells suffix.peakTapeCells⟩, ?_, hf⟩
        simp [runFrom, hh, hc, hs]

/-- The run of `m` from `c` with the fuel used never takes more steps than its fuel. -/
theorem runFrom_steps_le {t s : ℕ} (m : Machine t s) :
    ∀ (fuel : ℕ) (c : Configuration t s) (receipt : ExecutionReceipt t s),
      runFrom m fuel c = some receipt → receipt.steps ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro c receipt h
    simp only [runFrom] at h
    split_ifs at h
    cases h
    simp
  | succ fuel ih =>
    intro c receipt h
    simp only [runFrom] at h
    split_ifs at h
    · cases h
      simp
    · cases hs : step m c with
      | none => simp [hs] at h
      | some next =>
        cases hr : runFrom m fuel next with
        | none => simp [hs, hr] at h
        | some suffix =>
          simp only [hs, hr, Option.some.injEq] at h
          subst h
          have := ih next suffix hr
          simp only
          omega

/-- **Completeness** (proof of `lem:multitape-refuter`): if the original run halts after `steps` transitions and
every head starts at most `r - steps` cells from the left end, the cut run halts too, in a
configuration faithful to the original final one. -/
theorem cutRun_complete {t s : ℕ} (m : Machine t s) (r : ℕ) :
    ∀ (fuel : ℕ) (c d : Configuration t s) (receipt : ExecutionReceipt t s),
      runFrom m fuel c = some receipt → PrefixFaithful r c d →
      (∀ i, c.heads i + receipt.steps ≤ r) →
      ∃ d', cutRunFrom m r fuel d = some d' ∧ PrefixFaithful r receipt.final d' := by
  intro fuel
  induction fuel with
  | zero =>
    intro c d receipt hrun h _
    simp only [runFrom] at hrun
    split_ifs at hrun with hh
    cases hrun
    refine ⟨d, ?_, h⟩
    simp [cutRunFrom, h.control, hh]
  | succ fuel ih =>
    intro c d receipt hrun h hbound
    simp only [runFrom] at hrun
    split_ifs at hrun with hh
    · cases hrun
      refine ⟨d, ?_, h⟩
      simp [cutRunFrom, h.control, hh]
    · cases hs : step m c with
      | none => simp [hs] at hrun
      | some next =>
        cases hr : runFrom m fuel next with
        | none => simp [hs, hr] at hrun
        | some suffix =>
          simp only [hs, hr, Option.some.injEq] at hrun
          subst hrun
          have hlt : ∀ i, c.heads i < r := by
            intro i
            have := hbound i
            simp only at this
            omega
          rcases step_faithful m h hlt with ⟨hc, _⟩ | ⟨c', d'', hc, hd, h'⟩
          · rw [hc] at hs
            cases hs
          · have hcn : c' = next := Option.some.inj (hc.symm.trans hs)
            subst hcn
            have hnext : ∀ i, c'.heads i + suffix.steps ≤ r := by
              intro i
              have hmove : c'.heads i ≤ c.heads i + 1 := step_heads_le m hc i
              have := hbound i
              simp only at this
              omega
            obtain ⟨d', hd', hf⟩ := ih c' d'' suffix hr h' hnext
            refine ⟨d', ?_, hf⟩
            have hcut : ¬ ∃ i, r ≤ d.heads i := by
              rintro ⟨i, hi⟩
              rw [h.heads] at hi
              exact absurd (hlt i) (Nat.not_lt.mpr hi)
            have hh' : ¬ m.halted d.control = true := by rw [h.control]; exact hh
            simp [cutRunFrom, hh', hcut, hd, hd']

/-! ## The initial copy and the two verdicts -/

theorem prefixFaithful_initial {t s : ℕ} (m : Machine t s) (r : ℕ) (tapes : Fin t → List Bool) :
    PrefixFaithful r (initialConfiguration m tapes) (initialConfiguration m (prefixTapes r tapes)) where
  control := rfl
  heads := rfl
  tapes := fun i => agreeBelow_prefixTape r (tapes i)

/-- The cut run of `m` on the copied prefixes of `tapes`. -/
def prefixRun {t s : ℕ} (m : Machine t s) (r fuel : ℕ) (tapes : Fin t → List Bool) :
    Option (Configuration t s) :=
  cutRunFrom m r fuel (initialConfiguration m (prefixTapes r tapes))

/-- The accepting-verdict predicate of `P_M^+` (proof of `lem:multitape-refuter`): the cut run on the copied framed
tapes halts in an accepting state. -/
def CertifiesAccept (v : RepairOrdinary.Verifier) (r fuel : ℕ) (input witness : List Bool) : Prop :=
  ∃ d, prefixRun v.machine r fuel (v.inputTapes input witness) = some d ∧
    v.accepting d.control = true

/-- The rejecting-verdict predicate of `P_M^-` (proof of `lem:multitape-refuter`), a separate predicate: the cut run
halts in a non-accepting state. It is not the complement of `CertifiesAccept`: an aborted run
certifies neither verdict (proof of `cor:framed-refuter`). -/
def CertifiesReject (v : RepairOrdinary.Verifier) (r fuel : ℕ) (input witness : List Bool) : Prop :=
  ∃ d, prefixRun v.machine r fuel (v.inputTapes input witness) = some d ∧
    v.accepting d.control = false

/-- `V_M^fr(x, fuel, w) = 1`: the original framed run halts within `fuel` steps and accepts. -/
def HaltsAccepting (v : RepairOrdinary.Verifier) (fuel : ℕ) (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true

/-- `V_M^fr(x, fuel, w) = 0`: the original framed run halts within `fuel` steps and rejects. -/
def HaltsRejecting (v : RepairOrdinary.Verifier) (fuel : ℕ) (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = false

theorem haltsAccepting_iff_acceptsAt (v : RepairOrdinary.Verifier) (fuel : ℕ) (x w : List Bool) :
    HaltsAccepting v fuel x w ↔ v.acceptsAt fuel x w := Iff.rfl

/-- **Every certified accepting verdict is genuine, for every `r`** (proof of `lem:multitape-refuter`). -/
theorem certifiesAccept_genuine (v : RepairOrdinary.Verifier) (r fuel : ℕ) (x w : List Bool)
    (h : CertifiesAccept v r fuel x w) : HaltsAccepting v fuel x w := by
  obtain ⟨d, hd, hacc⟩ := h
  obtain ⟨receipt, hrun, hf⟩ :=
    cutRun_sound v.machine r fuel _ _ d (prefixFaithful_initial _ r _) hd
  exact ⟨receipt, hrun, by rw [← hf.control]; exact hacc⟩

/-- **Every certified rejecting verdict is genuine, for every `r`** (proof of `lem:multitape-refuter`). -/
theorem certifiesReject_genuine (v : RepairOrdinary.Verifier) (r fuel : ℕ) (x w : List Bool)
    (h : CertifiesReject v r fuel x w) : HaltsRejecting v fuel x w := by
  obtain ⟨d, hd, hacc⟩ := h
  obtain ⟨receipt, hrun, hf⟩ :=
    cutRun_sound v.machine r fuel _ _ d (prefixFaithful_initial _ r _) hd
  exact ⟨receipt, hrun, by rw [← hf.control]; exact hacc⟩

/-- More fuel never changes a halted run (copied from `Audit.Step2.Input7A.runFrom_mono`). -/
theorem runFrom_mono {t s : ℕ} (m : Machine t s) :
    ∀ (f : ℕ) (c : Configuration t s) (r : ExecutionReceipt t s),
      runFrom m f c = some r → ∀ j, runFrom m (f + j) c = some r := by
  intro f
  induction f with
  | zero =>
    intro c r h j
    cases j with
    | zero => simpa using h
    | succ j =>
      simp only [runFrom] at h
      split_ifs at h with hh
      simp only [runFrom, hh, if_true]
      exact h
  | succ f ih =>
    intro c r h j
    rw [show f + 1 + j = (f + j) + 1 by omega]
    simp only [runFrom] at h ⊢
    split_ifs at h ⊢ with hh
    · exact h
    · cases hs : step m c with
      | none => simp [hs] at h
      | some next =>
        simp only [hs] at h ⊢
        cases hr : runFrom m f next with
        | none => simp [hr] at h
        | some suffix =>
          simp only [hr] at h
          rw [ih next suffix hr j]
          exact h

/-- Two halted runs from the same configuration have the same result. -/
theorem runFrom_unique {t s : ℕ} (m : Machine t s) (c : Configuration t s) (f f' : ℕ)
    (a b : ExecutionReceipt t s) (ha : runFrom m f c = some a) (hb : runFrom m f' c = some b) :
    a = b := by
  have h1 := runFrom_mono m f c a ha f'
  have h2 := runFrom_mono m f' c b hb f
  rw [Nat.add_comm] at h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- No pair of cutoffs certifies both verdicts. -/
theorem not_certifies_both (v : RepairOrdinary.Verifier) (r r' fuel fuel' : ℕ) (x w : List Bool)
    (hacc : CertifiesAccept v r fuel x w) (hrej : CertifiesReject v r' fuel' x w) : False := by
  obtain ⟨a, ha, haa⟩ := certifiesAccept_genuine v r fuel x w hacc
  obtain ⟨b, hb, hbb⟩ := certifiesReject_genuine v r' fuel' x w hrej
  have hab := runFrom_unique v.machine _ fuel fuel' a b ha hb
  subst hab
  rw [haa] at hbb
  exact Bool.noConfusion hbb

/-- **The useful prefix exists** (proof of `lem:multitape-refuter`): if the original framed run halts within `t`
steps (with fuel `fuel`), then the cutoff `r = t + 2` certifies its actual verdict. -/
theorem certifies_of_halts (v : RepairOrdinary.Verifier) (t fuel : ℕ) (x w : List Bool)
    (receipt : ExecutionReceipt v.tapeCount v.stateCount)
    (hrun : run v.machine fuel (v.inputTapes x w) = some receipt) (ht : receipt.steps ≤ t) :
    (v.accepting receipt.final.control = true → CertifiesAccept v (t + 2) fuel x w) ∧
    (v.accepting receipt.final.control = false → CertifiesReject v (t + 2) fuel x w) := by
  obtain ⟨d, hd, hf⟩ := cutRun_complete v.machine (t + 2) fuel _ _ receipt hrun
    (prefixFaithful_initial _ (t + 2) _) (fun i => by
      simp only [initialConfiguration]
      omega)
  refine ⟨fun h => ⟨d, hd, by rw [hf.control]; exact h⟩, fun h => ⟨d, hd, by rw [hf.control]; exact h⟩⟩

/-- The weak-machine instance (proof of `cor:framed-refuter`, "For each promised computation choose
`r = t_M(N)+2`"): every framed run of a weak machine is certified with its actual verdict at the
cutoff `M.runtime n + 2` and fuel `M.runtime n`. -/
theorem weak_certifies (M : RepairSource.OrdinaryWeakMachine) (n : ℕ) (x : BitInput n)
    (w : BitInput (n / 16)) :
    (M.verifier.acceptsAt (M.runtime n) (List.ofFn x) (List.ofFn w) →
      CertifiesAccept M.verifier (M.runtime n + 2) (M.runtime n) (List.ofFn x) (List.ofFn w)) ∧
    (HaltsRejecting M.verifier (M.runtime n) (List.ofFn x) (List.ofFn w) →
      CertifiesReject M.verifier (M.runtime n + 2) (M.runtime n) (List.ofFn x) (List.ofFn w)) := by
  obtain ⟨receipt, hrun⟩ := M.halts n x w
  have ht := runFrom_steps_le _ _ _ _ hrun
  have hc := certifies_of_halts M.verifier (M.runtime n) (M.runtime n) _ _ receipt hrun ht
  constructor
  · rintro ⟨r', hr', hacc⟩
    rw [hrun] at hr'
    cases hr'
    exact hc.1 hacc
  · rintro ⟨r', hr', hacc⟩
    rw [hrun] at hr'
    cases hr'
    exact hc.2 hacc

end NearCubicGates.Adapters.Refuter
