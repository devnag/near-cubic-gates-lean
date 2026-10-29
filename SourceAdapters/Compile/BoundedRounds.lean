import SourceAdapters.Compile.BoundedMachine

/-!
proof of `lem:multitape-refuter`, Step 3: iterate the finite window for the supplied clock.
The finite-window multi-round relation follows from the single-step relation and the head-movement bound.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.LocalBitMultitape

set_option autoImplicit false

def MachineWindow.rounds {t s width : ℕ} (machine : Machine t s) :
    ℕ → MachineWindow t s width → Option (MachineWindow t s width)
  | 0, a => some a
  | fuel + 1, a => (a.advance machine).bind (MachineWindow.rounds machine fuel)

theorem machineAdvance_heads_le {t s : ℕ} (machine : Machine t s)
    {c d : Configuration t s} (h : machineAdvance machine c = some d) (tape : Fin t) :
    d.heads tape ≤ c.heads tape + 1 := by
  by_cases hh : machine.halted c.control = true
  · have he : c = d := by simpa [machineAdvance, hh] using h
    subst d
    omega
  · have hs : step machine c = some d := by simpa [machineAdvance, hh] using h
    exact Refuter.step_heads_le machine hs tape

/-- Exact finite-window iteration as long as every visited cell fits.
The width depends only on the supplied clock and initial heads, not on a
promised accepting computation or a proof-only runtime function. -/
theorem MachineWindow.rounds_correct {t s width : ℕ} (machine : Machine t s)
    (fuel : ℕ) {a : MachineWindow t s width} {c : Configuration t s}
    (h : a.Represents c) (hroom : ∀ tape, c.heads tape + fuel < width) :
    (a.rounds machine fuel = none ∧ machineRounds machine fuel c = none) ∨
      ∃ b d, a.rounds machine fuel = some b ∧ machineRounds machine fuel c = some d ∧
        b.Represents d := by
  induction fuel generalizing a c with
  | zero => exact Or.inr ⟨a, c, rfl, rfl, h⟩
  | succ fuel ih =>
      have hstepRoom : ∀ tape, c.heads tape + 1 < width := by
        intro tape
        have hb := hroom tape
        omega
      rcases MachineWindow.advance_correct machine h hstepRoom with
        ⟨ha, hc⟩ | ⟨b, d, ha, hc, hd⟩
      · left
        simp [MachineWindow.rounds, machineRounds, ha, hc]
      · have hnextRoom : ∀ tape, d.heads tape + fuel < width := by
          intro tape
          have hm := machineAdvance_heads_le machine hc tape
          have hb := hroom tape
          omega
        rcases ih hd hnextRoom with ⟨hb, he⟩ | ⟨last, final, hb, he, hf⟩
        · left
          simp [MachineWindow.rounds, machineRounds, ha, hc, hb, he]
        · right
          exact ⟨last, final, by simp [MachineWindow.rounds, ha, hb],
            by simp [machineRounds, hc, he], hf⟩

/-- Boolean verdict of the fixed finite rounds; only genuine halted states
can accept, so an exhausted nonhalting clock is rejected. -/
def MachineWindow.accepted {t s width : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) (fuel : ℕ) (a : MachineWindow t s width) : Bool :=
  match a.rounds machine fuel with
  | none => false
  | some final => machine.halted final.control && accepting final.control

/-- The ordinary round semantics has the actual bounded accepting verdict. -/
theorem machineRounds_accepted_iff {t s : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) (fuel : ℕ) (c : Configuration t s) :
    (∃ final, machineRounds machine fuel c = some final ∧
      machine.halted final.control = true ∧ accepting final.control = true) ↔
    ∃ receipt, runFrom machine fuel c = some receipt ∧ accepting receipt.final.control = true := by
  have h := machineRounds_halted_eq_run machine fuel c
  constructor
  · rintro ⟨final, hr, hh, ha⟩
    rw [hr] at h
    simp only [Option.bind_some, hh, ↓reduceIte] at h
    cases he : runFrom machine fuel c with
    | none => simp [he] at h
    | some receipt =>
        have hf : final = receipt.final := by simpa [he] using h
        exact ⟨receipt, rfl, hf ▸ ha⟩
  · rintro ⟨receipt, hr, ha⟩
    rw [hr] at h
    cases he : machineRounds machine fuel c with
    | none => simp [he] at h
    | some final =>
        rw [he] at h
        simp only [Option.bind_some, Option.map_some] at h
        split at h
        · next hh =>
          have hf : final = receipt.final := Option.some.inj h
          exact ⟨final, rfl, hh, hf ▸ ha⟩
        · contradiction

/-- proof of `lem:multitape-refuter`, Step 3: arbitrary bounded computation acceptance is preserved by
the finite window, including zero fuel and early halts. -/
theorem MachineWindow.accepted_iff {t s width : ℕ} (machine : Machine t s)
    (accepting : Fin s → Bool) (fuel : ℕ) {a : MachineWindow t s width}
    {c : Configuration t s} (h : a.Represents c)
    (hroom : ∀ tape, c.heads tape + fuel < width) :
    a.accepted machine accepting fuel = true ↔
      ∃ receipt, runFrom machine fuel c = some receipt ∧ accepting receipt.final.control = true := by
  rw [← machineRounds_accepted_iff]
  rcases MachineWindow.rounds_correct machine fuel h hroom with
    ⟨ha, hc⟩ | ⟨b, d, ha, hc, hd⟩
  · simp [MachineWindow.accepted, ha, hc]
  · simp [MachineWindow.accepted, ha, hc, hd.control]

end NearCubicGates.Adapters.Compile
