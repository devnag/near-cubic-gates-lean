import SourceAdapters.Proximity.TrimHonestOutputLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid rewind and complete raw restriction output from the
actual original-proof, auxiliary, and retained-address stores. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def outputSetup : St VV MM := .seq (.op (.rwM scheduleStore)) (.op (.zero scheduleIndex))
def outputInitial (a : DS VV MM) : DS VV MM := (a.rew scheduleStore).set scheduleIndex 0
def outputProgram : St VV MM := .seq outputSetup outputLoop

theorem output_setup (a : DS VV MM) :
    Ex C outputSetup a (outputInitial a) (a.rc scheduleStore + 3) := by
  simpa only [outputSetup, outputInitial, Nat.add_assoc] using
    Ex.seq (Ex.op (OpEx.rwM (C := C) scheduleStore a))
      (Ex.op (OpEx.zero scheduleIndex (a.rew scheduleStore)))

theorem output_initial_frame (a : DS VV MM) : OutputFrame outputTemps a (outputInitial a) := by
  have h : OutputFrame outputTemps a (a.rew scheduleStore) := by
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    intro m hm
    have hn : m ≠ scheduleStore := by intro he; apply hm; simp [he]
    simp [DS.rew, hn]
  exact h.trans (OutputFrame.set outputTemps _ scheduleIndex 0 (by simp [outputTemps]))

theorem Ready.output_initial {n q N : ℕ} {V : NonadaptiveVerifier n q}
    {input : BitInput n} {proof : BitInput N} {a : DS VV MM} (h : Ready C V input proof a) :
    Ready C V input proof (outputInitial a) := by
  have hr : Ready C V input proof (a.rew scheduleStore) := by
    refine ⟨h.proof_ram, h.proof_len, ?_, h.proof_width, h.keys_ram, h.values_ram,
      h.aux_len, ?_, ?_, h.aux_width⟩
    · simpa [DS.rew, proofStore, scheduleStore] using h.proof_cursor
    · simpa [DS.rew, auxiliaryStore, scheduleStore] using h.aux_cursor
    · simpa [DS.rew, keyStore, scheduleStore] using h.key_cursor
  exact hr.set scheduleIndex 0 (by decide) (by decide)

theorem output_program {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) (a : DS VV MM) (hc : Cst a)
    (ready : Ready C V input proof a) (addresses : List ℕ)
    (hm : a.ram scheduleStore = addresses) (hlen : a.env scheduleLength = addresses.length)
    (hvalues : ∀ x ∈ addresses, x < 2 ^ C.Wd) (hwidth : addresses.length < 2 ^ C.Wd) :
    Hs C outputProgram a
      (a.rc scheduleStore +
        (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 38) *
          addresses.length + 6) (fun b =>
        b.out = a.out ++ addresses.map (canonicalClauseProof V input (finiteProofOracle proof)) ∧
        Ready C V input proof b ∧ OutputFrame outputTemps a b) := by
  have e1 := output_setup (C := C) a
  have f1 := output_initial_frame a
  obtain ⟨b, cost, e2, hcost, bo, rb, fb⟩ :=
    output_loop V input proof addresses (outputInitial a) []
      (f1.constants hc (by decide)) ready.output_initial
      (by rw [f1.ram]; exact hm) (by simp [outputInitial, DS.rew])
      (by simp [outputInitial])
      (by simpa only [List.length_nil, Nat.zero_add] using
        (f1.env scheduleLength (by decide)).trans hlen) hvalues (by simpa using hwidth)
  refine ⟨b, a.rc scheduleStore + 3 + cost + 1, Ex.seq e1 e2, by omega, ?_⟩
  exact ⟨bo, rb, f1.trans fb⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
