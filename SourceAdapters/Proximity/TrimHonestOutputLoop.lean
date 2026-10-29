import SourceAdapters.Proximity.TrimHonestOutputStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": restriction emits every retained label in its original
schedule order. Address magnitudes affect width, never loop length. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def outputLoop : St VV MM := .loop (.lt scheduleIndex scheduleLength) outputStep

theorem output_loop {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (input : BitInput n) (proof : BitInput N) :
    ∀ (addresses : List ℕ) (a : DS VV MM) (past : List ℕ),
      Cst a → Ready C V input proof a → a.ram scheduleStore = past ++ addresses →
      a.rc scheduleStore = past.length → a.env scheduleIndex = past.length →
      a.env scheduleLength = past.length + addresses.length →
      (∀ x ∈ addresses, x < 2 ^ C.Wd) → past.length + addresses.length < 2 ^ C.Wd →
      Hs C outputLoop a
        ((6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 38) *
          addresses.length + 2) (fun b =>
        b.out = a.out ++ addresses.map (canonicalClauseProof V input (finiteProofOracle proof)) ∧
        Ready C V input proof b ∧ OutputFrame outputTemps a b) := by
  intro addresses
  induction addresses with
  | nil =>
    intro a past _ ready _ _ hi hlen _ _
    refine ⟨a, 2, Ex.loopF (show scheduleIndex ≠ scheduleLength by decide)
      (by simp [Cnd.eval, hi, hlen]), by simp, ?_⟩
    exact ⟨by simp, ready, OutputFrame.refl _ _⟩
  | cons x xs ih =>
    intro a past hc ready hm hr hi hlen hvalues hwidth
    have ht : (Cnd.lt scheduleIndex scheduleLength).eval a = true := by
      simp [Cnd.eval, hi, hlen]
    have hread : (a.ram scheduleStore).drop (a.rc scheduleStore) = x :: xs := by
      rw [hm, hr, List.drop_left]
    obtain ⟨b, nb, eb, hb, bout, br, bi, rb, fb⟩ :=
      output_step V input proof a hc ready x xs hread (hvalues x (by simp))
        (by rw [hi]; simp only [List.length_cons] at hwidth; omega)
    have bm : b.ram scheduleStore = (past ++ [x]) ++ xs := by
      rw [fb.ram, hm, List.append_assoc]
      rfl
    have bcursor : b.rc scheduleStore = (past ++ [x]).length := by
      rw [br, hr]
      simp
    have bindex : b.env scheduleIndex = (past ++ [x]).length := by rw [bi, hi]; simp
    have blen : b.env scheduleLength = (past ++ [x]).length + xs.length := by
      rw [fb.env scheduleLength (by decide), hlen]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    have bw : (past ++ [x]).length + xs.length < 2 ^ C.Wd := by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hwidth
      omega
    obtain ⟨d, nd, ed, hd, dout, rd, fd⟩ :=
      ih b (past ++ [x]) (fb.constants hc (by decide)) rb bm bcursor bindex blen
        (fun y hy => hvalues y (List.mem_cons_of_mem _ hy)) bw
    refine ⟨d, nb + nd + 2, Ex.loopT (show scheduleIndex ≠ scheduleLength by decide) ht eb ed,
      ?_, ?_⟩
    · calc
        nb + nd + 2 ≤ (6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 36) +
          ((6 * N + 16 * (auxKeys (2 ^ V.randomBits) (blockVariableBound q)).length + 38) * xs.length + 2) + 2 := by omega
        _ = _ := by simp only [List.length_cons]; ring
    · exact ⟨by rw [dout, bout, List.map_cons, List.append_assoc]; rfl, rd, fb.trans fd⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
