import Proof.Foundations.OrdinarySourceHandoff

/-! The source handoff on canonical external tape zero. The change of external
tape convention is a proved static controller renaming; loading and rewind
remain actual transitions. This places raw-stream operations in WordFunction. -/
namespace NearCubicWires.RepairOrdinary.FramedSource
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameTape (t : ℕ) : Fin (t + 3) := (0 : Fin 3).natAdd t

def inputLayout (t : ℕ) (ht : 0 < t) : Fin (t + 3) ≃ Fin (t + 3) :=
  Equiv.swap (SourceHandoff.zeroTape t ht) (frameTape t)

theorem loader_input (t : ℕ) (ht : 0 < t) (bs : List Bool) (i : Fin (t + 3)) :
    SourceHandoff.loaderInput t ht bs i = if i = frameTape t then frame bs else [] := by
  obtain ⟨j, rfl⟩ := (SourceHandoff.layout t ht).surjective i
  have he : SourceHandoff.layout t ht ((0 : Fin 3).castAdd t) = frameTape t :=
    SourceHandoff.layout_extra t ht 0 (by decide)
  rw [← he]
  simp only [SourceHandoff.loaderInput, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [Fin.addCases_left, Fin.ext_iff, Fin.val_castAdd]
    rfl
  · have hn : k.natAdd 3 ≠ (0 : Fin 3).castAdd t := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp only [Fin.addCases_right, if_neg hn]

theorem input_tapes (t : ℕ) (ht : 0 < t) (bs : List Bool) :
    SourceHandoff.loaderInput t ht bs ∘ (inputLayout t ht).symm =
      (fun i : Fin (t + 3) => if i.val = 0 then frame bs else []) := by
  funext i
  simp only [Function.comp_apply, loader_input]
  have he : (inputLayout t ht).symm i = frameTape t ↔ i.val = 0 := by
    rw [Equiv.symm_apply_eq]
    change i = Equiv.swap (SourceHandoff.zeroTape t ht) (frameTape t) (frameTape t) ↔ _
    rw [Equiv.swap_apply_right]
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  simp only [he]

def rawWrapper {s : ℕ} (t : ℕ) (ht : 0 < t) (q : Machine t s) : Machine (t + 3) (5 + s) :=
  Composition.machine (SourceHandoff.loader t ht) (TapeEmbedding.machine 3 q)

def machine {s : ℕ} (t : ℕ) (ht : 0 < t) (q : Machine t s) : Machine (t + 3) (5 + s) :=
  TapeRenaming.machine (inputLayout t ht) (rawWrapper t ht q)

theorem source_handoff {t s : ℕ} (ht : 0 < t) (q : Machine t s)
    (bs : List Bool) (fuel : ℕ) (next : ExecutionReceipt t s)
    (hq : run q fuel (SourceHandoff.sourceTapes bs) = some next) :
    ∃ r : ExecutionReceipt (t + 3) (5 + s),
      run (machine t ht q) (4 * bs.length + 3 + fuel)
        (fun i => if i.val = 0 then frame bs else []) = some r ∧
      (∀ i : Fin t, r.final.tapes (inputLayout t ht (i.castAdd 3)) = next.final.tapes i) ∧
      r.steps = 4 * bs.length + 3 + next.steps ∧
      r.peakTapeCells ≤ max (4 * bs.length + 1)
        (next.peakTapeCells + 3 * bs.length + 1) := by
  obtain ⟨raw, hr, hout, hs, hp⟩ := SourceHandoff.source_handoff ht q bs fuel next hq
  have hn := TapeRenaming.run_rename (inputLayout t ht) (rawWrapper t ht q)
    (4 * bs.length + 3 + fuel) _ raw hr
  have hinit : initialConfiguration (machine t ht q)
        (fun i => if i.val = 0 then frame bs else []) =
      TapeRenaming.config (inputLayout t ht)
        (initialConfiguration (rawWrapper t ht q) (SourceHandoff.loaderInput t ht bs)) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact (input_tapes t ht bs).symm
  refine ⟨TapeRenaming.receipt (inputLayout t ht) raw, ?_, ?_, hs, hp⟩
  · change runFrom (machine t ht q) _ _ = _
    rw [hinit]
    exact hn
  · intro i
    simpa [TapeRenaming.receipt, TapeRenaming.config] using hout i

theorem source_tape_fresh (t : ℕ) (ht : 0 < t) (i : Fin t) :
    (inputLayout t ht (i.castAdd 3)).val ≠ 0 := by
  intro h
  have hi : inputLayout t ht (i.castAdd 3) = SourceHandoff.zeroTape t ht := Fin.ext h
  have he : inputLayout t ht (frameTape t) = SourceHandoff.zeroTape t ht := by
    simp [inputLayout]
  have hn := (inputLayout t ht).injective (hi.trans he.symm)
  exact SourceHandoff.core_ne_extra i 0 hn

def program {t s : ℕ} (ht : 0 < t) (q : Machine t s) (output : Fin t) : Program where
  tapeCount := t + 3
  stateCount := 5 + s
  twoTapes := by omega
  machine := machine t ht q
  outputTape := inputLayout t ht (output.castAdd 3)
  outputFresh := source_tape_fresh t ht output

def ofRaw {Request : Type} {t s : ℕ} (ht : 0 < t) (q : Machine t s) (tape : Fin t)
    (input output : Request → List Bool) (budget : Request → ℕ)
    (realizes : ∀ req, ∃ r : ExecutionReceipt t s,
      run q (budget req) (SourceHandoff.sourceTapes (input req)) = some r ∧
      r.final.tapes tape = output req) :
    WordFunction Request input output (fun req => 4 * (input req).length + 3 + budget req) where
  program := program ht q tape
  realizes := by
    intro req
    obtain ⟨raw, hr, ho⟩ := realizes req
    obtain ⟨r, hrun, hout, _, _⟩ := source_handoff ht q (input req) (budget req) raw hr
    exact ⟨r, hrun, (hout tape).trans ho⟩

end NearCubicWires.RepairOrdinary.FramedSource
