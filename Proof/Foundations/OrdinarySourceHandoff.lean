import Proof.Foundations.OrdinaryTapeRenaming
import Proof.Foundations.OrdinaryCopyComposition

/-! Actual loader-to-source handoff with a fresh source workspace. The source
uses the first t tapes; the loader's framed input and unary counter live on
three additional tapes. Only source input tape zero is filled by the loader.
All remaining source tapes are untouched and empty at entry. -/
namespace NearCubicWires.RepairOrdinary.SourceHandoff
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroTape (t : ℕ) (ht : 0 < t) : Fin (t + 3) := (⟨0, ht⟩ : Fin t).castAdd 3

def layout (t : ℕ) (ht : 0 < t) : Fin (3 + t) ≃ Fin (t + 3) :=
  finAddFlip.trans (Equiv.swap (zeroTape t ht) ((1 : Fin 3).natAdd t))

theorem core_ne_extra {t : ℕ} (i : Fin t) (j : Fin 3) : i.castAdd 3 ≠ j.natAdd t := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

theorem layout_output (t : ℕ) (ht : 0 < t) :
    layout t ht ((1 : Fin 3).castAdd t) = zeroTape t ht := by
  simp [layout]

theorem layout_extra (t : ℕ) (ht : 0 < t) (j : Fin 3) (hj : j ≠ 1) :
    layout t ht (j.castAdd t) = j.natAdd t := by
  have hn : j.natAdd t ≠ (1 : Fin 3).natAdd t := by
    intro h
    apply hj
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hh
    omega
  simp only [layout, Equiv.trans_apply, finAddFlip_apply_castAdd]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm (core_ne_extra ⟨0, ht⟩ j)) hn

theorem layout_core_zero (t : ℕ) (ht : 0 < t) :
    layout t ht ((⟨0, ht⟩ : Fin t).natAdd 3) = (1 : Fin 3).natAdd t := by
  simp [layout, zeroTape]

theorem layout_core (t : ℕ) (ht : 0 < t) (i : Fin t) (hi : i.val ≠ 0) :
    layout t ht (i.natAdd 3) = i.castAdd 3 := by
  have hn : i.castAdd 3 ≠ zeroTape t ht := by
    intro h
    apply hi
    exact congrArg Fin.val h
  simp only [layout, Equiv.trans_apply, finAddFlip_apply_natAdd]
  exact Equiv.swap_apply_of_ne_of_ne hn (core_ne_extra i 1)

def sourceTapes {t : ℕ} (bs : List Bool) : Fin t → List Bool :=
  fun i => if i.val = 0 then bs else []

def extraTapes (bs : List Bool) : Fin 3 → List Bool :=
  fun j => if j.val = 0 then frame bs
    else if j.val = 1 then [] else List.replicate bs.length false

def loader (t : ℕ) (ht : 0 < t) : Machine (t + 3) 5 :=
  TapeRenaming.machine (layout t ht) (TapeEmbedding.machine t Streaming.machine)

def loaderInput (t : ℕ) (ht : 0 < t) (bs : List Bool) : Fin (t + 3) → List Bool :=
  (Fin.addCases (fun j : Fin 3 => if j.val = 0 then frame bs else [])
    (fun _ : Fin t => [])) ∘ (layout t ht).symm

def loaded (t : ℕ) (ht : 0 < t) (bs : List Bool) : Configuration (t + 3) 5 :=
  TapeRenaming.config (layout t ht) (TapeEmbedding.config (fun _ : Fin t => 0)
    (fun _ : Fin t => []) (Streaming.finished (frame bs) bs bs.length))

theorem loaded_heads (t : ℕ) (ht : 0 < t) (bs : List Bool) (i : Fin (t + 3)) :
    (loaded t ht bs).heads i = 0 := by
  change (TapeEmbedding.config (fun _ : Fin t => 0) (fun _ : Fin t => [])
    (Streaming.finished (frame bs) bs bs.length)).heads ((layout t ht).symm i) = 0
  generalize (layout t ht).symm i = j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [TapeEmbedding.config, Streaming.finished, Streaming.config]
  · simp [TapeEmbedding.config]

theorem loaded_tapes (t : ℕ) (ht : 0 < t) (bs : List Bool) :
    (loaded t ht bs).tapes = Fin.addCases (sourceTapes bs) (extraTapes bs) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j.val = 0
    · have heq : j = (⟨0, ht⟩ : Fin t) := Fin.ext hj
      subst j
      change (loaded t ht bs).tapes (zeroTape t ht) = _
      rw [← layout_output]
      simp [loaded, TapeRenaming.config, TapeEmbedding.config,
        Streaming.finished, Streaming.config, sourceTapes]
    · rw [← layout_core t ht j hj]
      simp [loaded, TapeRenaming.config, TapeEmbedding.config, sourceTapes, hj]
  · simp only [Fin.addCases_right]
    by_cases hj : j = 1
    · subst j
      rw [← layout_core_zero t ht]
      simp only [loaded, TapeRenaming.config, Function.comp_apply,
        Equiv.symm_apply_apply, TapeEmbedding.config, Fin.addCases_right]
      rfl
    · have hv : j.val ≠ 1 := by
        intro h
        exact hj (Fin.ext h)
      rw [← layout_extra t ht j hj]
      simp [loaded, TapeRenaming.config, TapeEmbedding.config,
        Streaming.finished, Streaming.config, extraTapes, hv]

theorem loaded_source_entry {s : ℕ} (t : ℕ) (ht : 0 < t)
    (q : Machine t s) (bs : List Bool) :
    Composition.restart (loaded t ht bs) q.start =
      TapeEmbedding.config (fun _ : Fin 3 => 0) (extraTapes bs)
        (initialConfiguration q (sourceTapes bs)) := by
  apply configuration_ext
  · rfl
  · funext i
    change (loaded t ht bs).heads i = _
    rw [loaded_heads]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [TapeEmbedding.config, initialConfiguration]
  · exact loaded_tapes t ht bs

theorem loader_run (t : ℕ) (ht : 0 < t) (bs : List Bool) :
    ∃ receipt : ExecutionReceipt (t + 3) 5,
      run (loader t ht) (4 * bs.length + 2) (loaderInput t ht bs) = some receipt ∧
      receipt.final = loaded t ht bs ∧
      receipt.steps = 4 * bs.length + 2 ∧
      receipt.peakTapeCells ≤ 4 * bs.length + 1 := by
  obtain ⟨r, hr, hf, hs, hp⟩ := Streaming.copy_run bs
  have he := TapeEmbedding.run_embed Streaming.machine (fun _ : Fin t => 0)
    (fun _ : Fin t => []) (4 * bs.length + 2) _ r hr
  have hn := TapeRenaming.run_rename (layout t ht) (TapeEmbedding.machine t Streaming.machine)
    (4 * bs.length + 2) _ _ he
  refine ⟨TapeRenaming.receipt (layout t ht)
    (TapeEmbedding.receipt (fun _ : Fin t => 0) (fun _ : Fin t => []) r), ?_, ?_, ?_, ?_⟩
  · have hzero : ∀ i : Fin (3 + t),
        (TapeEmbedding.config (fun _ : Fin t => 0) (fun _ : Fin t => [])
          (initialConfiguration Streaming.machine
            (fun j : Fin 3 => if j.val = 0 then frame bs else []))).heads i = 0 := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [TapeEmbedding.config, initialConfiguration]
    have hinit : initialConfiguration (loader t ht) (loaderInput t ht bs) =
        TapeRenaming.config (layout t ht)
          (TapeEmbedding.config (fun _ : Fin t => 0) (fun _ : Fin t => [])
            (initialConfiguration Streaming.machine
              (fun j : Fin 3 => if j.val = 0 then frame bs else []))) := by
      apply configuration_ext
      · rfl
      · funext i
        exact (hzero ((layout t ht).symm i)).symm
      · rfl
    change runFrom (loader t ht) _ (initialConfiguration (loader t ht) (loaderInput t ht bs)) = _
    rw [hinit]
    exact hn
  · exact congrArg (fun c => TapeRenaming.config (layout t ht)
      (TapeEmbedding.config (fun _ : Fin t => 0) (fun _ : Fin t => []) c)) hf
  · exact hs
  · simpa [TapeRenaming.receipt, TapeEmbedding.receipt, TapeEmbedding.extraCells] using hp

@[simp] theorem extra_cells (bs : List Bool) :
    TapeEmbedding.extraCells (extraTapes bs) = 3 * bs.length + 1 := by
  simp [TapeEmbedding.extraCells, extraTapes, Fin.sum_univ_succ]
  omega

theorem source_handoff {t s : ℕ} (ht : 0 < t) (q : Machine t s)
    (bs : List Bool) (fuel : ℕ) (next : ExecutionReceipt t s)
    (hq : run q fuel (sourceTapes bs) = some next) :
    ∃ receipt : ExecutionReceipt (t + 3) (5 + s),
      run (Composition.machine (loader t ht) (TapeEmbedding.machine 3 q))
        (4 * bs.length + 3 + fuel) (loaderInput t ht bs) = some receipt ∧
      (∀ i : Fin t, receipt.final.tapes (i.castAdd 3) = next.final.tapes i) ∧
      receipt.steps = 4 * bs.length + 3 + next.steps ∧
      receipt.peakTapeCells ≤ max (4 * bs.length + 1)
        (next.peakTapeCells + 3 * bs.length + 1) := by
  obtain ⟨copied, hc, hf, hs, hp⟩ := loader_run t ht bs
  have he := TapeEmbedding.run_embed q (fun _ : Fin 3 => 0) (extraTapes bs)
    fuel _ next hq
  have hnext : runFrom (TapeEmbedding.machine 3 q) fuel
      (Composition.restart copied.final q.start) =
      some (TapeEmbedding.receipt (fun _ : Fin 3 => 0) (extraTapes bs) next) := by
    rw [hf, loaded_source_entry]
    exact he
  have hjoin := Composition.run_join (loader t ht) (TapeEmbedding.machine 3 q)
    (4 * bs.length + 2) fuel _ copied _ hc hnext
  refine ⟨Composition.joinedReceipt copied
    (TapeEmbedding.receipt (fun _ : Fin 3 => 0) (extraTapes bs) next), ?_, ?_, ?_, ?_⟩
  · simpa [run, initialConfiguration, Composition.machine, Composition.leftConfig,
      Nat.add_assoc] using hjoin
  · intro i
    simp [Composition.joinedReceipt, Composition.rightConfig, TapeEmbedding.receipt,
      TapeEmbedding.config]
  · simp [Composition.joinedReceipt, TapeEmbedding.receipt, hs, Nat.add_assoc]
  · simpa [Composition.joinedReceipt, TapeEmbedding.receipt, Nat.add_assoc] using
      (max_le_max_right (next.peakTapeCells + TapeEmbedding.extraCells (extraTapes bs)) hp)

end NearCubicWires.RepairOrdinary.SourceHandoff
