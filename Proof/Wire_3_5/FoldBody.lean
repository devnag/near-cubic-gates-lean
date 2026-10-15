import Proof.Wire_3_5.FoldLoop
import Proof.Hierarchy.HierarchyBinaryPower
import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.OrdinaryZeroPadding

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- **A ready run survives `false`-padding** of every tape to its capacity. -/
theorem ready_pad {t s : ℕ} (p : Machine t s) (cost : ℕ) (input output : Fin t → List Bool) (cap : Fin t → ℕ)
    (h : ClockJoin.ReadyRun p cost input output) :
    ClockJoin.ReadyRun p cost (fun i => ZeroPadding.pad (cap i) (input i))
      (fun i => ZeroPadding.pad (cap i) (output i)) := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  obtain ⟨r', hr', hf, hsteps, _⟩ := ZeroPadding.run_config p cap cost _ r hr
  refine ⟨r', hr', ?_, ?_, ?_⟩
  · rw [hf]; funext i; simp only [ZeroPadding.config, ht]
  · intro i; rw [hf]; exact hh i
  · omega

section Body
variable {tw sw ks : ℕ}

/-- The capacity of each worker tape: `total` on the scratch slots, `0` (no padding) on the ports. -/
noncomputable def scratchCap (scratch : Fin ks → Fin tw) (total : ℕ) (i : Fin tw) : ℕ := by
  classical
  exact if ∃ j, scratch j = i then total else 0

/-- The worker's tapes with the scratch padded with `false` to `total`. -/
noncomputable def padScratch (scratch : Fin ks → Fin tw) (total : ℕ) (X : Fin tw → List Bool) : Fin tw → List Bool :=
  fun i => ZeroPadding.pad (scratchCap scratch total i) (X i)

/-- The worker's tapes with the scratch emptied. -/
noncomputable def blankScratch (scratch : Fin ks → Fin tw) (X : Fin tw → List Bool) : Fin tw → List Bool := by
  classical
  exact fun i => if ∃ j, scratch j = i then [] else X i

/-- The round's tapes: the worker's tapes, the erase driver `1^total` and the capacity tape `0^capT`. -/
def roundTapes (X : Fin tw → List Bool) (total capT : ℕ) : Fin (tw + 2) → List Bool :=
  Fin.addCases X ![List.replicate total true, List.replicate capT false]

/-- The erase machine's slots: the worker's scratch, then the driver and the capacity tape. -/
def eraseSlots (scratch : Fin ks → Fin tw) (j : Fin (ks + 1 + 1)) : Fin (tw + 2) :=
  if h : j.val < ks then (scratch ⟨j.val, h⟩).castAdd 2 else ⟨tw + (j.val - ks), by have := j.isLt; omega⟩

theorem eraseSlots_injective (scratch : Fin ks → Fin tw) (hinj : Function.Injective scratch) :
    Function.Injective (eraseSlots scratch) := by
  intro a b he
  have hv := congrArg Fin.val he
  unfold eraseSlots at hv
  have ha := a.isLt
  have hb := b.isLt
  split_ifs at hv with h1 h2 h2
  · have := hinj (Fin.ext (by simpa using hv) : scratch ⟨a.val, h1⟩ = scratch ⟨b.val, h2⟩)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · have := (scratch ⟨a.val, h1⟩).isLt; simp at hv; omega
  · have := (scratch ⟨b.val, h2⟩).isLt; simp at hv; omega
  · exact Fin.ext (by simp at hv; omega)

theorem eraseSlots_scratch (scratch : Fin ks → Fin tw) (j : Fin ks) :
    eraseSlots scratch (Fin.castAdd 1 (Fin.castAdd 1 j)) = (scratch j).castAdd 2 := by
  unfold eraseSlots; simp

theorem eraseSlots_driver (scratch : Fin ks → Fin tw) :
    eraseSlots scratch (Fin.castAdd 1 (Fin.natAdd ks (0 : Fin 1))) = Fin.natAdd tw (0 : Fin 2) := by
  unfold eraseSlots; apply Fin.ext; simp

theorem eraseSlots_capacity (scratch : Fin ks → Fin tw) :
    eraseSlots scratch (Fin.natAdd (ks + 1) (0 : Fin 1)) = Fin.natAdd tw (1 : Fin 2) := by
  unfold eraseSlots; apply Fin.ext; simp

theorem eraseSlots_cases (j : Fin (ks + 1 + 1)) :
    (∃ j' : Fin ks, j = Fin.castAdd 1 (Fin.castAdd 1 j')) ∨ j = Fin.castAdd 1 (Fin.natAdd ks (0 : Fin 1)) ∨
      j = Fin.natAdd (ks + 1) (0 : Fin 1) := by
  have := j.isLt
  by_cases h : j.val < ks
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext (by simp)⟩
  · by_cases h2 : j.val = ks
    · exact Or.inr (Or.inl (Fin.ext (by simp; omega)))
    · exact Or.inr (Or.inr (Fin.ext (by simp; omega)))

/-- **One copy round**: the worker, the erase of its scratch, and the advance to the next copy. -/
noncomputable def foldBody {sa : ℕ} (worker : Machine tw sw) (scratch : Fin ks → Fin tw)
    (advance : Machine (tw + 2) sa) :=
  Composition.machine (TapeEmbedding.machine 2 worker)
    (Composition.machine (RecoveryFocus.machine (eraseSlots scratch) (RecoveryScratchErase.resetMachine ks)) advance)

theorem scratchCap_slot (scratch : Fin ks → Fin tw) (total : ℕ) (j : Fin ks) :
    scratchCap scratch total (scratch j) = total := by
  unfold scratchCap; rw [if_pos ⟨j, rfl⟩]

theorem padScratch_blank (scratch : Fin ks → Fin tw) (_hinj : Function.Injective scratch) (total : ℕ)
    (X : Fin tw → List Bool) (j : Fin ks) :
    padScratch scratch total (blankScratch scratch X) (scratch j) = List.replicate total false := by
  unfold padScratch blankScratch
  rw [scratchCap_slot, if_pos ⟨j, rfl⟩]
  simp [ZeroPadding.pad]

/-- **The copy round is ready**: from the worker's run on empty scratch (leaving at most `total` cells of scratch) and
the advance's run, the round takes the padded tapes of this round to those of the next. -/
theorem foldBody_ready {sa : ℕ} (worker : Machine tw sw) (scratch : Fin ks → Fin tw)
    (hinj : Function.Injective scratch) (advance : Machine (tw + 2) sa) (total capT cw ca : ℕ)
    (hcap : total + 1 ≤ capT) (P P' Pn : Fin tw → List Bool)
    (hwork : ClockJoin.ReadyRun worker cw P P')
    (hlen : ∀ j, (P' (scratch j)).length ≤ total)
    (hadv : ClockJoin.ReadyRun advance ca (roundTapes (padScratch scratch total (blankScratch scratch P')) total capT)
      (roundTapes (padScratch scratch total Pn) total capT)) :
    ClockJoin.ReadyRun (foldBody worker scratch advance) (cw + 1 + (2 * total + 4 + 1 + ca))
      (roundTapes (padScratch scratch total P) total capT) (roundTapes (padScratch scratch total Pn) total capT) := by
  -- the worker on padded scratch, lifted past the two erase tapes
  have h1 := ready_pad worker cw P P' (scratchCap scratch total) hwork
  obtain ⟨r1, hr1, ht1, hh1, hs1⟩ := h1
  have hw : ClockJoin.ReadyRun (TapeEmbedding.machine 2 worker) cw
      (roundTapes (padScratch scratch total P) total capT) (roundTapes (padScratch scratch total P') total capT) := by
    have he := TapeEmbedding.run_embed worker (fun _ => 0) ![List.replicate total true, List.replicate capT false]
      cw _ r1 hr1
    refine ⟨TapeEmbedding.receipt (fun _ => 0) ![List.replicate total true, List.replicate capT false] r1,
      ?_, ?_, ?_, ?_⟩
    · have hi : initialConfiguration (TapeEmbedding.machine 2 worker) (roundTapes (padScratch scratch total P) total capT) =
          TapeEmbedding.config (fun _ => 0) ![List.replicate total true, List.replicate capT false]
            (initialConfiguration worker (padScratch scratch total P)) := by
        apply configuration_ext
        · rfl
        · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
            simp [initialConfiguration, TapeEmbedding.config]
        · rfl
      unfold run; rw [hi]; exact he
    · simp only [TapeEmbedding.receipt, TapeEmbedding.config]
      rw [ht1]; rfl
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [TapeEmbedding.receipt, TapeEmbedding.config, hh1]
    · simpa [TapeEmbedding.receipt] using hs1
  -- the erase of the scratch slots
  have hb : ∀ j, (padScratch scratch total P' (scratch j)).length ≤ total := by
    intro j
    unfold padScratch; rw [scratchCap_slot]
    simp [ZeroPadding.pad]; have := hlen j; omega
  have he0 := RecoveryScratchErase.erase_ready total capT (fun j => padScratch scratch total P' (scratch j)) hb
  have hmax : max capT (total + 1) = capT := max_eq_left hcap
  rw [hmax] at he0
  obtain ⟨re, hre, hte, hhe, hse⟩ := he0
  have hin : ∀ j, roundTapes (padScratch scratch total P') total capT (eraseSlots scratch j) =
      Fin.addCases (Fin.addCases (fun j => padScratch scratch total P' (scratch j))
        (fun _ : Fin 1 => List.replicate total true)) (fun _ : Fin 1 => List.replicate capT false) j := by
    intro j
    rcases eraseSlots_cases j with ⟨j', rfl⟩ | rfl | rfl
    · rw [eraseSlots_scratch]; simp [roundTapes]
    · rw [eraseSlots_driver]; simp [roundTapes]
    · rw [eraseSlots_capacity]; simp [roundTapes]
  have hE := ClockJoin.ReadyRun.focus (p := RecoveryScratchErase.resetMachine ks) (n := 2 * total + 4)
    ⟨re, hre, hte, hhe, hse.le⟩ (eraseSlots scratch) (eraseSlots_injective scratch hinj)
    (roundTapes (padScratch scratch total P') total capT) hin
  have hEout : install (eraseSlots scratch) (roundTapes (padScratch scratch total P') total capT)
      (Fin.addCases (Fin.addCases (fun _ : Fin ks => List.replicate total false)
        (fun _ : Fin 1 => List.replicate total true)) (fun _ : Fin 1 => List.replicate capT false)) =
      roundTapes (padScratch scratch total (blankScratch scratch P')) total capT := by
    have hinjE := eraseSlots_injective scratch hinj
    funext i
    refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
    · by_cases hs : ∃ j, scratch j = i'
      · obtain ⟨j, rfl⟩ := hs
        conv_lhs => rw [← eraseSlots_scratch, install_slot _ hinjE]
        simp only [Fin.addCases_left, roundTapes]
        rw [padScratch_blank scratch hinj]
      · rw [install_other]
        · simp only [roundTapes, Fin.addCases_left]
          unfold padScratch blankScratch scratchCap
          rw [if_neg hs, if_neg hs]
        · intro j hj
          rcases eraseSlots_cases j with ⟨j', rfl⟩ | rfl | rfl
          · rw [eraseSlots_scratch] at hj
            exact hs ⟨j', Fin.castAdd_injective _ _ hj⟩
          · rw [eraseSlots_driver] at hj; have := congrArg Fin.val hj; simp at this; omega
          · rw [eraseSlots_capacity] at hj; have := congrArg Fin.val hj; simp at this; omega
    · obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      · conv_lhs => rw [← eraseSlots_driver, install_slot _ hinjE]
        simp [roundTapes]
      · conv_lhs => rw [← eraseSlots_capacity, install_slot _ hinjE]
        simp [roundTapes]
  rw [hEout] at hE
  have hjoin := ClockJoin.join _ _ _ _ _ _ _ hE hadv
  exact ClockJoin.join _ _ _ _ _ _ _ hw hjoin

/-- **The uniform fold**: `c` copy rounds on one reused bank. If round `i` starts from the worker tapes `Q i`, the
worker ends at `Q' i` (at most `total` scratch cells), and the advance takes the erased `Q' i` to `Q (i+1)`, then the
loop takes `Q 0` to `Q c`, with the unary copy count `c` on the counter tape. -/
theorem uniformFold_ready {sa : ℕ} (worker : Machine tw sw) (scratch : Fin ks → Fin tw)
    (hinj : Function.Injective scratch) (advance : Machine (tw + 2) sa) (total capT cw ca c : ℕ)
    (hcap : total + 1 ≤ capT) (Q Q' : ℕ → Fin tw → List Bool)
    (hwork : ∀ i, i < c → ClockJoin.ReadyRun worker cw (Q i) (Q' i))
    (hlen : ∀ i, i < c → ∀ j, (Q' i (scratch j)).length ≤ total)
    (hadv : ∀ i, i < c → ClockJoin.ReadyRun advance ca
      (roundTapes (padScratch scratch total (blankScratch scratch (Q' i))) total capT)
      (roundTapes (padScratch scratch total (Q (i + 1))) total capT)) :
    ClockJoin.ReadyRun (foldLoop (foldBody worker scratch advance))
      (1 + 1 + (c * (cw + 1 + (2 * total + 4 + 1 + ca) + 2) + c + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scratch total (Q 0)) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c))
      (Fin.addCases (roundTapes (padScratch scratch total (Q c)) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) :=
  foldLoop_ready (foldBody worker scratch advance) (fun i => roundTapes (padScratch scratch total (Q i)) total capT)
    _ c (fun i hi => foldBody_ready worker scratch hinj advance total capT cw ca hcap (Q i) (Q' i) (Q (i + 1))
      (hwork i hi) (hlen i hi) (hadv i hi))

end Body

end NearCubicWires.WireExponent3_5.Transfer
