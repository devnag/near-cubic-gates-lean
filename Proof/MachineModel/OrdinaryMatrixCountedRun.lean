import Proof.PCP.VerifierDecodingRepeat

/-! Bounded-index application of the existing physical repeat controller.
The body is required only at the positions actually visited by the loop;
the successful exhaustion includes the controller's paid driver rewind. -/
namespace NearCubicWires.RepairOrdinary.MatrixCountedRun
open LocalBitMultitape RepairSource.VerifierDecoding.RepeatMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem driver_run {t s : ℕ} (body : Machine t s) (total cost : ℕ)
    (source : ℕ → Configuration t s)
    (hstart : ∀ i < total, (source i).control = body.start)
    (supplier : ∀ i < total, ∃ r, runFrom body cost (source i) = some r ∧ r.steps ≤ cost ∧
      r.final.heads = (source (i + 1)).heads ∧ r.final.tapes = (source (i + 1)).tapes)
    (n pos : ℕ) (hn : pos + n = total) :
    ∃ r,
      runFrom (machine body (fun _ _ => true)) (n * (cost + 2) + total + 3)
        (cfg 0 (source pos) total (pos + 1)) = some r ∧
      r.steps ≤ n * (cost + 2) + total + 3 ∧ r.final = cfg 3 (source total) total 1 := by
  induction n generalizing pos with
  | zero =>
    have hpos : pos = total := by omega
    subst pos
    obtain ⟨r, hr, hf, hs⟩ := (exhaust body (fun _ _ => true) (source total) total).run
      (by simp [machine, cfg, controlConfig, phaseCode])
    exact ⟨r, by simpa using hr, by simpa using hs.le, hf⟩
  | succ n ih =>
    have hpos : pos < total := by omega
    obtain ⟨r, hr, hs, hh, ht⟩ := supplier pos hpos
    have hp := iteration body (fun _ _ => true) (source pos) total pos r (hstart pos hpos) hpos hr
    simp only [↓reduceIte] at hp
    have he : cfg 0 r.final total (pos + 2) = cfg 0 (source (pos + 1)) total (pos + 2) := by
      apply configuration_ext
      · rfl
      · simp [cfg, controlConfig, TapeEmbedding.config, hh]
      · simp [cfg, controlConfig, TapeEmbedding.config, ht]
    rw [he] at hp
    obtain ⟨tail, htail, hts, htf⟩ := ih (pos + 1) (by omega)
    rcases hp with ⟨space, hp⟩
    have htail' : runFrom (machine body (fun _ _ => true)) (n * (cost + 2) + total + 3)
        (cfg 0 (source (pos + 1)) total (pos + 2)) = some tail := by
      simpa only [Nat.add_assoc] using htail
    obtain ⟨joined, hj, hf, hsteps, _⟩ := hp.followedBy tail htail'
    have hb : (r.steps + 2) + (n * (cost + 2) + total + 3) ≤ (n + 1) * (cost + 2) + total + 3 := by nlinarith
    have hm := runFrom_moreFuel (machine body (fun _ _ => true)) _
      ((n + 1) * (cost + 2) + total + 3 - ((r.steps + 2) + (n * (cost + 2) + total + 3))) _ joined hj
    rw [Nat.add_sub_of_le hb] at hm
    exact ⟨joined, hm, by rw [hsteps]; nlinarith, hf.trans htf⟩

theorem counted_run {t s : ℕ} (body : Machine t s) (total cost : ℕ)
    (source : ℕ → Configuration t s)
    (hstart : ∀ i < total, (source i).control = body.start)
    (supplier : ∀ i < total, ∃ r, runFrom body cost (source i) = some r ∧ r.steps ≤ cost ∧
      r.final.heads = (source (i + 1)).heads ∧ r.final.tapes = (source (i + 1)).tapes) :
    ∃ r,
      runFrom (machine body (fun _ _ => true)) (total * (cost + 3) + 3)
        (cfg 0 (source 0) total 1) = some r ∧
      r.steps ≤ total * (cost + 3) + 3 ∧ r.final = cfg 3 (source total) total 1 := by
  have h := driver_run body total cost source hstart supplier total 0 (by omega)
  have ht : total * (cost + 2) + total + 3 = total * (cost + 3) + 3 := by ring
  simpa only [ht, Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.MatrixCountedRun
