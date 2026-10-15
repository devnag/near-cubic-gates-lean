import Proof.PCP.VerifierDecodingRepeatBody

/-! Complete bounded repetition theorem for the three decoder scans. The
only body supplier is an actual ordinary interpreter receipt; its endpoints
include all tapes and heads. No cursor reset or arithmetic computation is
hidden in the semantic transition used to state the loop's result. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def iterate {α : Type} (next : α → Bool × α) : ℕ → α → Bool × α
  | 0,x => (true,x)
  | n+1,x => if (next x).1 then iterate next n (next x).2 else next x

noncomputable def Result {α : Type} {t s : ℕ} (source : α → Configuration t s)
    (total : ℕ) (out : Bool × α) (final : Configuration (t+1) (Fintype.card (Control s))) : Prop :=
  if out.1 then final = cfg 3 (source out.2) total 1 else final.control = phaseCode s 4

private theorem cfg_eq {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total head : ℕ)
    (hh : c.heads = d.heads) (ht : c.tapes = d.tapes) : cfg phase c total head = cfg phase d total head := by
  apply configuration_ext
  · rfl
  · simp [cfg,controlConfig,TapeEmbedding.config,hh]
  · simp [cfg,controlConfig,TapeEmbedding.config,ht]

/-- All loop counts come from the literal driver. A successful exhaustion
restores it to head1; a failing body halts the whole loop immediately. -/
theorem driver_run {α : Type} {t s : ℕ} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : α → Configuration t s)
    (next : α → Bool × α) (Inv : α → Prop) (cost : ℕ)
    (hstart : ∀ x, Inv x → (source x).control = body.start)
    (supplier : ∀ x, Inv x → ∃ r, runFrom body cost (source x) = some r ∧ r.steps ≤ cost ∧
      r.final.heads = (source (next x).2).heads ∧ r.final.tapes = (source (next x).2).tapes ∧
      accepted r.final.control r.final.scanned = (next x).1 ∧ ((next x).1 = true → Inv (next x).2))
    (n total pos : ℕ) (x : α) (hx : Inv x) (hn : pos+n=total) :
    ∃ receipt,
      runFrom (machine body accepted) (n*(cost+2)+total+3) (cfg 0 (source x) total (pos+1)) = some receipt ∧
      receipt.steps ≤ n*(cost+2)+total+3 ∧ Result source total (iterate next n x) receipt.final := by
  induction n generalizing pos x with
  | zero =>
    have hpos : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (exhaust body accepted (source x) total).run
      (by simp [machine,cfg,controlConfig,phaseCode])
    exact ⟨r,by simpa using hr,by simpa using hs.le,by simpa [Result,iterate] using hf⟩
  | succ n ih =>
    obtain ⟨r,hr,hrt,hrh,hrp,hra,hinv⟩ := supplier x hx
    have hp := iteration body accepted (source x) total pos r (hstart x hx) (by omega) hr
    rw [hra] at hp
    cases hb : (next x).1 with
    | false =>
      simp only [hb,Bool.false_eq_true,↓reduceIte] at hp
      obtain ⟨result,hresult,hfinal,hsteps⟩ := hp.run (by simp [machine,cfg,controlConfig,phaseCode])
      have htime : r.steps+2 ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine body accepted) (r.steps+2)
        ((n+1)*(cost+2)+total+3-(r.steps+2)) _ result hresult
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,by omega,?_⟩
      simp [Result,iterate,hb,hfinal,cfg,controlConfig]
    | true =>
      simp only [hb,↓reduceIte] at hp
      have he := cfg_eq 0 r.final (source (next x).2) total (pos+2) hrh hrp
      rw [he] at hp
      obtain ⟨tail,htail,htt,htf⟩ := ih (pos+1) (next x).2 (hinv hb) (by omega)
      rcases hp with ⟨space,hp⟩
      obtain ⟨result,hresult,hfinal,hsteps,_⟩ := hp.followedBy tail htail
      have htime : (r.steps+2)+(n*(cost+2)+total+3) ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine body accepted) _
        ((n+1)*(cost+2)+total+3-((r.steps+2)+(n*(cost+2)+total+3))) _ result hresult
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,?_,?_⟩
      · rw [hsteps]
        nlinarith
      · simpa only [Result,iterate,hb,↓reduceIte,hfinal] using htf

/-- The whole repeated consumer, including its final paid driver rewind. -/
theorem repeat_run {α : Type} {t s : ℕ} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : α → Configuration t s)
    (next : α → Bool × α) (Inv : α → Prop) (cost : ℕ)
    (hstart : ∀ x, Inv x → (source x).control = body.start)
    (supplier : ∀ x, Inv x → ∃ r, runFrom body cost (source x) = some r ∧ r.steps ≤ cost ∧
      r.final.heads = (source (next x).2).heads ∧ r.final.tapes = (source (next x).2).tapes ∧
      accepted r.final.control r.final.scanned = (next x).1 ∧ ((next x).1 = true → Inv (next x).2))
    (total : ℕ) (x : α) (hx : Inv x) :
    ∃ receipt,
      runFrom (machine body accepted) (total*(cost+3)+3) (cfg 0 (source x) total 1) = some receipt ∧
      receipt.steps ≤ total*(cost+3)+3 ∧ Result source total (iterate next total x) receipt.final := by
  have h := driver_run body accepted source next Inv cost hstart supplier total total 0 x hx (by omega)
  have he : total*(cost+2)+total+3=total*(cost+3)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
