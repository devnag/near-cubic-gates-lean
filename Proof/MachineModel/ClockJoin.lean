import Proof.MachineModel.ClockLengthReady
import Proof.Foundations.OrdinaryTapeRenaming

/-! Actual clock phase composition at restored physical heads. This is a
local execution lemma, not an imported realization premise. -/
namespace NearCubicWires.RepairOrdinary.ClockJoin
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ReadyRun {t s : ℕ} (p : Machine t s) (budget : ℕ)
    (input output : Fin t → List Bool) : Prop :=
  ∃ r : ExecutionReceipt t s,run p budget input=some r ∧ r.final.tapes=output ∧
    (∀ i,r.final.heads i=0) ∧ r.steps≤budget

theorem join {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (input middle output : Fin t → List Bool)
    (hp : ReadyRun p fp input middle) (hq : ReadyRun q fq middle output) :
    ReadyRun (Composition.machine p q) (fp+1+fq) input output := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := hp
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := hq
  have he : Composition.restart first.final q.start=initialConfiguration q middle := by
    apply configuration_ext
    · rfl
    · funext i; exact hh i
    · exact ht
  have hlast' : runFrom q fq (Composition.restart first.final q.start)=some last := by
    rw [he]
    exact hlast
  have hr := Composition.run_join p q fp fq _ first last hfirst hlast'
  refine ⟨Composition.joinedReceipt first last,hr,hlt,hlh,?_⟩
  dsimp only [Composition.joinedReceipt]
  omega

theorem enlarge {t s : ℕ} (p : Machine t s) (small large : ℕ)
    (input output : Fin t → List Bool) (h : ReadyRun p small input output) (hb : small≤large) :
    ReadyRun p large input output := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  have hmore := run_moreFuel p small (large-small) input r hr
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r,hmore,ht,hh,hs.trans hb⟩

def lifted {t e s : ℕ} (layout : Fin (t+e) ≃ Fin (t+e)) (p : Machine t s) : Machine (t+e) s :=
  TapeRenaming.machine layout (TapeEmbedding.machine e p)

def data {t e : ℕ} (layout : Fin (t+e) ≃ Fin (t+e))
    (localTapes : Fin t → List Bool) (extra : Fin e → List Bool) : Fin (t+e) → List Bool :=
  (Fin.addCases localTapes extra) ∘ layout.symm

theorem lift {t e s : ℕ} (layout : Fin (t+e) ≃ Fin (t+e)) (p : Machine t s)
    (fuel : ℕ) (input output : Fin t → List Bool) (extra : Fin e → List Bool)
    (h : ReadyRun p fuel input output) :
    ReadyRun (lifted layout p) fuel (data layout input extra) (data layout output extra) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  let heads := fun _ : Fin e => 0
  have he := TapeEmbedding.run_embed p heads extra _ _ r hr
  have hr' := TapeRenaming.run_rename layout (TapeEmbedding.machine e p) _ _ _ he
  have hi : TapeRenaming.config layout (TapeEmbedding.config heads extra (initialConfiguration p input))=
      initialConfiguration (lifted layout p) (data layout input extra) := by
    apply configuration_ext
    · rfl
    · funext i
      simp [TapeRenaming.config,TapeEmbedding.config,heads,initialConfiguration]
      exact Fin.addCases (motive := fun j : Fin (t+e) => (Fin.addCases (motive := fun _ : Fin (t+e) => ℕ) (fun _ : Fin t => 0) (fun _ : Fin e => 0)) j=0)
        (fun _ => by simp) (fun _ => by simp) (layout.symm i)
    · rfl
  rw [hi] at hr'
  refine ⟨_,hr',?_,?_,hs⟩
  · funext i
    simp only [TapeRenaming.receipt,TapeRenaming.config,TapeEmbedding.receipt,TapeEmbedding.config,
      data,Function.comp_apply,ht]
  · intro i
    change (Fin.addCases (motive := fun _ : Fin (t+e) => ℕ) r.final.heads heads) (layout.symm i)=0
    exact Fin.addCases (motive := fun j : Fin (t+e) => (Fin.addCases (motive := fun _ : Fin (t+e) => ℕ) r.final.heads heads) j=0)
      (fun j => by simpa using hh j) (fun _ => by simp [heads]) (layout.symm i)

end NearCubicWires.RepairOrdinary.ClockJoin
