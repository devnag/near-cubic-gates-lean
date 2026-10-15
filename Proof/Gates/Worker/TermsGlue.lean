import Proof.Gates.Worker.Terms
import Proof.Gates.Codec.Transcode
import Proof.Gates.Codec.CallPairW

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Codec Format

theorem readMany_circ (w : List Bool) (q p0 n : ℕ) :
    readMany (readCircuit q) n (w.drop p0) = ((List.range n).map (circAt w q p0), w.drop (circPos w q p0 n)) :=
  readMany_iter (readCircuit q) w (fun p => (readCircuit q (w.drop p)).1) (fun p => circuitEnd w p q)
    (fun p => Prod.ext rfl (readCircuit_drop w p q).1) n p0

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

/-- The decoded guess's circuits are the transcoder's `circAt`, from the position after the two circuit fields of the
pair. -/
theorem decodeGuess_circuits_at (N : ℕ) (x : BitInput N) (w : List Bool) (p0 : ℕ)
    (hp0 : (readField (readField w).2).2 = w.drop p0) (j : ℕ) (hj : j < (decodeGuess s P g N x w).auxCount P x) :
    (decodeGuess s P g N x w).circuits j = circAt w (width s g N) p0 j := by
  rw [decodeGuess_circuits, hp0, readMany_circ]
  have hj' : j < (pcpp s P g x (decodeGuess s P g N x w).oracle).proofBits + gadgets s g N := hj
  simp [List.getD_eq_getElem?_getD, hj']

theorem canonList_eq_nil {q : ℕ} (S : Finset (Fin q)) : canonList S = [] ↔ ¬ S.Nonempty := by
  rw [Finset.not_nonempty_iff_eq_empty, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    exact h i ((mem_canonList S i).2 hi)
  · rintro rfl i hi
    simpa using (mem_canonList _ i).1 hi

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

/-- The single/parity call of the meaning is the writer's `oneCallOf` with the canonical parity list. -/
theorem singleCall_eq (ω : ℚ) (j : ℕ) (S : Finset (Fin (width s g N))) (Cs : ℕ → NCircuit (width s g N))
    (hCs : Cs j = G.circuits j) :
    G.singleCall ω j S = oneCallOf Cs j ((canonList S).map Fin.val) ω := by
  unfold singleCall oneCallOf
  by_cases hS : S.Nonempty
  · have hne : (canonList S).map Fin.val ≠ [] := by
      rw [Ne, List.map_eq_nil_iff, canonList_eq_nil]; exact not_not.2 hS
    rw [if_pos hS, if_neg hne, hCs]
  · have he : (canonList S).map Fin.val = [] := by rw [List.map_eq_nil_iff, canonList_eq_nil]; exact hS
    rw [if_neg hS, he, if_pos rfl, hCs]

/-- The pair call of the meaning is the writer's `pairCallOf`. -/
theorem pairCall_eq (ω : ℚ) (i j : ℕ) (Cs : ℕ → NCircuit (width s g N)) (hi : Cs i = G.circuits i)
    (hj : Cs j = G.circuits j) : G.pairCall ω i j = pairCallOf Cs i j ω := by
  unfold pairCall pairCallOf
  rw [hi, hj]

end Guess

end NearCubicGates.Close.Worker
