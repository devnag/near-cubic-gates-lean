import Proof.Gates.CellsGatherE.QSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.QueryPass

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.RecordEmission (GW eG2 qScratch)

def qT : Fin VV := ⟨74, by decide⟩    -- the tag (position of the next query record)
def qPi : Fin VV := ⟨75, by decide⟩   -- part index
def qNP : Fin VV := ⟨76, by decide⟩   -- number of parts
def qJ : Fin VV := ⟨77, by decide⟩    -- prime index
def qIdx : Fin VV := ⟨78, by decide⟩  -- store index
def qQR : Fin VV := ⟨79, by decide⟩   -- `q^{roleCount}`
def qPw : Fin VV := ⟨80, by decide⟩   -- power loop counter
def qX : Fin VV := ⟨81, by decide⟩    -- temporary
def qR : Fin VV := ⟨82, by decide⟩    -- record

/-! ## Generic: Horner, tagged records, emission loops -/

/-- The tagged query records of the keys `L`, tags from `n`. -/
def QR (Z : ℕ) (L : List ℕ) (n : ℕ) : List ℕ := (L.zipIdx n).map fun e => qRec Z e.1 e.2

theorem QR_append (Z : ℕ) (L1 L2 : List ℕ) (n : ℕ) : QR Z (L1 ++ L2) n = QR Z L1 n ++ QR Z L2 (n + L1.length) := by
  unfold QR; rw [List.zipIdx_append, List.map_append]

theorem QR_single (Z k n : ℕ) : QR Z [k] n = [qRec Z k n] := rfl

theorem pre_le (g : ℕ → List ℕ) (k N : ℕ) (hk : k < N) :
    ((List.range k).flatMap g).length + (g k).length ≤ ((List.range N).flatMap g).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + d + 1 = (k + 1) + d by omega, List.range_add, List.flatMap_append, List.length_append,
    List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
  omega

/-- **A counted loop that appends tagged records.** Pass `k` appends the records of `g k` (tags continuing). -/
theorem emitLoop {C : Ctx} (i m tg : Fin VV) (him : i ≠ m) (hit : tg ≠ i) (body : St VV MM) (a : DS VV MM)
    (N : ℕ) (hN : N < 2 ^ C.Wd) (g : ℕ → List ℕ) (Z : ℕ) (S Wc : List ℕ) (n1 : ℕ) (R : ℕ → DS VV MM → Prop)
    (t : ℕ) (hR : ∀ k d v, R k d → R k (d.set i v)) (h0 : R 0 a) (hG : GW a S Wc) (hT : a.env tg = n1)
    (hm : a.env m = N)
    (hstep : ∀ k < N, ∀ d, R k d → GW d S (Wc ++ QR Z ((List.range k).flatMap g) n1) →
      d.env tg = n1 + ((List.range k).flatMap g).length → d.env i = k → d.env m = N →
      Hs C body d t (fun e => R (k + 1) e ∧
        GW e S (Wc ++ QR Z ((List.range k).flatMap g) n1 ++ QR Z (g k) (n1 + ((List.range k).flatMap g).length)) ∧
        e.env tg = n1 + ((List.range k).flatMap g).length + (g k).length ∧ e.env i = k ∧ e.env m = N)) :
    Hs C (forS i m body) a (N * (t + 4) + 4) (fun b => R N b ∧
      GW b S (Wc ++ QR Z ((List.range N).flatMap g) n1) ∧ b.env tg = n1 + ((List.range N).flatMap g).length ∧
      b.env i = N ∧ b.env m = N) := by
  have := forS_spec' (C := C) i m him body a N hN
    (fun k d => R k d ∧ GW d S (Wc ++ QR Z ((List.range k).flatMap g) n1) ∧
      d.env tg = n1 + ((List.range k).flatMap g).length) t
    (fun k d v ⟨h1, h2, h3⟩ => ⟨hR k d v h1, h2, by rw [DS.set_env_ne _ _ hit]; exact h3⟩)
    ⟨h0, by simpa [QR] using hG, by simpa using hT⟩ hm ?_
  · exact Hs.mono this le_rfl (fun b ⟨⟨h1, h2, h3⟩, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)
  · intro k hk d ⟨h1, h2, h3⟩ hi hmN
    refine Hs.mono (hstep k hk d h1 h2 h3 hi hmN) le_rfl (fun e ⟨e1, e2, e3, e4, e5⟩ => ⟨⟨e1, ?_, ?_⟩, e4, e5⟩)
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, QR_append, ← List.append_assoc]; exact e2
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]; omega

end NearCubicGates.Close.Cells.QueryPass
