import Proof.Gates.Worker.TermModel

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Codec
open NearCubicGates.Close.WorkerArith (sysList halfIf parityMean_halfIf canonList_ne_nil_iff canonList_inj
  symmDiff_nonempty_iff)

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

theorem canonList_singleton {q : ℕ} (i : Fin q) : (canonList ({i} : Finset (Fin q))).map Fin.val = [i.val] := by
  have hp := canonList_perm ({i} : Finset (Fin q))
  rw [Finset.toList_singleton, List.perm_singleton] at hp
  rw [hp]; rfl

/-- The support rows are the canonical code-support rows at width `q`. -/
def RowsOK (q : ℕ) (rows : ℕ → List ℕ) : Prop :=
  ∀ j (hj : j < P.code.length q), rows j = (canonList (P.code.support q ⟨j, hj⟩)).map Fin.val

namespace Guess
variable {s g} {N : ℕ} (x : BitInput N) (G : Guess (width s g N))

theorem sysList_eq (rows : ℕ → List ℕ) (hrows : RowsOK P (width s g N) rows) (u : ℕ) (hu : u < sysCount s P g x G.oracle) :
    sysList (width s g N) rows u = (canonList (G.sysSupport P x u)).map Fin.val := by
  unfold sysList sysSupport
  by_cases h : u < width s g N
  · rw [if_pos h, dif_pos h, canonList_singleton]
  · have h' : u - width s g N < P.code.length (substituted s g x G.oracle).n := by
      have : u < width s g N + P.code.length (width s g N) := hu
      show u - width s g N < P.code.length (width s g N)
      omega
    rw [if_neg h, dif_neg h, dif_pos h', hrows (u - width s g N) h']
    rfl

variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (w : List Bool) (Cs : ℕ → NCircuit (width s g N))
  (rows : ℕ → List ℕ) (hrows : RowsOK P (width s g N) rows)
include hrows

/-- A systematic operand's parity-mean flag, from its support list. -/
theorem halfIf_sysList (u : ℕ) (hu : u < sysCount s P g x G.oracle) :
    halfIf (decide (sysList (width s g N) rows u ≠ [])) = parityMean (G.sysSupport P x u) := by
  rw [G.sysList_eq P x rows hrows u hu, parityMean_halfIf]
  congr 1
  exact decide_eq_decide.2 (canonList_ne_nil_iff _)

/-- **One operand: the model is the meaning.** -/
theorem termParts_model1 (o : Opd) (hsys : o.sys = true → o.idx < sysCount s P g x G.oracle)
    (hCs : o.sys = false → Cs o.idx = G.circuits o.idx) :
    G.termParts P x ctr ω w [(o.neg, o.atom)] = model1 ctr Cs rows ω w o := by
  unfold model1 Opd.atom
  cases hs : o.sys
  · simp only [Bool.false_eq_true, if_false]
    rw [termParts_aux, G.singleCall_eq ω o.idx ∅ Cs (hCs hs)]
    simp [canonList]
  · simp only [if_true]
    rw [termParts_sys, G.halfIf_sysList P x rows hrows o.idx (hsys hs)]

/-- **Two operands: the model is the meaning.** -/
theorem termParts_model2 (o1 o2 : Opd) (hsys1 : o1.sys = true → o1.idx < sysCount s P g x G.oracle)
    (hsys2 : o2.sys = true → o2.idx < sysCount s P g x G.oracle)
    (hCs1 : o1.sys = false → Cs o1.idx = G.circuits o1.idx) (hCs2 : o2.sys = false → Cs o2.idx = G.circuits o2.idx) :
    G.termParts P x ctr ω w [(o1.neg, o1.atom), (o2.neg, o2.atom)] = model2 ctr Cs rows ω w o1 o2 := by
  unfold model2 Opd.atom
  cases h1 : o1.sys <;> cases h2 : o2.sys
  · simp only [Bool.false_eq_true, if_false]
    rw [termParts_aux_aux]
    congr 1
    by_cases hij : o1.idx = o2.idx
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij, G.pairCall_eq ω _ _ Cs (hCs1 h1) (hCs2 h2)]
  · simp only [Bool.false_eq_true, if_false, if_true]
    rw [termParts_aux_sys, G.singleCall_eq ω _ _ Cs (hCs1 h1), G.sysList_eq P x rows hrows _ (hsys2 h2)]
  · simp only [Bool.false_eq_true, if_false, if_true]
    rw [termParts_sys_aux, G.singleCall_eq ω _ _ Cs (hCs2 h2), G.sysList_eq P x rows hrows _ (hsys1 h1)]
  · simp only [if_true]
    rw [termParts_sys_sys, parityMean_halfIf, G.sysList_eq P x rows hrows _ (hsys1 h1),
      G.sysList_eq P x rows hrows _ (hsys2 h2)]
    congr 3
    exact decide_eq_decide.2 ((symmDiff_nonempty_iff _ _).trans (not_congr (canonList_inj _ _).symm))

end Guess

end NearCubicGates.Close.Worker
