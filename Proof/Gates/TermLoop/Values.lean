import Proof.Gates.TermLoop.Fields

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd model1 model2 Atom)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

def termModel (i : ℕ) (t : Fin 10) : Bool × (ℚ × ℚ) :=
  let o := litOpd s P g x B i
  let h := helpOpd s P g x B i
  let Cs := circs s g N bits pad
  let rows := suppRows P (width s g N)
  let w := termField s P g x bits pad B i t
  match t.val with
  | 0 => model1 ctr Cs rows ω w h
  | 1 => model1 ctr Cs rows ω w (o 0)
  | 2 => model1 ctr Cs rows ω w (o 1)
  | 3 => model1 ctr Cs rows ω w (o 2)
  | 4 => model2 ctr Cs rows ω w (o 0) (o 1)
  | 5 => model2 ctr Cs rows ω w (o 0) (o 2)
  | 6 => model2 ctr Cs rows ω w (o 1) (o 2)
  | 7 => model2 ctr Cs rows ω w (o 0) h
  | 8 => model2 ctr Cs rows ω w (o 1) h
  | _ => model2 ctr Cs rows ω w (o 2) h

section Link
variable (ho : (theGuess s P g x bits pad).oracle = B)
include ho

theorem sysCount_guess : sysCount s P g x (theGuess s P g x bits pad).oracle = sysCount s P g x B := by rw [ho]

theorem clause_var (i : ℕ) (k : Fin 3) :
    litVar ((theGuess s P g x bits pad).clause P x i k) = litVar (clauseOf s P g x B i k) := by
  have : ∀ O : Outer.OuterGuess (width s g N), O = B →
      litVar ((pcpp s P g x O).clause ⟨i % 2 ^ (pcpp s P g x O).randomBits, Nat.mod_lt _ (by positivity)⟩ k) =
        litVar (clauseOf s P g x B i k) := by
    rintro O rfl; rfl
  exact this _ ho

theorem clause_neg (i : ℕ) (k : Fin 3) :
    litNeg ((theGuess s P g x bits pad).clause P x i k) = litNeg (clauseOf s P g x B i k) := by
  have : ∀ O : Outer.OuterGuess (width s g N), O = B →
      litNeg ((pcpp s P g x O).clause ⟨i % 2 ^ (pcpp s P g x O).randomBits, Nat.mod_lt _ (by positivity)⟩ k) =
        litNeg (clauseOf s P g x B i k) := by
    rintro O rfl; rfl
  exact this _ ho

/-- A literal's operand is the loaded descriptor's. -/
theorem lit_parts (i : ℕ) (k : Fin 3) :
    (theGuess s P g x bits pad).literalParts P x ((theGuess s P g x bits pad).clause P x i k) =
      ((litOpd s P g x B i k).neg, (litOpd s P g x B i k).atom) := by
  rw [Worker.Guess.literalParts_eq, clause_var s P g x bits pad B ho, clause_neg s P g x bits pad B ho,
    sysCount_guess s P g x bits pad B ho]
  unfold litOpd Opd.atom
  by_cases h : litVar (clauseOf s P g x B i k) < sysCount s P g x B <;> simp [h]

/-- The helper's operand is the loaded descriptor's. -/
theorem help_parts (i : ℕ) :
    ((false : Bool), (theGuess s P g x bits pad).helper P x i) = ((helpOpd s P g x B i).neg, (helpOpd s P g x B i).atom) := by
  unfold Worker.Guess.helper helpOpd Opd.atom
  rw [ho]; simp

end Link

theorem rowsOK : Worker.RowsOK P (width s g N) (suppRows P (width s g N)) := by
  intro j hj; simp [suppRows, hj]

section Model
variable (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B)
  (hpad : N / 16 + 1 ≤ pad)
include hdec hpad

omit hpad in
theorem litOpd_sys (i : ℕ) (k : Fin 3) :
    (litOpd s P g x B i k).sys = true → (litOpd s P g x B i k).idx < sysCount s P g x (theGuess s P g x bits pad).oracle := by
  rw [sysCount_guess s P g x bits pad B (guess_oracle s P g x bits pad B hdec)]
  unfold litOpd; intro h; simp only [decide_eq_true_eq] at h; simp [h]

theorem litOpd_aux (i : ℕ) (k : Fin 3) : (litOpd s P g x B i k).sys = false →
    circs s g N bits pad (litOpd s P g x B i k).idx = (theGuess s P g x bits pad).circuits (litOpd s P g x B i k).idx := by
  intro h
  unfold litOpd at h ⊢
  simp only [decide_eq_false_iff_not, not_lt] at h
  simp only [show ¬ litVar (clauseOf s P g x B i k) < sysCount s P g x B by omega, if_false]
  refine (circuits_eq s P g x bits pad B hdec hpad _ ?_).symm
  have := ClauseFront.litVar_lt (clauseOf s P g x B i k)
  unfold auxN; omega

theorem helpOpd_aux (i : ℕ) (hi : i < gadgets s g N) : (helpOpd s P g x B i).sys = false →
    circs s g N bits pad (helpOpd s P g x B i).idx = (theGuess s P g x bits pad).circuits (helpOpd s P g x B i).idx := by
  intro _
  refine (circuits_eq s P g x bits pad B hdec hpad _ ?_).symm
  unfold helpOpd auxN; simp only; omega

omit hdec hpad in
theorem helpOpd_sys (i : ℕ) :
    (helpOpd s P g x B i).sys = true → (helpOpd s P g x B i).idx < sysCount s P g x (theGuess s P g x bits pad).oracle := by
  intro h; simp [helpOpd] at h

/-- **The loaded descriptors' model is the meaning's raw term.** -/
theorem termModel_eq (i : ℕ) (hi : i < gadgets s g N) (t : Fin 10) :
    termModel s P g x bits pad B ctr ω i t = (theGuess s P g x bits pad).termRaw P x ctr ω i t := by
  have ho := guess_oracle s P g x bits pad B hdec
  have hw := termField_eq s P g x bits pad B hdec hpad i hi t
  have l := lit_parts s P g x bits pad B ho i
  have hp := help_parts s P g x bits pad B ho i
  have hr := rowsOK s P g (N := N)
  set G := theGuess s P g x bits pad with hG
  unfold Worker.Guess.termRaw
  rw [hw]
  have m1 := fun (o : Opd) (h1 : o.sys = true → o.idx < sysCount s P g x G.oracle)
    (h2 : o.sys = false → circs s g N bits pad o.idx = G.circuits o.idx) =>
    G.termParts_model1 P x ctr ω (termField s P g x bits pad B i t) (circs s g N bits pad)
      (suppRows P (width s g N)) hr o h1 h2
  have m2 := fun (o1 o2 : Opd) (h1 : o1.sys = true → o1.idx < sysCount s P g x G.oracle)
    (h1' : o2.sys = true → o2.idx < sysCount s P g x G.oracle)
    (h2 : o1.sys = false → circs s g N bits pad o1.idx = G.circuits o1.idx)
    (h2' : o2.sys = false → circs s g N bits pad o2.idx = G.circuits o2.idx) =>
    G.termParts_model2 P x ctr ω (termField s P g x bits pad B i t) (circs s g N bits pad)
      (suppRows P (width s g N)) hr o1 o2 h1 h1' h2 h2'
  have ls := litOpd_sys s P g x bits pad B hdec i
  have la := litOpd_aux s P g x bits pad B hdec hpad i
  have hs := helpOpd_sys s P g x bits pad B i
  have ha := helpOpd_aux s P g x bits pad B hdec hpad i hi
  fin_cases t
  · show _ = G.termParts P x ctr ω _ [((false : Bool), G.helper P x i)]
    rw [hp]; exact (m1 _ hs ha).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 0)]
    rw [l]; exact (m1 _ (ls 0) (la 0)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 1)]
    rw [l]; exact (m1 _ (ls 1) (la 1)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 2)]
    rw [l]; exact (m1 _ (ls 2) (la 2)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 0), G.literalParts P x (G.clause P x i 1)]
    rw [l, l]; exact (m2 _ _ (ls 0) (ls 1) (la 0) (la 1)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 0), G.literalParts P x (G.clause P x i 2)]
    rw [l, l]; exact (m2 _ _ (ls 0) (ls 2) (la 0) (la 2)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 1), G.literalParts P x (G.clause P x i 2)]
    rw [l, l]; exact (m2 _ _ (ls 1) (ls 2) (la 1) (la 2)).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 0), ((false : Bool), G.helper P x i)]
    rw [l, hp]; exact (m2 _ _ (ls 0) hs (la 0) ha).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 1), ((false : Bool), G.helper P x i)]
    rw [l, hp]; exact (m2 _ _ (ls 1) hs (la 1) ha).symm
  · show _ = G.termParts P x ctr ω _ [G.literalParts P x (G.clause P x i 2), ((false : Bool), G.helper P x i)]
    rw [l, hp]; exact (m2 _ _ (ls 2) hs (la 2) ha).symm

end Model

end

end NearCubicGates.Close.TermLoop
