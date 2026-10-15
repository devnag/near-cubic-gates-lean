import Proof.Gates.Worker.Calls
import Proof.Gates.Worker.TableSplit

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages
open NearCubicGates.FreshHelperTable NearCubicGates.GadgetTableTransfer NearCubicGates.FiveCycle
open NearCubicGates.CircuitNormalization NearCubicWires.Bindings.CTW26

theorem agreement_comm {α : Type*} [Fintype α] (f g : α → Bool) :
    FiniteAverages.agreement f g = FiniteAverages.agreement g f := by
  unfold FiniteAverages.agreement
  congr 1
  funext y
  by_cases h : f y = g y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

instance finTwoPowNonempty (m : ℕ) : Nonempty (Fin (2 ^ m)) := ⟨⟨0, by positivity⟩⟩

section Chosen
variable (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (cl pl : ℕ)
  (C : Target.WeightedSymmetricCircuit (D.n + cl + pl))

/-- The list entry at address `(a, j)`. -/
noncomputable def addrName (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) : Name P D ⊕ Fin (2 ^ cl) :=
  names (clausesOf P D cl) aj.1 (slot aj.2)

/-- The honest functions of all names. -/
noncomputable def honestOf : Name P D ⊕ Fin (2 ^ cl) → BitInput D.n → Bool :=
  honestAssignment (clausesOf P D cl) (originalOf P D hD)

/-- The address cofactors. -/
noncomputable def candOf (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) : BitInput D.n → Bool := (addressCofactor C aj).eval

/-- The systematic names: the checked circuit's input. -/
noncomputable def systematicOf (X : Name P D) : Bool := decide (X.val < (checkedCircuit P.code D).n)

/-- The chosen coordinate functions (v2 lines 2462–2466): systematic names exact, every other name one minimizing
address cofactor. -/
noncomputable def chosenOf : Name P D ⊕ Fin (2 ^ cl) → BitInput D.n → Bool :=
  NameCofactors.prescribedSelected (prescribed (systematicOf P D)) (addrName P D cl pl) (honestOf P D hD cl)
    (candOf D cl pl C)

/-- The address chosen for a name. -/
noncomputable def chosenAddrOf (nm : Name P D ⊕ Fin (2 ^ cl)) : Fin (2 ^ cl) × Fin (2 ^ pl) :=
  NameCofactors.chosenAddress (addrName P D cl pl)
    (NameCofactors.addressError (addrName P D cl pl) (honestOf P D hD cl) (candOf D cl pl C)) nm

theorem chosenOf_aux (nm : Name P D ⊕ Fin (2 ^ cl)) (h : prescribed (G := Fin (2 ^ cl)) (systematicOf P D) nm = false)
    (r : BitInput D.n) : chosenOf P D hD cl pl C nm r = (addressCofactor C (chosenAddrOf P D hD cl pl C nm)).eval r := by
  unfold chosenOf
  rw [NameCofactors.prescribedSelected_auxiliary _ _ _ _ _ h]
  rfl

theorem chosenOf_sys (X : Name P D) (h : X.val < (checkedCircuit P.code D).n) :
    chosenOf P D hD cl pl C (Sum.inl X) = originalOf P D hD X := by
  unfold chosenOf
  rw [NameCofactors.prescribedSelected_exact _ _ _ _ _ (by simp [prescribed, systematicOf, h])]
  rfl

/-- **eq:gadget-table-error** for the chosen functions. -/
theorem chosen_penalty_bound (hP : 5 ≤ 2 ^ pl) :
    mean (fun a : Fin (2 ^ cl) => mean (penalty (names (clausesOf P D cl)) (fun a => (clausesOf P D cl a).negative)
      (chosenOf P D hD cl pl C) a)) ≤
      (((2 ^ pl : ℕ) : ℝ) / ((2 ^ pl) / 5 : ℕ)) * error (hardTable P D hD cl pl) C.eval := by
  have h := constructed_table_prescribed_bound (G := Fin (2 ^ cl)) (Input := BitInput D.n) (2 ^ pl) hP
    (clausesOf P D cl) (originalOf P D hD) (systematicOf P D) (fun a x => clausesOf_true P D hD cl a x)
    (candOf D cl pl C)
  have hsplit : mean (fun aj : Fin (2 ^ cl) × Fin (2 ^ pl) =>
      error (table (names (clausesOf P D cl)) (honestAssignment (clausesOf P D cl) (originalOf P D hD)) aj)
        (candOf D cl pl C aj)) = error (hardTable P D hD cl pl) C.eval := by
    rw [error_split]
    congr 1
    funext aj
    congr 1
    funext y
    rw [hardTable_at]
    rfl
  rw [← hsplit]
  exact h

end Chosen

/-! ## Part 2: admitted calls -/

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- Every call of a term is admitted, within the weight caps `b` (single, parity) and `2b` (pair). -/
theorem callOf_admitted {B1 B2 : ℕ} (ω : ℚ) (b : ℕ) (ops : List (Bool × Atom)) (c : Call)
    (hc : G.callOf P x ω ops = some c)
    (hwf : ∀ o ∈ ops, ∀ j, o.2 = .aux j →
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ (G.circuits j).topWeight ≤ b)
    (hq4 : 4 ≤ width s g N) (hb : b ≤ width s g N ^ 4) (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1)
    (hr2 : ω ≤ 1 / 16) (hr3 : (ratWord ω).length ≤ width s g N ^ B2) :
    c.Admitted B1 B2 ∧ (c.kind = .pair → c.W ≤ 2 * b) ∧ (c.kind ≠ .pair → c.W ≤ b) := by
  classical
  have hwf' : ∀ e ∈ ops.map Prod.snd, ∀ j, e = .aux j →
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ (G.circuits j).topWeight ≤ b := by
    intro e he j hj
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
    exact hwf o ho j hj
  unfold callOf at hc
  generalize ops.map Prod.snd = as at hc hwf'
  have hE := empty_wellFormed (width s g N) (Call.B0 (width s g N))
  -- the single / parity call on circuit `j` with support `S`
  have hsingle : ∀ (j : ℕ) (S : Finset (Fin (width s g N))),
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ (G.circuits j).topWeight ≤ b →
      (G.singleCall ω j S).Admitted B1 B2 ∧ ((G.singleCall ω j S).kind = .pair → (G.singleCall ω j S).W ≤ 2 * b) ∧
        ((G.singleCall ω j S).kind ≠ .pair → (G.singleCall ω j S).W ≤ b) := by
    intro j S ⟨hw, ht⟩
    by_cases hS : S.Nonempty
    · rw [G.singleCall_pos ω j S hS]
      refine ⟨⟨hq4, hw, hE, fun _ => rfl, fun h => absurd rfl h, ?_, ?_, hr1, hr2, hr3,
        by simp only [List.length_map, canonList]; exact (List.length_filter_le _ _).trans (by simp)⟩,
        fun h => absurd h (fun h2 => by cases h2), ?_⟩
      · intro i hi
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
        exact k.isLt
      · show (G.circuits j).topWeight + (NCircuit.empty _).topWeight ≤ 2 * width s g N ^ 4
        rw [empty_topWeight]; omega
      · intro _
        show (G.circuits j).topWeight + (NCircuit.empty _).topWeight ≤ b
        rw [empty_topWeight]; omega
    · rw [G.singleCall_neg ω j S hS]
      refine ⟨⟨hq4, hw, hE, fun _ => rfl, fun _ => rfl, by simp, ?_, hr1, hr2, hr3, by simp⟩,
        fun h => absurd h (fun h2 => by cases h2), ?_⟩
      · show (G.circuits j).topWeight + (NCircuit.empty _).topWeight ≤ 2 * width s g N ^ 4
        rw [empty_topWeight]; omega
      · intro _
        show (G.circuits j).topWeight + (NCircuit.empty _).topWeight ≤ b
        rw [empty_topWeight]; omega
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · simp at hc
  · cases a₁ with
    | sys u => simp at hc
    | aux j =>
      simp only [Option.some.injEq] at hc
      subst hc
      exact hsingle j ∅ (hwf' _ (by simp) j rfl)
  · cases a₁ with
    | sys u =>
      cases a₂ with
      | sys v => simp at hc
      | aux j =>
        simp only [Option.some.injEq] at hc
        subst hc
        exact hsingle j _ (hwf' _ (by simp) j rfl)
    | aux i =>
      cases a₂ with
      | sys u =>
        simp only [Option.some.injEq] at hc
        subst hc
        exact hsingle i _ (hwf' _ (by simp) i rfl)
      | aux j =>
        dsimp only at hc
        by_cases hij : i = j
        · rw [if_pos hij] at hc; simp at hc
        · rw [if_neg hij] at hc
          simp only [Option.some.injEq] at hc
          subst hc
          obtain ⟨hwi, hti⟩ := hwf' _ (by simp) i rfl
          obtain ⟨hwj, htj⟩ := hwf' _ (by simp) j rfl
          refine ⟨⟨hq4, hwi, hwj, fun h => absurd rfl h, fun _ => rfl, by simp [pairCall], ?_, hr1, hr2, hr3,
            by simp [pairCall]⟩, ?_, fun h => absurd rfl h⟩
          · show (G.circuits i).topWeight + (G.circuits j).topWeight ≤ 2 * width s g N ^ 4
            omega
          · intro _
            show (G.circuits i).topWeight + (G.circuits j).topWeight ≤ 2 * b
            omega
  · cases a₁ <;> cases a₂ <;> simp at hc

end Guess

theorem addCases_lt {m k : ℕ} {α : Type*} (f : Fin m → α) (h₂ : Fin k → α) (X : Fin (m + k)) (h : X.val < m) :
    Fin.addCases (motive := fun _ => α) f h₂ X = f ⟨X.val, h⟩ := by
  obtain ⟨v, hv⟩ := X
  show Fin.addCases (motive := fun _ => α) f h₂ (Fin.castAdd k ⟨v, h⟩) = _
  rw [Fin.addCases_left]

theorem addCases_ge {m k : ℕ} {α : Type*} (f : Fin m → α) (h₂ : Fin k → α) (X : Fin (m + k)) (h : m ≤ X.val) :
    Fin.addCases (motive := fun _ => α) f h₂ X = h₂ ⟨X.val - m, by omega⟩ := by
  obtain ⟨v, hv⟩ := X
  simp only at h ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  show Fin.addCases (motive := fun _ => α) f h₂ (Fin.natAdd m ⟨d, by omega⟩) = _
  rw [Fin.addCases_right]
  congr 1
  ext
  simp

theorem originalOf_lt (P : ThreeQueryPCPP) (D : Circuit) (hD : ∀ x, D.D.eval x = true) (X : Name P D)
    (h : X.val < (checkedCircuit P.code D).n) (r : BitInput D.n) :
    originalOf P D hD X r = sysEnc P.code D.n r ⟨X.val, h⟩ := by
  unfold originalOf
  exact addCases_lt _ _ X h

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

theorem assignment_lt (r : BitInput (width s g N)) (X : Fin (G.Arity P x)) (h : X.val < sysCount s P g x G.oracle) :
    G.assignment P x r X = sysEnc P.code (substituted s g x G.oracle).n r ⟨X.val, h⟩ := by
  unfold assignment
  exact addCases_lt _ _ X h

theorem assignment_ge (r : BitInput (width s g N)) (X : Fin (G.Arity P x)) (h : sysCount s P g x G.oracle ≤ X.val) :
    G.assignment P x r X = (G.circuits (X.val - sysCount s P g x G.oracle)).eval r := by
  unfold assignment
  rw [addCases_ge _ _ X h]
  rfl

end Guess

/-! ## Part 3: the guess of an approximator -/

section Construct
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {N : ℕ} (x : BitInput N)
  (B : Outer.OuterGuess (width s g N)) (hD : ∀ r, (substituted s g x B).D.eval r = true)
  (C : Target.WeightedSymmetricCircuit
    ((substituted s g x B).n + clauseWidth g.clauseDegree (width s g N) + g.positionLog))
  (pub : CTW26_Lemma3_2) (hn : 1 ≤ width s g N)

noncomputable def cofCircuit
    (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) :
    NCircuit (width s g N) :=
  toNCircuit (addressCofactor C (chosenAddrOf P (substituted s g x B) hD _ _ C nm))
    (Classical.choice (integer_description_exists pub hn _))

/-- One circuit per auxiliary name: proof coordinate `j`, then helper `proofBits + a`. -/
noncomputable def proofCircuits (j : ℕ) : NCircuit (width s g N) :=
  if h : j < (pcpp s P g x B).proofBits then
    cofCircuit s P g x B hD C pub hn (Sum.inl (Fin.natAdd (sysCount s P g x B) ⟨j, h⟩))
  else if h' : j - (pcpp s P g x B).proofBits < 2 ^ clauseWidth g.clauseDegree (width s g N) then
    cofCircuit s P g x B hD C pub hn (Sum.inr ⟨j - (pcpp s P g x B).proofBits, h'⟩)
  else NCircuit.empty _

/-- The guess with the pair `B`, the chosen circuits, and witness prefixes `W`. -/
noncomputable abbrev baseGuess (W : ℕ → Fin 10 → List Bool) : Guess (width s g N) :=
  ⟨B, proofCircuits s P g x B hD C pub hn, W⟩

theorem cofCircuit_eval (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N)))
    (r : BitInput (width s g N)) :
    (cofCircuit s P g x B hD C pub hn nm).eval r =
      (addressCofactor C (chosenAddrOf P (substituted s g x B) hD _ _ C nm)).eval r :=
  toNCircuit_eval _ _ r

theorem cofCircuit_good (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) :
    (cofCircuit s P g x B hD C pub hn nm).WellFormed (Call.B0 (width s g N)) ∧
      (cofCircuit s P g x B hD C pub hn nm).topWeight = C.topWeight :=
  ⟨toNCircuit_wellFormed _ _, toNCircuit_topWeight _ _⟩

theorem proofCircuits_good (W : ℕ → Fin 10 → List Bool) (j : ℕ)
    (hj : j < (baseGuess s P g x B hD C pub hn W).auxCount P x) :
    (proofCircuits s P g x B hD C pub hn j).WellFormed (Call.B0 (width s g N)) ∧
      (proofCircuits s P g x B hD C pub hn j).topWeight = C.topWeight := by
  unfold proofCircuits
  split_ifs with h h'
  · exact cofCircuit_good s P g x B hD C pub hn _
  · exact cofCircuit_good s P g x B hD C pub hn _
  · exfalso
    unfold Guess.auxCount gadgets baseGuess at hj
    exact h' (by simp only at hj; omega)

theorem assignment_eq (W : ℕ → Fin 10 → List Bool) (r : BitInput (width s g N))
    (X : Name P (substituted s g x B)) :
    (baseGuess s P g x B hD C pub hn W).assignment P x r X =
      chosenOf P (substituted s g x B) hD _ _ C (Sum.inl X) r := by
  have hsc : sysCount s P g x B = (checkedCircuit P.code (substituted s g x B)).n := rfl
  by_cases hX : X.val < (checkedCircuit P.code (substituted s g x B)).n
  · calc (baseGuess s P g x B hD C pub hn W).assignment P x r X
          = sysEnc P.code (substituted s g x B).n r ⟨X.val, hX⟩ :=
            Guess.assignment_lt P x (baseGuess s P g x B hD C pub hn W) r X hX
      _ = originalOf P (substituted s g x B) hD X r := (originalOf_lt P _ hD X hX r).symm
      _ = chosenOf P (substituted s g x B) hD _ _ C (Sum.inl X) r := by
            rw [chosenOf_sys _ _ _ _ _ _ _ hX]
  · have hge : sysCount s P g x B ≤ X.val := by rw [hsc]; exact Nat.le_of_not_lt hX
    have hlt : X.val - sysCount s P g x B < (pcpp s P g x B).proofBits := by
      have := X.isLt
      have hpb : (pcpp s P g x B).proofBits = (P.output (checkedCircuit P.code (substituted s g x B))).proofBits := rfl
      omega
    have hX' : (Fin.natAdd (sysCount s P g x B) ⟨X.val - sysCount s P g x B, hlt⟩ :
        Fin (sysCount s P g x B + (pcpp s P g x B).proofBits)) = X := by
      ext; simp only [Fin.val_natAdd]; omega
    calc (baseGuess s P g x B hD C pub hn W).assignment P x r X
          = (proofCircuits s P g x B hD C pub hn (X.val - sysCount s P g x B)).eval r :=
            Guess.assignment_ge P x (baseGuess s P g x B hD C pub hn W) r X hge
      _ = (cofCircuit s P g x B hD C pub hn (Sum.inl X)).eval r := by
            unfold proofCircuits
            rw [dif_pos hlt]
            exact congrArg (fun nm => (cofCircuit s P g x B hD C pub hn (Sum.inl nm)).eval r) hX'
      _ = (addressCofactor C (chosenAddrOf P (substituted s g x B) hD _ _ C (Sum.inl X))).eval r :=
            cofCircuit_eval s P g x B hD C pub hn _ r
      _ = chosenOf P (substituted s g x B) hD _ _ C (Sum.inl X) r :=
            (chosenOf_aux P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog C
              (Sum.inl X) (by simp only [prescribed, Sum.elim_inl, systematicOf, decide_eq_false_iff_not]; exact hX)
              r).symm

theorem helper_eq (W : ℕ → Fin 10 → List Bool) (a : Fin (2 ^ clauseWidth g.clauseDegree (width s g N)))
    (r : BitInput (width s g N)) :
    (baseGuess s P g x B hD C pub hn W).atomValue P x r ((baseGuess s P g x B hD C pub hn W).helper P x a.val) =
      chosenOf P (substituted s g x B) hD _ _ C (Sum.inr a) r := by
  have h1 : ¬ (pcpp s P g x B).proofBits + a.val < (pcpp s P g x B).proofBits := by omega
  have h2 : (pcpp s P g x B).proofBits + a.val - (pcpp s P g x B).proofBits <
      2 ^ clauseWidth g.clauseDegree (width s g N) := by
    have := a.isLt; omega
  have ha : (⟨(pcpp s P g x B).proofBits + a.val - (pcpp s P g x B).proofBits, h2⟩ :
      Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) = a := by ext; simp
  calc (baseGuess s P g x B hD C pub hn W).atomValue P x r ((baseGuess s P g x B hD C pub hn W).helper P x a.val)
        = (proofCircuits s P g x B hD C pub hn ((pcpp s P g x B).proofBits + a.val)).eval r := rfl
    _ = (cofCircuit s P g x B hD C pub hn (Sum.inr a)).eval r := by
          unfold proofCircuits; rw [dif_neg h1, dif_pos h2, ha]
    _ = (addressCofactor C (chosenAddrOf P (substituted s g x B) hD _ _ C (Sum.inr a))).eval r :=
          cofCircuit_eval s P g x B hD C pub hn _ r
    _ = chosenOf P (substituted s g x B) hD _ _ C (Sum.inr a) r :=
          (chosenOf_aux P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog C
            (Sum.inr a) rfl r).symm

theorem meanPenalty_eq (W : ℕ → Fin 10 → List Bool) :
    ((baseGuess s P g x B hD C pub hn W).family P x).meanPenalty =
      mean (fun a : Fin (2 ^ clauseWidth g.clauseDegree (width s g N)) =>
        mean (penalty (names (clausesOf P (substituted s g x B) _)) (fun a => (clausesOf P (substituted s g x B) _ a).negative)
          (chosenOf P (substituted s g x B) hD _ g.positionLog C) a)) := by
  unfold GadgetFamily.meanPenalty
  congr 1
  funext a
  congr 1
  funext r
  have hx : ∀ i : Fin 3, ((baseGuess s P g x B hD C pub hn W).family P x).x a i r =
      literal ((clausesOf P (substituted s g x B) _ a).negative i)
        (chosenOf P (substituted s g x B) hD _ g.positionLog C (Sum.inl ((clausesOf P (substituted s g x B) _ a).name i)) r) := by
    intro i
    rw [Guess.family_x, literal_eval_eq, assignment_eq]
    rfl
  have hy : ((baseGuess s P g x B hD C pub hn W).family P x).y a r =
      chosenOf P (substituted s g x B) hD _ g.positionLog C (Sum.inr a) r := helper_eq s P g x B hD C pub hn W a r
  rw [hx 0, hx 1, hx 2, hy]
  rfl

end Construct

/-! ## Part 4: useful witnesses and `U < γ − ε` -/

section Final
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {N : ℕ} (x : BitInput N)
  (B : Outer.OuterGuess (width s g N)) (hD : ∀ r, (substituted s g x B).D.eval r = true)
  (C : Target.WeightedSymmetricCircuit
    ((substituted s g x B).n + clauseWidth g.clauseDegree (width s g N) + g.positionLog))
  (pub : CTW26_Lemma3_2) (hn : 1 ≤ width s g N) {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- Useful witness prefixes: per term, a witness of radius at most `ω` for its call, when one exists. -/
noncomputable def usefulWit (a : ℕ) (t : Fin 10) : List Bool := by
  classical
  exact if h : ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω
    then Classical.choose h else []

/-- The guess of the approximator: chosen cofactors and useful witnesses. -/
noncomputable abbrev approxGuess : Guess (width s g N) :=
  baseGuess s P g x B hD C pub hn (usefulWit s P g x B hD C pub hn ctr ω)

/-- Calls and operands do not read the witness prefixes. -/
theorem callOf_base (W W' : ℕ → Fin 10 → List Bool) (a : ℕ) (t : Fin 10) :
    (baseGuess s P g x B hD C pub hn W).callOf P x ω ((baseGuess s P g x B hD C pub hn W).operands P x a t) =
      (baseGuess s P g x B hD C pub hn W').callOf P x ω ((baseGuess s P g x B hD C pub hn W').operands P x a t) := by
  rfl

theorem usefulWit_length (a : ℕ) (t : Fin 10) :
    (usefulWit s P g x B hD C pub hn ctr ω a t).length ≤ ctr.witnessLength (width s g N) := by
  unfold usefulWit
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem usefulWit_spec (a : ℕ) (t : Fin 10)
    (hex : ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω) :
    ∀ c, (baseGuess s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c (usefulWit s P g x B hD C pub hn ctr ω a t)).2 ≤ ω := by
  unfold usefulWit
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- thm:pair-uniform completeness supplies a useful witness for every term of every gadget. -/
theorem useful_exists (aC : ℝ) (onsetC : ℕ)
    (hcomplete : ∀ c : Call, onsetC ≤ c.n → c.Admitted B1 B2 →
      (c.kind = .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A3 c.n) →
      (c.kind ≠ .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A1 c.n) →
      ∃ w : List Bool, w.length ≤ ctr.witnessLength c.n ∧ (ctr.value c w).2 ≤ c.radius)
    (b : ℕ) (hC : C.topWeight ≤ b) (hq4 : 4 ≤ width s g N) (hon : onsetC ≤ width s g N)
    (hb4 : b ≤ width s g N ^ 4) (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1) (hr2 : ω ≤ 1 / 16)
    (hr3 : (ratWord ω).length ≤ width s g N ^ B2)
    (hA3 : (2 * b : ℝ) ≤ aC * (ω : ℝ) * A3 (width s g N)) (hA1 : (b : ℝ) ≤ aC * (ω : ℝ) * A1 (width s g N))
    (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) :
    ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω := by
  cases hco : (baseGuess s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
      ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) with
  | none => exact ⟨[], by simp, fun c hc => by simp at hc⟩
  | some c =>
    obtain ⟨hcn, hcr⟩ := Guess.callOf_n_radius P x (baseGuess s P g x B hD C pub hn (fun _ _ => [])) ω _ c hco
    have hwf : ∀ o ∈ (baseGuess s P g x B hD C pub hn (fun _ _ => [])).operands P x a t, ∀ j, o.2 = .aux j →
        ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).circuits j).WellFormed (Call.B0 (width s g N)) ∧
          ((baseGuess s P g x B hD C pub hn (fun _ _ => [])).circuits j).topWeight ≤ b := by
      intro o ho j hj
      have hjlt := Guess.operands_aux_lt P x (baseGuess s P g x B hD C pub hn (fun _ _ => [])) a ha t o ho j hj
      obtain ⟨hw, ht⟩ := proofCircuits_good s P g x B hD C pub hn (fun _ _ => []) j hjlt
      exact ⟨hw, by show (proofCircuits s P g x B hD C pub hn j).topWeight ≤ b; rw [ht]; exact hC⟩
    obtain ⟨hadm, hpair, hnon⟩ := Guess.callOf_admitted P x (baseGuess s P g x B hD C pub hn (fun _ _ => []))
      ω b _ c hco hwf hq4 hb4 hr1 hr2 hr3
    have hp : c.kind = .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A3 c.n := by
      intro hk
      rw [hcr, hcn]
      have := hpair hk
      calc (c.W : ℝ) ≤ ((2 * b : ℕ) : ℝ) := by exact_mod_cast this
        _ = 2 * (b : ℝ) := by push_cast; ring
        _ ≤ _ := hA3
    have hs : c.kind ≠ .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A1 c.n := by
      intro hk
      rw [hcr, hcn]
      have := hnon hk
      calc (c.W : ℝ) ≤ (b : ℝ) := by exact_mod_cast this
        _ ≤ _ := hA1
    obtain ⟨w, hwl, hwr⟩ := hcomplete c (by rw [hcn]; exact hon) hadm hp hs
    refine ⟨w, by rw [← hcn]; exact hwl, fun c' hc' => ?_⟩
    cases hc'
    rw [← hcr]
    exact hwr

theorem approx_complete (aC : ℝ) (onsetC : ℕ)
    (hcomplete : ∀ c : Call, onsetC ≤ c.n → c.Admitted B1 B2 →
      (c.kind = .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A3 c.n) →
      (c.kind ≠ .pair → (c.W : ℝ) ≤ aC * (c.radius : ℝ) * A1 c.n) →
      ∃ w : List Bool, w.length ≤ ctr.witnessLength c.n ∧ (ctr.value c w).2 ≤ c.radius)
    (budget : ℕ → ℕ) (ε εT : ℝ) (hC : C.topWeight ≤ budget (width s g N))
    (hagree : 1 - (P.gamma : ℝ) / 5 + ε ≤ FiniteAverages.agreement C.eval
      (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog))
    (hε : 0 < ε) (hε1 : ε < 1) (hεγ : ε < (P.gamma : ℝ) / 5) (hεT : εT ≤ 2 * ε) (hω0 : 0 ≤ ω)
    (hωε : (ω : ℝ) ≤ ε / 128)
    (hP5 : 5 ≤ 2 ^ g.positionLog) (hP : 128 ≤ ε * ((2 ^ g.positionLog : ℕ) : ℝ))
    (hq4 : 4 ≤ width s g N) (hon : onsetC ≤ width s g N) (hb4 : budget (width s g N) ≤ width s g N ^ 4)
    (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1) (hr2 : ω ≤ 1 / 16) (hr3 : (ratWord ω).length ≤ width s g N ^ B2)
    (hA3 : (2 * budget (width s g N) : ℝ) ≤ aC * (ω : ℝ) * A3 (width s g N))
    (hA1 : (budget (width s g N) : ℝ) ≤ aC * (ω : ℝ) * A1 (width s g N))
    (hsrc : B.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N))
    (hpf : B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N))
    (hrb : (pcpp s P g x B).randomBits ≤ clauseWidth g.clauseDegree (width s g N))
    (hν1 : 1 ≤ nu N) (hprec : (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu N) : ℝ) < εT)
    (hS : (approxGuess s P g x B hD C pub hn ctr ω).SetupOK x) :
    (approxGuess s P g x B hD C pub hn ctr ω).Guards P x ctr budget εT ∧
      (approxGuess s P g x B hD C pub hn ctr ω).SizeOK P x ctr budget ∧
      (approxGuess s P g x B hD C pub hn ctr ω).upperEstimate P x ctr ω < (P.gamma : ℝ) - εT := by
  have hex := fun (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) =>
    useful_exists s P g x B hD C pub hn ctr ω aC onsetC hcomplete (budget (width s g N)) hC hq4 hon hb4 hr1 hr2 hr3
      hA3 hA1 a ha t
  refine ⟨⟨hrb, by omega, hν1, hprec, hS⟩,
    ⟨hsrc, hpf, fun j hj => ?_, fun a _ t => usefulWit_length s P g x B hD C pub hn ctr ω a t⟩, ?_⟩
  · obtain ⟨hw, ht⟩ := proofCircuits_good s P g x B hD C pub hn _ j hj
    exact ⟨hw, by show (proofCircuits s P g x B hD C pub hn j).topWeight ≤ _; rw [ht]; exact hC⟩
  haveI : Nonempty (Fin (gadgets s g N)) := finTwoPowNonempty _
  have hsound := Guess.termInterval_sound P x (approxGuess s P g x B hD C pub hn ctr ω) ctr ω
  have hrad : ∀ (a : Fin (gadgets s g N)) (t : Fin 10),
      (((approxGuess s P g x B hD C pub hn ctr ω).termInterval P x ctr ω a.val t).2 : ℝ) ≤ (ω : ℝ) := by
    intro a t
    have h := Guess.intervalOf_radius P x (approxGuess s P g x B hD C pub hn ctr ω) ctr ω hω0
      (usefulWit s P g x B hD C pub hn ctr ω a.val t)
      ((approxGuess s P g x B hD C pub hn ctr ω).operands P x a.val t)
      (Guess.operands_length P x _ a.val t)
      (fun c hc => usefulWit_spec s P g x B hD C pub hn ctr ω a.val t (hex a.val a.isLt t) c
        (by rw [callOf_base s P g x B hD C pub hn ω (fun _ _ => []) (usefulWit s P g x B hD C pub hn ctr ω)]; exact hc))
    exact_mod_cast h
  have hup := upper_le ((approxGuess s P g x B hD C pub hn ctr ω).family P x)
    (fun (a : Fin (gadgets s g N)) (t : Fin 10) => (approxGuess s P g x B hD C pub hn ctr ω).termInterval P x ctr ω a.val t)
    hsound (ω : ℝ) hrad
  rw [meanPenalty_eq] at hup
  have hpen := chosen_penalty_bound P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N))
    g.positionLog C hP5
  have hcyc := cycle_factor (2 ^ g.positionLog) ε hP5 hε hε1 hP
  have herr : error (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog)
      C.eval ≤ (P.gamma : ℝ) / 5 - ε := by
    have h1 := error_add_agreement (hardTable P (substituted s g x B) hD
      (clauseWidth g.clauseDegree (width s g N)) g.positionLog) C.eval
    rw [agreement_comm] at hagree
    linarith
  have herr0 := error_nonneg (hardTable P (substituted s g x B) hD
      (clauseWidth g.clauseDegree (width s g N)) g.positionLog) C.eval
  have hγ1 : (P.gamma : ℝ) < 1 := by exact_mod_cast P.gamma_lt_one
  set δ := error (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog) C.eval
  set κ := (((2 ^ g.positionLog : ℕ) : ℝ) / ((2 ^ g.positionLog) / 5 : ℕ))
  have hU : (approxGuess s P g x B hD C pub hn ctr ω).upperEstimate P x ctr ω ≤ κ * δ + 10 * (ω : ℝ) := by
    show upper _ ≤ _
    linarith
  have h1 : κ * δ ≤ (5 + ε) * δ := mul_le_mul_of_nonneg_right hcyc herr0
  have h2 : (5 + ε) * δ ≤ (5 + ε) * ((P.gamma : ℝ) / 5 - ε) := mul_le_mul_of_nonneg_left herr (by linarith)
  nlinarith

end Final

end NearCubicGates.Close.Worker
