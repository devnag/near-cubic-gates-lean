import Proof.Gates.Worker.Meaning
import Proof.Gates.NoInstanceGadgetSoundness
import Proof.Hierarchy.CompetitorSourceAverage

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages

/-- The bit table of a gadget family in the old project's format. -/
def bitsOf {Gd Pt : Type*} (F : GadgetFamily Gd Pt) : Gd → Pt → Fin 4 → Bool :=
  fun a r => ![F.x a 0 r, F.x a 1 r, F.x a 2 r, F.y a r]

theorem exactPenalty_bitsOf {Gd Pt : Type*} [Fintype Gd] [Fintype Pt] (F : GadgetFamily Gd Pt) :
    GadgetPairMeans.exactPenalty (bitsOf F) = F.meanPenalty := by
  unfold GadgetPairMeans.exactPenalty GadgetFamily.meanPenalty bitsOf
  simp

/-- A function of `a mod m` averages over `Fin (k m)` as over `Fin m`. -/
theorem sum_range_mod (f : ℕ → ℝ) (m k : ℕ) :
    ∑ a ∈ Finset.range (k * m), f (a % m) = k * ∑ c ∈ Finset.range m, f c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * m = k * m + m by ring, Finset.sum_range_add, ih]
    have : ∑ i ∈ Finset.range m, f ((k * m + i) % m) = ∑ c ∈ Finset.range m, f c := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    rw [this]; push_cast; ring

theorem mean_mod (f : ℕ → ℝ) (rb cl : ℕ) (h : rb ≤ cl) :
    mean (fun a : Fin (2 ^ cl) => f (a.val % 2 ^ rb)) = mean (fun c : Fin (2 ^ rb) => f c.val) := by
  unfold mean
  rw [Fin.sum_univ_eq_sum_range (fun a => f (a % 2 ^ rb)), Fin.sum_univ_eq_sum_range f]
  have hsplit : 2 ^ cl = 2 ^ (cl - rb) * 2 ^ rb := by rw [← pow_add]; congr 1; omega
  rw [hsplit, sum_range_mod f (2 ^ rb) (2 ^ (cl - rb))]
  simp only [Fintype.card_fin]
  push_cast
  have h1 : (0 : ℝ) < 2 ^ (cl - rb) := by positivity
  have h2 : (0 : ℝ) < 2 ^ rb := by positivity
  field_simp

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- The proof assignment the guess induces at `r`: proof coordinate `j` is circuit `j` at `r`. -/
noncomputable def proofAt (r : BitInput (width s g N)) : BitInput (pcpp s P g x G.oracle).proofBits :=
  fun j => (G.circuits j.val).eval r

/-- The literal assignment `(sysEnc r, proofAt r)`. -/
noncomputable def assignment (r : BitInput (width s g N)) : BitInput (G.Arity P x) :=
  Fin.addCases (sysEnc P.code (substituted s g x G.oracle).n r) (G.proofAt P x r)

theorem atomValue_atomOf (r : BitInput (width s g N)) (v : Fin (G.Arity P x)) :
    G.atomValue P x r (G.atomOf P x v) = G.assignment P x r v := by
  unfold atomOf assignment
  by_cases hv : v.val < sysCount s P g x G.oracle
  · have hv' : v = Fin.castAdd (pcpp s P g x G.oracle).proofBits ⟨v.val, hv⟩ := by ext; rfl
    conv_rhs => rw [hv']
    rw [Fin.addCases_left]
    simp only [hv, if_true, atomValue, dite_true]
    rfl
  · have hv' : v = Fin.natAdd (sysCount s P g x G.oracle)
        ⟨v.val - sysCount s P g x G.oracle, by have := v.isLt; simp only [Arity] at this; omega⟩ := by
      ext; simp; omega
    conv_rhs => rw [hv']
    rw [Fin.addCases_right]
    simp only [hv, if_false, atomValue, proofAt]

theorem family_x (a : Fin (gadgets s g N)) (i : Fin 3) (r : BitInput (width s g N)) :
    (G.family P x).x a i r = (G.clause P x a.val i).eval (G.assignment P x r) := by
  unfold family
  simp only
  cases hc : G.clause P x a.val i with
  | positive v => simp [literalParts, Literal.eval, atomValue_atomOf, literalNeg, literalVar]
  | negative v => simp [literalParts, Literal.eval, atomValue_atomOf, literalNeg, literalVar]

end Guess

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

theorem originalClause_eq_accepts (a : ℕ) (r : BitInput (width s g N)) :
    Gadget.originalClause ((G.clause P x a 0).eval (G.assignment P x r)) ((G.clause P x a 1).eval (G.assignment P x r))
      ((G.clause P x a 2).eval (G.assignment P x r)) =
      (pcpp s P g x G.oracle).accepts (sysEnc P.code (substituted s g x G.oracle).n r) (G.proofAt P x r)
        ⟨a % 2 ^ (pcpp s P g x G.oracle).randomBits, Nat.mod_lt _ (by positivity)⟩ := by
  unfold Gadget.originalClause RawThreeQueryPCPP.accepts
  simp [List.ofFn_succ, clause, assignment, Bool.or_assoc]

theorem pointwise (h2 : 2 ≤ width s g N)
    (hrb : (pcpp s P g x G.oracle).randomBits ≤ clauseWidth g.clauseDegree (width s g N))
    (r : BitInput (width s g N)) (hD : (substituted s g x G.oracle).D.eval r = false) :
    (P.gamma : ℝ) ≤ NoInstanceGadgetSoundness.falseClauseMean (bitsOf (G.family P x)) r := by
  classical
  have hJ := P.sound (substituted s g x G.oracle) r h2 hD (G.proofAt P x r)
  let acc : Fin (2 ^ (pcpp s P g x G.oracle).randomBits) → Bool := fun c =>
    (pcpp s P g x G.oracle).accepts (sysEnc P.code (substituted s g x G.oracle).n r) (G.proofAt P x r) c
  let h : ℕ → ℝ := fun c => if hc : c < 2 ^ (pcpp s P g x G.oracle).randomBits then
    (if acc ⟨c, hc⟩ then (0 : ℝ) else 1) else 0
  have hmean : NoInstanceGadgetSoundness.falseClauseMean (bitsOf (G.family P x)) r =
      mean (fun c : Fin (2 ^ (pcpp s P g x G.oracle).randomBits) => if acc c then (0 : ℝ) else 1) := by
    unfold NoInstanceGadgetSoundness.falseClauseMean
    have hfun : (fun a : Fin (gadgets s g N) =>
        if Gadget.originalClause (bitsOf (G.family P x) a r 0) (bitsOf (G.family P x) a r 1)
          (bitsOf (G.family P x) a r 2) then (0 : ℝ) else 1) =
        fun a : Fin (gadgets s g N) => h (a.val % 2 ^ (pcpp s P g x G.oracle).randomBits) := by
      funext a
      simp only [bitsOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, family_x, h]
      rw [dif_pos (Nat.mod_lt _ (by positivity)), originalClause_eq_accepts]
    rw [hfun]
    unfold gadgets
    rw [mean_mod h _ _ hrb]
    congr 1
    funext c
    simp only [h, dif_pos c.isLt]
  rw [hmean]
  have hfrac : mean (fun c : Fin (2 ^ (pcpp s P g x G.oracle).randomBits) => if acc c then (0 : ℝ) else 1) =
      1 - (pcpp s P g x G.oracle).fraction (sysEnc P.code (substituted s g x G.oracle).n r) (G.proofAt P x r) := by
    unfold mean RawThreeQueryPCPP.fraction
    have hsplit : ∀ c : Fin (2 ^ (pcpp s P g x G.oracle).randomBits),
        (if acc c then (0 : ℝ) else 1) = 1 - (if acc c then (1 : ℝ) else 0) := by
      intro c; split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Finset.sum_boole]
    have hpos : (0 : ℝ) < 2 ^ (pcpp s P g x G.oracle).randomBits := by positivity
    push_cast
    field_simp
    rfl
  rw [hfrac]
  have : (pcpp s P g x G.oracle).fraction (sysEnc P.code (substituted s g x G.oracle).n r) (G.proofAt P x r) ≤
      1 - (P.gamma : ℝ) := hJ
  linarith

end Guess

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- On a hierarchy no-instance, once CHECK passes, `D_B` accepts at most a `1/L_ν` fraction of the outer randomness
(`sec:gadget-machine`: "by imp:short-pcp, C^{O_{B_pf}}_{⟨B_src⟩_ν} is satisfied by at least a 1 − 1/L_ν fraction of its inputs.
Hence D_B(x) = 1 on at most a 1/L_ν fraction of inputs"; `Outer.sound_at`). -/
theorem outer_mean (hpow : N = 2 ^ nu N) (hν1 : 1 ≤ nu N) (hon : (g.sv s).onset ≤ nu N)
    (hfit : Outer.SrcFits g.lenExp (nu N) G.oracle.src) (hcheck : Outer.CheckAt (nu N) x G.oracle.src)
    (hno : (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts N x = false) :
    mean (fun r : BitInput (width s g N) => (Gadget.bit ((substituted s g x G.oracle).D.eval r) : ℝ)) ≤
      1 / (Outer.instLength g.lenExp (nu N) : ℝ) := by
  classical
  have hno' : ¬ (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.verifier.language
      (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.time N x := by
    intro hyes
    have := (hierarchy_language_exact _ N x).mpr hyes
    rw [hno] at this
    exact Bool.false_ne_true this
  have hcard := Outer.sound_at s.mw (g.sv s) (nu N) N hpow x G.oracle hon hν1 hfit hcheck hno'
  have hb : ∀ b : Bool, ((Gadget.bit b : ℤ) : ℝ) = if b then 1 else 0 := by
    intro b; cases b <;> simp [Gadget.bit]
  have hm : mean (fun r : BitInput (width s g N) => (Gadget.bit ((substituted s g x G.oracle).D.eval r) : ℝ)) =
      ((Finset.univ.filter fun r => (substituted s g x G.oracle).D.eval r = true).card : ℝ) /
        (2 : ℝ) ^ width s g N := by
    unfold mean
    simp only [hb]
    rw [Finset.sum_boole]
    congr 1
    simp [BitInput]
  rw [hm]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ width s g N := by positivity
  rw [div_le_iff₀ hpos]
  have hcard' : ((Finset.univ.filter fun r => (substituted s g x G.oracle).D.eval r = true).card : ℝ) ≤
      (2 : ℝ) ^ width s g N / (Outer.instLength g.lenExp (nu N) : ℝ) := hcard
  calc _ ≤ (2 : ℝ) ^ width s g N / (Outer.instLength g.lenExp (nu N) : ℝ) := hcard'
    _ = 1 / (Outer.instLength g.lenExp (nu N) : ℝ) * (2 : ℝ) ^ width s g N := by ring

end Guess

theorem meaning_oneSided {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} {B1 B2 : ℕ}
    (ctr : Counter B1 B2) (budget : ℕ → ℕ) (ε : ℝ) (ω : ℚ)
    (N : ℕ) (x : BitInput N) (G : Guess (width s g N))
    (hI : Sound (G.family P x) (fun (a : Fin (gadgets s g N)) (t : Fin 10) => G.termInterval P x ctr ω a.val t))
    (h : G.Certified P x ctr budget ε ω) :
    (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts N x = true := by
  classical
  obtain ⟨hguard, hU⟩ := h
  obtain ⟨hrb, h2, hν1, hprec, hpow, hon, hfit, hcheck⟩ := hguard
  by_contra hno
  rw [Bool.not_eq_true] at hno
  haveI : Nonempty (Fin (gadgets s g N)) := ⟨⟨0, by unfold gadgets; positivity⟩⟩
  have hγ0 : (0 : ℝ) ≤ (P.gamma : ℝ) := by exact_mod_cast P.gamma_pos.le
  have hgap := NoInstanceGadgetSoundness.gap_lower_bound (bitsOf (G.family P x))
    (fun r => (substituted s g x G.oracle).D.eval r) (P.gamma : ℝ) (1 / (Outer.instLength g.lenExp (nu N) : ℝ)) hγ0
    (fun r hD => G.pointwise P x h2 hrb r hD) (G.outer_mean x hpow hν1 hon hfit hcheck hno)
  rw [exactPenalty_bitsOf] at hgap
  have hup := upper_ge (G.family P x) (fun (a : Fin (gadgets s g N)) (t : Fin 10) => G.termInterval P x ctr ω a.val t) hI
  have hUdef : Guess.upperEstimate P x G ctr ω = upper (fun (a : Fin (gadgets s g N)) (t : Fin 10) => G.termInterval P x ctr ω a.val t) := rfl
  rw [hUdef] at hU
  have hLpos : (0 : ℝ) < (Outer.instLength g.lenExp (nu N) : ℝ) := by
    exact_mod_cast Outer.instLength_pos (G := g.lenExp) (nu N) hν1
  have hdiv : (P.gamma : ℝ) * (1 / (Outer.instLength g.lenExp (nu N) : ℝ)) =
      (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu N) : ℝ) := by ring
  nlinarith

end NearCubicGates.Close.Worker
