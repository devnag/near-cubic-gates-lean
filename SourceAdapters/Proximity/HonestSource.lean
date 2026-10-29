import SourceAdapters.Proximity.TrimHonestRegisters
import SourceAdapters.Proximity.HonestLoading
import SourceAdapters.Code.BitSending

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the actual original honest-proof source call.
Its source description and input bits are physically sent, and every returned
proof bit is loaded with its exact finite length, including trailing zeros. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestSource

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Code
open SourceRequests (State Script lengthReg)
open TrimHonest (inputStore inputLength proofStore)

def request {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : ProofCall V := .inr (.inl p)

def tag : List Bool := [true, false]

def script : Script := .seq (SourceRequests.beginRequest tag)
  (.seq (BitSending.script inputStore inputLength) (HonestLoading.callLoad proofStore TrimHonest.proofLength))

def scratch : List (Fin VV) := [t0, t1, t3, c0, vJ, TrimHonest.proofLength]

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem run (p : AcceptedSourceInput) (Wd Lk Bk : ℕ) (pre tail : List Bool)
    (a : State) (hc : Cst a)
    (hlen : a.env lengthReg = (sourceCircuitWord p.1).length)
    (hip : a.ip = pre.length) (hempty : a.kin = [])
    (hinput : a.ram inputStore = (List.ofFn p.2.val).map Bool.toNat)
    (hinputLength : a.env inputLength = p.1.arity)
    (hproof : a.ram proofStore = []) (hproofCursor : a.rc proofStore = 0)
    (hinputWidth : p.1.arity < 2 ^ Wd) (hproofWidth : proofSize p.1 < 2 ^ Wd)
    (hroom : 2 + (sourceCircuitWord p.1).length + p.1.arity ≤ Lk)
    (hbudget : budget (request V p) ≤ Bk) :
    let C := SourceCallee.context V proofSize honest budget P Wd
      (pre ++ sourceCircuitWord p.1 ++ tail) Lk Bk
    Hs C script a
      (15 * (sourceCircuitWord p.1).length + a.rc inputStore + 8 * p.1.arity +
        Lk + Bk + 9 * proofSize p.1 + 33)
      (fun b =>
        b.ram proofStore = (List.ofFn (honest p)).map Bool.toNat ∧
        b.env TrimHonest.proofLength = proofSize p.1 ∧ b.rc proofStore = proofSize p.1 ∧
        b.rc inputStore = p.1.arity ∧ b.ip = pre.length ∧ b.out = a.out ∧
        b.kin = [] ∧ b.kout = frame (List.ofFn (honest p)) ∧
        b.kc = (frame (List.ofFn (honest p))).length ∧ Cst b ∧
        (∀ m, m ≠ proofStore → b.ram m = a.ram m) ∧
        (∀ m, m ≠ proofStore → m ≠ inputStore → b.rc m = a.rc m) ∧ Fr a b scratch) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord p.1 ++ tail) Lk Bk
  obtain ⟨b, nb, eb, hb, rb⟩ := SourceRequests.begin_request C tag (sourceCircuitWord p.1)
    pre tail a hc hlen rfl hip (by
      change a.kin.length + tag.length + (sourceCircuitWord p.1).length ≤ Lk
      simp only [hempty, List.length_nil, Nat.zero_add, tag, List.length_cons]
      omega)
  have rbrest := rb.rest_eq
  simp only [SourceRequests.rest, Prod.mk.injEq] at rbrest
  have cb := rb.constants hc
  have binput : b.ram inputStore = (List.ofFn p.2.val).map Bool.toNat := by rw [rbrest.2.2.1, hinput]
  have bsize : b.env inputLength = (List.ofFn p.2.val).length := by
    rw [rb.vars inputLength (by decide), hinputLength, List.length_ofFn]
  obtain ⟨d, nd, ed, hd, dkin, _, cd, dip, dout, dram, dcinput, dcother, _, _, dfr⟩ :=
    BitSending.runs C inputStore inputLength (by decide) (by decide) b cb (List.ofFn p.2.val)
      binput bsize (by change (List.ofFn p.2.val).length < 2 ^ Wd; simpa only [List.length_ofFn] using hinputWidth)
      (by change b.kin.length + (List.ofFn p.2.val).length ≤ Lk
          rw [rb.kin_eq, hempty]
          simp only [tag, List.nil_append, List.length_append, List.length_cons, List.length_nil, List.length_ofFn]
          omega)
  have drequest : d.kin = C.K.inw (request V p) := by
    rw [dkin, rb.kin_eq, hempty, List.nil_append]
    rfl
  have dproof : d.ram proofStore = [] := by rw [dram, rbrest.2.2.1, hproof]
  have dproofCursor : d.rc proofStore = 0 := by rw [dcother proofStore (by decide), rbrest.2.2.2.1, hproofCursor]
  obtain ⟨e, ne, ee, he, eproof, esize, ecproof, epos, ce, eip, eout, ekin, eoutword, eother, efr⟩ :=
    HonestLoading.call_load C proofStore TrimHonest.proofLength (by decide) (by decide)
      (request V p) d cd (List.ofFn (honest p)) drequest hbudget rfl dproof dproofCursor
      (by change (List.ofFn (honest p)).length < 2 ^ Wd; simpa only [List.length_ofFn] using hproofWidth)
  refine ⟨e, _, Ex.seq eb (Ex.seq ed ee), ?_, eproof, ?_, ?_, ?_, ?_, ?_, ekin, eoutword,
    epos, ce, ?_, ?_, ?_⟩
  · change nb ≤ 2 * tag.length + 15 * (sourceCircuitWord p.1).length + 13 at hb
    change nd ≤ b.rc inputStore + 8 * (List.ofFn p.2.val).length + 6 at hd
    change ne ≤ Lk + Bk + 9 * (List.ofFn (honest p)).length + 8 at he
    rw [rbrest.2.2.2.1] at hd
    simp only [tag, List.length_cons, List.length_nil, List.length_ofFn] at hb hd he
    omega
  · simpa only [List.length_ofFn] using esize
  · simpa only [List.length_ofFn] using ecproof
  · simpa only [List.length_ofFn] using (eother inputStore (by decide)).2.trans dcinput
  · exact eip.trans (dip.trans (rbrest.1.trans hip))
  · exact eout.trans (dout.trans rbrest.2.1)
  · intro m hm
    rw [(eother m hm).1, dram, rbrest.2.2.1]
  · intro m hm hi
    rw [(eother m hm).2, dcother m hi, rbrest.2.2.2.1]
  · apply (rb.vars.weaken ?_).trans ((dfr.weaken ?_).trans (efr.weaken ?_))
    all_goals intro i hi; simp only [SourceRequests.scratch, List.mem_cons, List.not_mem_nil, or_false] at hi
    all_goals rcases hi with rfl | rfl | rfl <;> simp [scratch]

end NearCubicGates.Adapters.Proximity.HonestSource
