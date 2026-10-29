import SourceAdapters.Proximity.RawSplitting
import SourceAdapters.Proximity.LegacyHeader
import SourceAdapters.Proximity.NativePolynomial

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": an actual target accepted-input splitter. Its
boundary uses the physically measured total length and the parsed arity. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.AcceptedSplitting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Close.Cells NearCubicWires.ExecutableInterfaces
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)
open SourceRequests (lengthReg)
open SourceHeader (arityReg)
open RawFields (State Script)

def output (p : AcceptedCircuitInput) : List Bool := frame p.1.word ++ frame (List.ofFn p.2.val)

def program : Script := .seq initP (.seq (SourcePrinting.readInto lengthReg)
  (.seq LegacyHeader.readArity RawSplitting.split))

noncomputable def context (p : AcceptedCircuitInput) : Ctx :=
  ctxOf noCallee ⟨16, 1, 0, 0, 0, 0⟩ (LengthPrefix.wrapped (acceptedCircuitInputWord p))

theorem width (p : AcceptedCircuitInput) :
    16 * ((acceptedCircuitInputWord p).length + 1) ≤ (context p).Wd := by
  have h := LengthPrefix.allocation_covers_length (acceptedCircuitInputWord p)
  simp only [context, ctxOf, Sz.W, Nat.one_mul]
  omega

theorem run (p : AcceptedCircuitInput) :
    ∃ b cost, Ex (context p) program (a0 : State) b cost ∧ b.out = output p ∧
      cost ≤ 20000 * ((acceptedCircuitInputWord p).length + 1) ^ 2 := by
  let C := context p
  let w := acceptedCircuitInputWord p
  let L := w.length
  have hwidth := width p
  change 16 * (L + 1) ≤ C.Wd at hwidth
  have hn : p.1.n ≤ L := by simp [L, w, acceptedCircuitInputWord]
  have hLbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le L
  have hnbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le p.1.n
  have hexp := Nat.lt_two_pow_self (n := C.Wd)
  obtain ⟨b, nb, eb, hb, cb, _, _, bip, bout, _, _, _, _⟩ :=
    initP_spec (C := C) (a0 : State) rfl rfl rfl (by omega)
  have hin : C.inp.drop b.ip = natWord L ++ w := by rw [bip]; rfl
  obtain ⟨d, nd, ed, hd, rd⟩ := SourcePrinting.read_into (C := C) lengthReg (by decide)
    b cb L w hin (by omega)
  have cd := rd.constants cb (by decide)
  have hdip : d.ip = (natWord L).length := by rw [rd.cursor, bip]; simp [a0]
  have hshape : C.inp = natWord L ++ natWord p.1.n ++
      ((encodeBooleanCircuit p.1.D).bits ++ List.ofFn p.2.val) := by
    change natWord L ++ w = _
    simp only [w, acceptedCircuitInputWord, Circuit.word, List.append_assoc]
  obtain ⟨e, ne, ee, he, hen, hs, hf⟩ := LegacyHeader.read_arity C d cd p.1.n
    (natWord L) ((encodeBooleanCircuit p.1.D).bits ++ List.ofFn p.2.val)
    hshape hdip (by omega) (by omega)
  have ce := Cst.of_fr cd hf (by decide)
  have helen : e.env lengthReg = p.1.word.length + (List.ofFn p.2.val).length := by
    rw [hf lengthReg (by decide), rd.value]
    simp only [L, w, acceptedCircuitInputWord, List.length_append]
  obtain ⟨f, nf, ef, hfr, hout⟩ := RawSplitting.split_run C e ce p.1.word (List.ofFn p.2.val)
    (natWord L) [] (by change natWord L ++ w = _; simp only [w, acceptedCircuitInputWord, List.append_nil])
    (hs.ip.trans hdip) helen (by simpa using hen)
  refine ⟨f, _, Ex.seq eb (Ex.seq ed (Ex.seq ee ef)), ?_, ?_⟩
  · have ho := rd.other
    simp only [Prod.mk.injEq] at ho
    rw [hout, hs.out, ho.1, bout]
    rfl
  · have hsum : p.1.word.length + (List.ofFn p.2.val).length = L := by simp only [L, w, acceptedCircuitInputWord, List.length_append]
    rw [hsum] at hfr
    nlinarith

noncomputable def wrappedWordFunction : WordFunction AcceptedCircuitInput
    (fun p => LengthPrefix.wrapped (acceptedCircuitInputWord p)) output
    (fun p => langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (acceptedCircuitInputWord p))
      (20000 * ((acceptedCircuitInputWord p).length + 1) ^ 2)) :=
  wordFunction_of_lang _ output noCallee ⟨16, 1, 0, 0, 0, 0⟩ program _ run
    (fun p => by have h := width p; change 1 ≤ (context p).Wd; omega)

end NearCubicGates.Adapters.Proximity.AcceptedSplitting
