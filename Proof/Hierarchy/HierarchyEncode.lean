import Proof.MachineModel.ClockPaddingReady
import Proof.MachineModel.UEmissionLanguageComplete
import Proof.PCP.VerifierDecodingRun

/-! The hierarchy encoding is the literal word produced by the paid
padding machine. Its independent allocation coefficient never changes the
hierarchy clock or the hierarchy's exact witness domain. -/
namespace NearCubicWires.RepairSource.HierarchyEncode
open LocalBitMultitape RepairOrdinary VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padded {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (x : List Bool) :=
  HierarchyPadding.rawInput k H.coefficient Cpad (code H.verifier) x
def length {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad n : ℕ) :=
  HierarchyBinary.inputLength k Cpad (code H.verifier).length H.coefficient n
def boundWord {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (x : List Bool) :=
  SignedSortKey.binary (HierarchyBinary.width H.coefficient (k+2) x.length) (H.time x.length)
def paddingWord {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (x : List Bool) :=
  List.replicate (length H Cpad x.length -
    (HierarchyPadding.headerBits H.coefficient (k+2) (code H.verifier) x).length) false

theorem padded_source {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (x : List Bool) :
    padded H Cpad x=VerifierInputFields.source (code H.verifier) x (boundWord H x) (paddingWord H Cpad x) := by
  simp only [padded,HierarchyPadding.rawInput,HierarchyPadding.headerBits,VerifierInputFields.source,
    boundWord,paddingWord,length,HierarchyBinary.bound,OrdinaryHierarchy.time,List.append_assoc]

theorem padded_length {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (x : List Bool) : (padded H Cpad x).length=length H Cpad x.length :=
  HierarchyPadding.raw_length k H.coefficient Cpad (code H.verifier) x hpad

theorem bound_value {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (x : List Bool) :
    RadixSemantics.value (boundWord H x)=H.time x.length :=
  HierarchyPadding.exact_bound H.coefficient (k+2) x

theorem padded_guards {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (x : List Bool) :
    (code H.verifier).length ≤ Nat.log 2 (padded H Cpad x).length ∧
    UInputScalars.Guards (padded H Cpad x) x (boundWord H x) := by
  obtain ⟨hc,hw,hn,hB,_⟩ := HierarchyPadding.entry_guards k H.coefficient Cpad
    (code H.verifier) x H.coefficientPositive hcoeff hpad
  refine ⟨hc,hw,?_,?_⟩ <;> rw [bound_value] <;> assumption

theorem padded_decoded {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (x : List Bool) :
    decode (padded H Cpad x).length (code H.verifier)=some (canonical H.verifier) :=
  decode_code H.verifier _ (padded_guards H Cpad hcoeff hpad x).1

theorem source_iff {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (x : List Bool) :
    UEmission.SourceAccepted (padded H Cpad x) ↔
      ∃ choices,choices.length=H.time x.length ∧ H.verifier.acceptsAt (H.time x.length) x choices := by
  have hg := padded_guards H Cpad hcoeff hpad x
  have hd := padded_decoded H Cpad hcoeff hpad x
  constructor
  · rintro ⟨v,word,input,bound,padding,choices,hs,_,hv,_,hchoices,ha⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ := UInputEntry.source_unique _ _ _ _ _ _ _ _
      ((padded_source H Cpad x).symm.trans hs)
    have he : v=canonical H.verifier := Option.some.inj (hv.symm.trans hd)
    rw [he] at ha
    have hB : choices.length=H.time x.length := hchoices.trans (bound_value H x)
    rw [hB] at ha
    exact ⟨choices,hB,(canonical_acceptsAt H.verifier _ _ _).1 ha⟩
  · rintro ⟨choices,hB,ha⟩
    refine ⟨canonical H.verifier,code H.verifier,x,boundWord H x,paddingWord H Cpad x,choices,
      padded_source H Cpad x,hg.2,hd,hg.1,hB.trans (bound_value H x).symm,?_⟩
    rw [hB]
    exact (canonical_acceptsAt H.verifier _ _ _).2 ha

theorem accepts_at_halting (v : OrdinaryVerifier) (fuel : ℕ) (input witness : List Bool)
    (htotal : ∃ r,run v.machine fuel (v.inputTapes input witness)=some r) :
    v.accepts input witness ↔ v.acceptsAt fuel input witness := by
  constructor
  · rintro ⟨other,r,hr,ha⟩
    obtain ⟨last,hlast⟩ := htotal
    have h1 := run_moreFuel v.machine other fuel _ r hr
    have h2 := run_moreFuel v.machine fuel other _ last hlast
    rw [Nat.add_comm fuel other] at h2
    have he : r=last := Option.some.inj (h1.symm.trans h2)
    exact ⟨last,hlast,he ▸ ha⟩
  · exact fun h => ⟨fuel,h⟩

theorem source_language {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (n : ℕ) (x : BitInput n) :
    H.verifier.language H.time n x ↔ UEmission.SourceAccepted (padded H Cpad (List.ofFn x)) := by
  rw [source_iff H Cpad hcoeff hpad]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨w,ha⟩
    exact ⟨List.ofFn w,List.length_ofFn,
      (accepts_at_halting H.verifier (H.time n) _ _ (H.halts n x w)).1 ha⟩
  · rintro ⟨choices,hlen,ha⟩
    have hw : ∃ w : BitInput choices.length,H.verifier.accepts (List.ofFn x) (List.ofFn w) :=
      ⟨choices.get,by simpa only [List.ofFn_get] using (show H.verifier.accepts (List.ofFn x) choices from ⟨H.time n,ha⟩)⟩
    rwa [hlen] at hw

def encode {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (r : InputRequest) : InputRequest :=
  ⟨length H Cpad r.1,fun i => (padded H Cpad (List.ofFn r.2)).getD i.val false⟩

theorem ofFn_getD (bits : List Bool) (N : ℕ) (hlen : bits.length=N) :
    List.ofFn (fun i : Fin N => bits.getD i.val false)=bits := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  · intro i hi hj
    simpa only [List.getElem_ofFn] using List.getD_eq_getElem bits false hj

theorem encode_word {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    List.ofFn (encode H Cpad r).2=padded H Cpad (List.ofFn r.2) := by
  apply ofFn_getD
  change (padded H Cpad (List.ofFn r.2)).length=length H Cpad r.1
  simpa only [List.length_ofFn] using padded_length H Cpad hpad (List.ofFn r.2)

theorem encode_length {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hpad : k+3 ≤ Cpad) (r : InputRequest) : r.1+1 ≤ (encode H Cpad r).1 := by
  have h := (HierarchyPadding.linear_length k H.coefficient Cpad (code H.verifier) (List.ofFn r.2) hpad).1
  change (List.ofFn r.2).length+1 ≤ (padded H Cpad (List.ofFn r.2)).length at h
  rw [padded_length H Cpad hpad,List.length_ofFn] at h
  exact h

theorem encoded_source_language {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    H.verifier.language H.time r.1 r.2 ↔ UEmission.SourceAccepted (List.ofFn (encode H Cpad r).2) := by
  rw [encode_word H Cpad hpad r]
  exact source_language H Cpad hcoeff hpad r.1 r.2

end NearCubicWires.RepairSource.HierarchyEncode
