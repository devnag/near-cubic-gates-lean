import SourceAdapters.Routing.CoordinateMachineInput

/-!
# Header, raw coordinate array, and translation-bank parsing

The packed input contains two natural-number headers, exactly `m*m*f` raw
coordinate bits, and the self-delimiting bank. These routines preserve the
packed input and its physical length and retain the position of the first item.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires NearCubicWires.CanonicalBinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (listWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine (storeNat storeNat_spec)

/-- The input word up to an arbitrary item suffix. -/
def headerInput (f m : ℕ) (coeff : List Bool) (bank : List ℕ) (rest : List Bool) : List Bool :=
  natWord f ++ (natWord m ++ (coeff ++ (listWord natWord bank ++ rest)))

def parseHeader : S := .seq (storeNat 20) (storeNat 21)

theorem parseHeader_spec (G : Glob) (s : FS) (f m Bd : ℕ) (rest : List Bool)
    (hat : At (s.env 10) 0 (natWord f ++ (natWord m ++ rest)))
    (h14 : s.env 14 = 0) (hend : (natWord f).length + (natWord m).length ≤ Bd)
    (hB : BdOk G Bd) :
    let t := evalS G parseHeader s
    t.env 20 = f ∧ t.env 21 = m ∧
      t.env 14 = (natWord f).length + (natWord m).length ∧
      Wr [5, 6, 8, 9, 14, 20, 21] s t := by
  obtain ⟨ha, hb⟩ := At.append hat
  obtain ⟨a20, a14, aW⟩ := storeNat_spec G s 20 f 0 Bd ha h14 (by omega) hB (by decide)
  generalize ea : evalS G (storeNat 20) s = a at a20 a14 aW
  have a10 : a.env 10 = s.env 10 := aW.env 10 (by decide)
  obtain ⟨b21, b14, bW⟩ := storeNat_spec G a 21 m (natWord f).length Bd
    (by simpa only [a10, zero_add] using (At.append hb).1)
    (by simpa only [zero_add] using a14) hend hB (by decide)
  simp only [parseHeader, evalS_seq, ea]
  exact ⟨(bW.env 20 (by decide)).trans a20, b21, b14,
    (aW.mono (by decide)).trans (bW.mono (by decide))⟩

/-- Extract the raw coordinate block and move the packed-input cursor past it. -/
def parseCoordinates : S :=
  .seq (.set 29 (.mul (.mul (.v 21) (.v 21)) (.v 20)))
    (.seq (.set 22 (.md (.shr (.v 10) (.v 14)) (.shl (.k 1) (.v 29))))
      (.set 14 (.add (.v 14) (.v 29))))

theorem parseCoordinates_spec (G : Glob) (s : FS) (f m : ℕ) (pre coeff rest : List Bool)
    (h10 : s.env 10 = bitsValue (pre ++ coeff ++ rest)) (h14 : s.env 14 = pre.length)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (hlen : coeff.length = m * m * f)
    (hsquare : m * m ≤ G.cap) (hend : pre.length + coeff.length ≤ G.cap)
    (hpow : 2 ^ coeff.length ≤ G.cap) :
    let t := evalS G parseCoordinates s
    t.env 22 = bitsValue coeff ∧ t.env 14 = pre.length + coeff.length ∧
      Wr [14, 22, 29] s t := by
  have h1 : min 1 G.cap = 1 := by have := Nat.one_le_two_pow (n := coeff.length); omega
  have hcount : min (m * m * f) G.cap = coeff.length := by rw [← hlen]; omega
  have hwindow : bitsValue (pre ++ (coeff ++ rest)) / 2 ^ pre.length % 2 ^ coeff.length =
      bitsValue coeff := by
    rw [← bitsValue_window]
    simp
  have he : evalS G parseCoordinates s =
      ((s.setv 29 coeff.length).setv 22 (bitsValue coeff)).setv 14 (pre.length + coeff.length) := by
    simp [parseCoordinates, evalE, h20, h21, min_eq_left hsquare, hcount, h1,
      min_eq_left hpow, h10, h14, hwindow, min_eq_left hend]
  rw [he]
  exact ⟨by simp, by simp,
    ((Wr.setv s (by simp) _).trans (Wr.setv _ (by simp) _)).trans (Wr.setv _ (by simp) _)⟩

/-- Read the bank with the supplied entry width and store the next item position. -/
def parseBank : S :=
  .seq (.set 23 (.v 12)) (.seq pListW (.seq (.set 23 (.v 30))
    (.seq (.set 26 (.v 29)) (.seq (.set 27 (.v 14)) (.set 30 (.v 12))))))

def bankWrites : List Var := [5, 6, 8, 9, 14, 23, 26, 27, 29, 30, 31]

theorem parseBank_spec (G : Glob) (s : FS) (bank : List ℕ) (width pos Bd : ℕ)
    (hat : At (s.env 10) pos (listWord natWord bank))
    (h14 : s.env 14 = pos) (h12 : s.env 12 = width)
    (hwords : ∀ x ∈ bank, x < 2 ^ width) (hpack : width * bank.length ≤ G.K)
    (hend : pos + (listWord natWord bank).length ≤ Bd) (hB : BdOk G Bd) :
    let t := evalS G parseBank s
    t.env 23 = packW width bank ∧ t.env 26 = bank.length ∧
      t.env 27 = pos + (listWord natWord bank).length ∧
      t.env 14 = pos + (listWord natWord bank).length ∧ t.env 30 = width ∧
      Wr bankWrites s t := by
  let a := s.setv 23 width
  obtain ⟨b29, b30, b14, bW⟩ := pListW_spec G a bank width pos Bd
    (by simpa [a] using hat) (by simpa [a] using h14) (by simp [a]) hwords hpack hend hB
  generalize eb : evalS G pListW a = b at b29 b30 b14 bW
  have b12 : b.env 12 = width := (bW.env 12 (by decide)).trans (by simpa [a] using h12)
  have he : evalS G parseBank s =
      (((b.setv 23 (packW width bank)).setv 26 bank.length).setv 27
        (pos + (listWord natWord bank).length)).setv 30 width := by
    rw [parseBank, evalS_seq, evalS_set]
    change evalS G (.seq pListW _) (s.setv 23 (s.env 12)) = _
    rw [h12]
    change evalS G (.seq pListW _) a = _
    simp [eb, evalE, b29, b30, b14, b12]
  rw [he]
  refine ⟨by simp, by simp, by simp, by simp [b14], by simp, ?_⟩
  exact (((((Wr.setv s (by decide) width).trans (bW.mono (by decide))).trans
    (Wr.setv b (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
    (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)

def parseInput : S := .seq parseHeader (.seq parseCoordinates parseBank)

def inputWrites : List Var := [5, 6, 8, 9, 14, 20, 21, 22, 23, 26, 27, 29, 30, 31]

theorem parseInput_spec (G : Glob) (s : FS) (f m : ℕ) (coeff : List Bool) (bank : List ℕ)
    (rest : List Bool) (width : ℕ)
    (h10 : s.env 10 = bitsValue (headerInput f m coeff bank rest)) (h14 : s.env 14 = 0)
    (h12 : s.env 12 = width) (hlen : coeff.length = m * m * f)
    (hB : BdOk G (headerInput f m coeff bank rest).length)
    (hsquare : m * m ≤ G.cap) (hpow : 2 ^ coeff.length ≤ G.cap)
    (hwords : ∀ x ∈ bank, x < 2 ^ width) (hpack : width * bank.length ≤ G.K) :
    let t := evalS G parseInput s
    let pos := (natWord f).length + (natWord m).length + coeff.length +
      (listWord natWord bank).length
    t.env 20 = f ∧ t.env 21 = m ∧ t.env 22 = bitsValue coeff ∧
      t.env 23 = packW width bank ∧ t.env 26 = bank.length ∧ t.env 27 = pos ∧
      t.env 14 = pos ∧ t.env 30 = width ∧ Wr inputWrites s t ∧ t.ip = s.ip := by
  let word := headerInput f m coeff bank rest
  have hat : At (s.env 10) 0 word := by rw [h10]; exact At.self word
  have hlenWord : word.length = (natWord f).length + (natWord m).length + coeff.length +
      (listWord natWord bank).length + rest.length := by
    simp only [word, headerInput, List.length_append]; omega
  have hcap : word.length ≤ G.cap := by
    have hh := hB.1
    change word.length + 2 * 2 ^ word.length ≤ G.cap at hh
    omega
  obtain ⟨a20, a21, a14, aW⟩ := parseHeader_spec G s f m word.length
    (coeff ++ (listWord natWord bank ++ rest)) hat h14 (by omega) hB
  generalize ea : evalS G parseHeader s = a at a20 a21 a14 aW
  have a10 : a.env 10 = bitsValue word := (aW.env 10 (by decide)).trans h10
  obtain ⟨b22, b14, bW⟩ := parseCoordinates_spec G a f m (natWord f ++ natWord m) coeff
    (listWord natWord bank ++ rest)
    (by simpa only [word, headerInput, List.append_assoc] using a10)
    (by simpa only [List.length_append] using a14) a20 a21 hlen hsquare
    (by simp only [List.length_append]; omega) hpow
  generalize eb : evalS G parseCoordinates a = b at b22 b14 bW
  have b10 : b.env 10 = s.env 10 := (bW.env 10 (by decide)).trans (aW.env 10 (by decide))
  have b12 : b.env 12 = width := (bW.env 12 (by decide)).trans ((aW.env 12 (by decide)).trans h12)
  have bankAt : At (b.env 10) ((natWord f).length + (natWord m).length + coeff.length)
      (listWord natWord bank) := by
    rw [b10]
    have hc := (At.append (At.append (At.append (At.append hat).2).2).2).1
    simpa only [zero_add, Nat.add_assoc] using hc
  obtain ⟨c23, c26, c27, c14, c30, cW⟩ := parseBank_spec G b bank width
    ((natWord f).length + (natWord m).length + coeff.length) word.length bankAt
    (by simpa only [List.length_append] using b14) b12 hwords hpack (by omega) hB
  generalize ec : evalS G parseBank b = c at c23 c26 c27 c14 c30 cW
  have he : evalS G parseInput s = c := by simp only [parseInput, evalS_seq, ea, eb, ec]
  have hip : (evalS G parseInput s).ip = s.ip := ip_rdFree G parseInput s (by decide)
  dsimp only
  rw [he] at hip ⊢
  refine ⟨?_, ?_, ?_, c23, c26, c27, c14, c30, ?_, hip⟩
  · exact (cW.env 20 (by decide)).trans ((bW.env 20 (by decide)).trans a20)
  · exact (cW.env 21 (by decide)).trans ((bW.env 21 (by decide)).trans a21)
  · exact (cW.env 22 (by decide)).trans b22
  · exact ((aW.mono (by decide)).trans (bW.mono (by decide))).trans (cW.mono (by decide))

theorem parseInput_wf (d : ℕ) (hd : d ≤ 6) : wfS parseInput d = true := by
  simp [parseInput, parseHeader, storeNat, parseCoordinates, parseBank, pListW,
    pNat, pNatOnes, pNatBits, bitE, wfS, dE]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine
