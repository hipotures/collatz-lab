import CollatzLab.UnequalSparse
import CollatzLab.SparseFamily
import CollatzLab.UnequalControl

/-! Literal and actual-integer finite checks for the longer spectral examples. -/
namespace CollatzLab.SparseChecks
open Morphism

def literalStep (L : Nat) (xs : List Int) : List Int := xs.flatMap
  (fun b => if b = 1 then 1 :: List.replicate (L - 1) 0 else List.replicate (L - 1) 1 ++ [0])

def literalIter (L : Nat) : Nat → List Int
  | 0 => [1]
  | k + 1 => literalStep L (literalIter L k)

theorem longer_images :
    List.ofFn (unequalSparse 4).one = [true,false,false,false] ∧
    List.ofFn (unequalSparse 4).zero = [true,true,true,false] ∧
    List.ofFn (unequalSparse 5).one = [true,false,false,false,false] ∧
    List.ofFn (unequalSparse 5).zero = [true,true,true,true,false] := by decide

set_option maxRecDepth 100000 in
theorem longer_literal_prefixes :
    (List.range 81).map (parityWord (unequalSparse 4)) = (literalIter 4 4).take 81 ∧
    (List.range 81).map (parityWord (unequalSparse 5)) = (literalIter 5 3).take 81 := by decide

set_option maxRecDepth 100000 in
theorem longer_positive_prefixes :
    (List.range 81).map (seedParity 1 1068260854125908800748069) = (literalIter 4 4).take 81 ∧
    numIter 1 1068260854125908800748069 81 = 1790509375726802165 ∧
    (List.range 81).map (seedParity 1 1385232115788469867170293) = (literalIter 5 3).take 81 ∧
    numIter 1 1385232115788469867170293 81 = 28664001524819015 := by decide

theorem spectral_counts :
    weight (word (unequalSparse 4)) 16 = 10 ∧
    weight (word (unequalSparse 5)) 25 = 17 ∧
    weight (word (unequalSparse 5)) 125 = 49 := by decide

theorem sparse_length_two_control : RealizesWord 1 1 (parityWord (unequalSparse 2)) := by
  have he : parityWord (unequalSparse 2) = parityWord unequalAlternating := by
    funext n
    rw [unequalAlternating_word]
    have hh := word_rec (by decide) (unequalSparse 2) (by decide) n
    simp only [parityWord, hh]
    cases word (unequalSparse 2) (n / 2) <;>
      rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn <;>
        simp [image, unequalSparse, bit, hn]
  rw [he]
  exact unequalAlternating_realized

end CollatzLab.SparseChecks
