import CollatzLab.UnequalSparse

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

end CollatzLab.SparseChecks
