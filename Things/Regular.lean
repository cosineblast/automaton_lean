
import Mathlib.Data.Set.Defs

inductive RegularExpression (A : Type) where
  | null
  | eps
  | literal (x : A)
  | concat (left : RegularExpression A) (right : RegularExpression A)
  | union (left : RegularExpression A) (right : RegularExpression A)

namespace RegularExpression

def language (re : RegularExpression A) : Set (List A) := 
  match re with 
  | null => ∅
  | eps => Set.singleton []
  | literal t => Set.singleton [t]
  | concat l r => setOf (fun w => ∃ x y, x ∈ l.language ∧ y ∈ r.language ∧ w = x.append y)
  | union l r => l.language ∪ r.language

end RegularExpression

def regular (l : Set (List A)) : Prop := 
  ∃ re : RegularExpression A, l = re.language


