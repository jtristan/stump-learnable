/-
Generalities about dvectors. 
This file is originally from https://github.com/formalabstracts/formalabstracts/blob/master/src/data/dvector.lean

and 

https://github.com/flypitch/flypitch/blob/4ac94138305ffa889f3ffea8d478f44ab610cee8/src/to_mathlib.lean

Authors: Jesse Han, Floris van Doorn 

-/


universes u v w

@[derive decidable_eq]inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

@[derive decidable_eq]inductive dfin : ℕ → Type
| fz {n} : dfin (n+1)
| fs {n} : dfin n → dfin (n+1)

namespace dfin

instance has_zero_dfin {n} : has_zero $ dfin (n+1) := ⟨fz⟩

instance has_one_dfin : ∀ {n}, has_one (dfin (nat.succ n))
| 0 := ⟨fz⟩
| (n+1) := ⟨fs fz⟩

end dfin